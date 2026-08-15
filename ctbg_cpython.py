_EMPTY = object()          # unique sentinel: cheaper to test with `is` than tuple unpacking
_M = (1 << 64) - 1
_A = 0x9E3779B97F4A7C15
_B = 0xBF58476D1CE4E5B9
_C = 0x94D049BB133111EB
_RI = 0xC2B2AE3D27D4EB4F
_RT = 0x165667B19E3779F9


class OptCTBGHashTable:
    __slots__ = ("n", "L", "keys", "vals", "count", "stats", "_mask",
                 "_ins_steps", "_qry_steps", "_starts", "_sizes")

    def __init__(self, capacity, L=16, c=1, s_max=6, stats=None):
        self.n = capacity
        self.L = L
        self.keys = [_EMPTY] * capacity          # parallel flat arrays instead of
        self.vals = [None] * capacity            # a list of (key, value) tuples
        self.count = 0
        self._mask = capacity - 1 if capacity & (capacity - 1) == 0 else 0
        self.stats = stats if stats is not None else ProbeStatistics()
        k = max(2, capacity.bit_length() - 4)
        part = RegionPartition(capacity, k)
        self._starts = [s for s, _ in part.bounds]
        self._sizes = [z for _, z in part.bounds]
        # Pre-expand both schedules into flat (region_index_0based, t) step lists,
        # removing all generator and counter overhead from the hot path.
        self._ins_steps = self._expand(InsertionSchedule(c, s_max).steps(k))
        self._qry_steps = self._expand(QuerySchedule(c, s_max).steps(k))

    @staticmethod
    def _expand(sched):
        steps, counters = [], {}
        for i, budget in sched:
            t = counters.get(i, 0)
            for _ in range(budget):
                steps.append((i - 1, t))
                t += 1
            counters[i] = t
        return steps

    def insert(self, key, value):
        keys = self.keys                          # hoist attribute lookups to locals
        vals = self.vals
        n = self.n
        record = self.stats.record                # hoist the bound method too
        hk = hash(key) & _M
        x = (hk + _A) & _M                        # inlined splitmix64 (no call per probe)
        x = ((x ^ (x >> 30)) * _B) & _M
        x = ((x ^ (x >> 27)) * _C) & _M
        x = (x ^ (x >> 31)) & _M
        m = self._mask
        home = (x & m) if m else (x % n)          
        probes = 0
        for j in range(self.L):                   # Phase 1: bounded local window
            pos = home + j
            if pos >= n:
                pos -= n
            probes += 1
            s = keys[pos]
            if s is _EMPTY:
                keys[pos] = key
                vals[pos] = value
                self.count += 1
                record("insert_local", probes)
                return Outcome.OK
            if s == key:
                record("insert_dup", probes)
                return Outcome.DUPLICATE
        self.stats.triggers += 1                  # Trigger
        starts, sizes = self._starts, self._sizes
        for ri, t in self._ins_steps:             # Phase 2: pre-expanded staged walk
            x = (hk ^ ((ri + 1) * _RI) ^ (t * _RT)) & _M
            x = (x + _A) & _M
            x = ((x ^ (x >> 30)) * _B) & _M
            x = ((x ^ (x >> 27)) * _C) & _M
            pos = starts[ri] + ((x ^ (x >> 31)) & _M) % sizes[ri]
            probes += 1
            s = keys[pos]
            if s is _EMPTY:
                keys[pos] = key
                vals[pos] = value
                self.count += 1
                record("insert_fallback", probes)
                return Outcome.OK
            if s == key:
                record("insert_dup", probes)
                return Outcome.DUPLICATE
        for pos in range(n - 1, -1, -1):          # terminal stage
            probes += 1
            s = keys[pos]
            if s is _EMPTY:
                keys[pos] = key
                vals[pos] = value
                self.count += 1
                record("insert_fallback", probes)
                return Outcome.OK
            if s == key:
                record("insert_dup", probes)
                return Outcome.DUPLICATE
        record("insert_full", probes)
        return Outcome.FULL

    def lookup(self, key):
        keys = self.keys
        n = self.n
        record = self.stats.record
        hk = hash(key) & _M
        x = (hk + _A) & _M
        x = ((x ^ (x >> 30)) * _B) & _M
        x = ((x ^ (x >> 27)) * _C) & _M
        x = (x ^ (x >> 31)) & _M
        m = self._mask
        home = (x & m) if m else (x % n)
        probes = 0
        for j in range(self.L):                   # Phase 1
            pos = home + j
            if pos >= n:
                pos -= n
            probes += 1
            s = keys[pos]
            if s is _EMPTY:
                record("lookup_miss_local", probes)
                return Outcome.ABSENT
            if s == key:
                record("lookup_hit_local", probes)
                return Outcome.FOUND
        self.stats.triggers += 1                  # Trigger
        starts, sizes = self._starts, self._sizes
        ins_steps, qry_steps = self._ins_steps, self._qry_steps
        li, lq = len(ins_steps), len(qry_steps)
        a = b = 0
        while a < li or b < lq:                   # interleaved staged walk
            if a < li:
                ri, t = ins_steps[a]; a += 1
                x = (hk ^ ((ri + 1) * _RI) ^ (t * _RT)) & _M
                x = (x + _A) & _M
                x = ((x ^ (x >> 30)) * _B) & _M
                x = ((x ^ (x >> 27)) * _C) & _M
                pos = starts[ri] + ((x ^ (x >> 31)) & _M) % sizes[ri]
                probes += 1
                s = keys[pos]
                if s is _EMPTY:                   # empty on the insertion path
                    record("lookup_miss_fb", probes)
                    return Outcome.ABSENT
                if s == key:
                    record("lookup_hit_fb", probes)
                    return Outcome.FOUND
            if b < lq:
                ri, t = qry_steps[b]; b += 1
                x = (hk ^ ((ri + 1) * _RI) ^ (t * _RT)) & _M
                x = (x + _A) & _M
                x = ((x ^ (x >> 30)) * _B) & _M
                x = ((x ^ (x >> 27)) * _C) & _M
                pos = starts[ri] + ((x ^ (x >> 31)) & _M) % sizes[ri]
                probes += 1
                s = keys[pos]
                if s == key:
                    record("lookup_hit_fb", probes)
                    return Outcome.FOUND
        for pos in range(n - 1, -1, -1):          # terminal stage (insertion path)
            probes += 1
            s = keys[pos]
            if s is _EMPTY:
                record("lookup_miss_fb", probes)
                return Outcome.ABSENT
            if s == key:
                record("lookup_hit_fb", probes)
                return Outcome.FOUND
        record("lookup_miss_fb", probes)
        return Outcome.ABSENT

    @property
    def load(self):
        return self.count / self.n
