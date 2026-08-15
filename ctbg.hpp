// ctbg.hpp : object-oriented implementation of the proposed algorithm (C++17)
#include <cstdint>
#include <cstddef>
#include <map>
#include <memory>
#include <string>
#include <vector>

enum class Outcome { Found, Absent, Ok, Duplicate, Full };

inline std::uint64_t mix64(std::uint64_t x) {          // splitmix64 finaliser
    x += 0x9E3779B97F4A7C15ULL;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    return x ^ (x >> 31);
}

struct Slot {
    std::uint64_t key   = 0;
    std::uint64_t value = 0;
    bool occupied       = false;
};

class ProbeStatistics {
public:
    void record(const std::string& kind, std::size_t probes) {
        auto& e = data_[kind];
        e.first  += 1;
        e.second += probes;
    }
    double avg(const std::string& kind) const {
        auto it = data_.find(kind);
        return it == data_.end() || it->second.first == 0
             ? 0.0 : double(it->second.second) / double(it->second.first);
    }
    std::size_t triggers = 0;
private:
    std::map<std::string, std::pair<std::uint64_t, std::uint64_t>> data_;
};

struct Region { std::size_t start, size; };

// Strategy interface: a schedule is fully described by its (region, budget) steps.
class ProbeSchedule {
public:
    virtual ~ProbeSchedule() = default;
    // Expand the staged walk into a flat (region_index, t) sequence.
    virtual std::vector<std::pair<std::size_t, std::size_t>>
    expand(std::size_t k) const = 0;
protected:
    static void emit(std::vector<std::pair<std::size_t, std::size_t>>& out,
                     std::vector<std::size_t>& counters,
                     std::size_t region, std::size_t budget) {
        for (std::size_t b = 0; b < budget; ++b)
            out.emplace_back(region, counters[region]++);
    }
};

// Balanced: stage s spends c*2^(s-i) probes in region i (large regions favoured early).
class InsertionSchedule final : public ProbeSchedule {
public:
    InsertionSchedule(std::size_t c, std::size_t sMax) : c_(c), sMax_(sMax) {}
    std::vector<std::pair<std::size_t, std::size_t>>
    expand(std::size_t k) const override {
        std::vector<std::pair<std::size_t, std::size_t>> out;
        std::vector<std::size_t> counters(k, 0);
        for (std::size_t s = 1; s <= sMax_; ++s)
            for (std::size_t i = 1; i <= std::min(s, k); ++i)
                emit(out, counters, i - 1, c_ << (s - i));
        return out;
    }
private:
    std::size_t c_, sMax_;
};

// Imbalanced: stage s spends c*2^(s-j) probes in each of R1..R_{4^(j-1)}.
class QuerySchedule final : public ProbeSchedule {
public:
    QuerySchedule(std::size_t c, std::size_t sMax) : c_(c), sMax_(sMax) {}
    std::vector<std::pair<std::size_t, std::size_t>>
    expand(std::size_t k) const override {
        std::vector<std::pair<std::size_t, std::size_t>> out;
        std::vector<std::size_t> counters(k, 0);
        for (std::size_t s = 1; s <= sMax_; ++s)
            for (std::size_t j = 1; j <= s; ++j) {
                std::size_t reach = 1;
                for (std::size_t x = 1; x < j && reach < k; ++x) reach *= 4;
                for (std::size_t i = 1; i <= std::min(reach, k); ++i)
                    emit(out, counters, i - 1, c_ << (s - j));
            }
        return out;
    }
private:
    std::size_t c_, sMax_;
};

class CTBGHashTable {
public:
    CTBGHashTable(std::size_t capacity, std::size_t L,
                  std::unique_ptr<ProbeSchedule> ins,
                  std::unique_ptr<ProbeSchedule> qry)
        : n_(capacity), L_(L), slots_(capacity) {
        buildRegions();
        insSteps_ = ins->expand(regions_.size());
        qrySteps_ = qry->expand(regions_.size());
    }

    Outcome insert(std::uint64_t key, std::uint64_t value) {
        std::size_t probes = 0;
        // Phase 1: bounded local window
        std::size_t home = mix64(key) % n_;
        for (std::size_t j = 0; j < L_; ++j) {
            Slot& s = slots_[(home + j) % n_];
            ++probes;
            if (!s.occupied) { place(s, key, value);
                stats_.record("insert_local", probes); return Outcome::Ok; }
            if (s.key == key) { stats_.record("insert_dup", probes);
                return Outcome::Duplicate; }
        }
        ++stats_.triggers;                                  // Trigger
        for (auto [ri, t] : insSteps_) {                    // Phase 2: staged walk
            Slot& s = slots_[probePos(key, ri, t)];
            ++probes;
            if (!s.occupied) { place(s, key, value);
                stats_.record("insert_fallback", probes); return Outcome::Ok; }
            if (s.key == key) { stats_.record("insert_dup", probes);
                return Outcome::Duplicate; }
        }
        for (std::size_t p = n_; p-- > 0; ) {               // terminal stage
            Slot& s = slots_[p];
            ++probes;
            if (!s.occupied) { place(s, key, value);
                stats_.record("insert_fallback", probes); return Outcome::Ok; }
            if (s.key == key) { stats_.record("insert_dup", probes);
                return Outcome::Duplicate; }
        }
        return Outcome::Full;
    }

    Outcome lookup(std::uint64_t key) {
        std::size_t probes = 0;
        std::size_t home = mix64(key) % n_;
        for (std::size_t j = 0; j < L_; ++j) {              // Phase 1
            const Slot& s = slots_[(home + j) % n_];
            ++probes;
            if (!s.occupied) { stats_.record("lookup_miss_local", probes);
                return Outcome::Absent; }                    // free absence certificate
            if (s.key == key) { stats_.record("lookup_hit_local", probes);
                return Outcome::Found; }
        }
        ++stats_.triggers;                                  // Trigger
        std::size_t a = 0, b = 0;                           // interleaved staged walk
        while (a < insSteps_.size() || b < qrySteps_.size()) {
            if (a < insSteps_.size()) {
                auto [ri, t] = insSteps_[a++];
                const Slot& s = slots_[probePos(key, ri, t)];
                ++probes;
                if (!s.occupied) { stats_.record("lookup_miss_fb", probes);
                    return Outcome::Absent; }                // empty on the insertion path
                if (s.key == key) { stats_.record("lookup_hit_fb", probes);
                    return Outcome::Found; }
            }
            if (b < qrySteps_.size()) {
                auto [ri, t] = qrySteps_[b++];
                const Slot& s = slots_[probePos(key, ri, t)];
                ++probes;
                if (s.occupied && s.key == key) {
                    stats_.record("lookup_hit_fb", probes); return Outcome::Found; }
                // empty on a query-only probe certifies nothing
            }
        }
        for (std::size_t p = n_; p-- > 0; ) {               // terminal stage
            const Slot& s = slots_[p];
            ++probes;
            if (!s.occupied) { stats_.record("lookup_miss_fb", probes);
                return Outcome::Absent; }
            if (s.key == key) { stats_.record("lookup_hit_fb", probes);
                return Outcome::Found; }
        }
        stats_.record("lookup_miss_fb", probes);
        return Outcome::Absent;
    }

    const ProbeStatistics& stats() const { return stats_; }

private:
    void buildRegions() {
        std::size_t k = 2, bits = 0;
        for (std::size_t v = n_; v > 1; v >>= 1) ++bits;
        if (bits > 6) k = bits - 4;
        std::size_t start = 0;
        for (std::size_t i = 1; i < k; ++i) {
            std::size_t size = std::max<std::size_t>(1, n_ >> i);
            size = std::min(size, n_ - start - (k - i));
            regions_.push_back({start, size});
            start += size;
        }
        regions_.push_back({start, n_ - start});            // remainder region
    }
    std::size_t probePos(std::uint64_t key, std::size_t ri, std::size_t t) const {
        std::uint64_t h = mix64(key ^ ((ri + 1) * 0xC2B2AE3D27D4EB4FULL)
                                    ^ (t * 0x165667B19E3779F9ULL));
        return regions_[ri].start + h % regions_[ri].size;
    }
    void place(Slot& s, std::uint64_t key, std::uint64_t value) {
        s.key = key; s.value = value; s.occupied = true; ++count_;
    }

    std::size_t n_, L_, count_ = 0;
    std::vector<Slot> slots_;
    std::vector<Region> regions_;
    std::vector<std::pair<std::size_t, std::size_t>> insSteps_, qrySteps_;
    ProbeStatistics stats_;
};

/**
 *
 * Usage:
 *  CTBGHashTable t ( 1 << 16, 16,
 *                 std::make_unique<InsertionSchedule>(1, 6),
 *                 std::make_unique<QuerySchedule>(1, 6));
 *  t.insert(42, 420);
 *  t.lookup(42);
 *
**/
