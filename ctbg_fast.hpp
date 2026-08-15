// ctbg_fast.hpp : optimised implementation (C++20)
#include <cstdint>
#include <cstddef>
#include <vector>

enum class Outcome : std::uint8_t { Found, Absent, Ok, Duplicate, Full };

// 16-byte slot, two per cache line pair; key 0 is reserved as the empty sentinel.
struct alignas(16) FastSlot { std::uint64_t key = 0, value = 0; };

struct NullStats {                       // zero-cost instrumentation policy
    static void record(int, std::size_t) {}
    static void trigger() {}
};

inline std::uint64_t mix64(std::uint64_t x) noexcept {
    x += 0x9E3779B97F4A7C15ULL;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    return x ^ (x >> 31);
}

/**
 * L is a template parameter: the window scan unrolls, and the trigger threshold
 * is a compile-time constant. Stats is a policy class (static dispatch, no vtable).
**/
template <std::size_t L = 16, class Stats = NullStats>
class FastCTBG {
    static_assert((L & (L - 1)) == 0, "L should be a power of two");
public:
    explicit FastCTBG(std::size_t capacityPow2)
        : n_(capacityPow2), mask_(capacityPow2 - 1), slots_(capacityPow2) {
        // capacity must be a power of two: home = hash & mask_ (no division)
        buildRegions();
        expandSchedules();
    }

    Outcome insert(std::uint64_t key, std::uint64_t value) noexcept {
        const std::size_t home = mix64(key) & mask_;
        __builtin_prefetch(&slots_[home]);               // pull the window's line early
        // Phase 1 : bounded local window (contiguous, branch-predictable)
        for (std::size_t j = 0; j < L; ++j) {
            FastSlot& s = slots_[(home + j) & mask_];
            if (s.key == 0) [[likely]] { s.key = key; s.value = value; ++count_;
                return Outcome::Ok; }
            if (s.key == key) [[unlikely]] return Outcome::Duplicate;
        }
        Stats::trigger();
        // Phase 2 : staged walk over pre-expanded steps (plain array iteration)
        for (const Step st : insSteps_) {
            FastSlot& s = slots_[pos(key, st)];
            if (s.key == 0) { s.key = key; s.value = value; ++count_;
                return Outcome::Ok; }
            if (s.key == key) return Outcome::Duplicate;
        }
        for (std::size_t p = n_; p-- > 0; ) {            // terminal stage
            FastSlot& s = slots_[p];
            if (s.key == 0) { s.key = key; s.value = value; ++count_;
                return Outcome::Ok; }
            if (s.key == key) return Outcome::Duplicate;
        }
        return Outcome::Full;
    }

    Outcome lookup(std::uint64_t key) const noexcept {
        const std::size_t home = mix64(key) & mask_;
        __builtin_prefetch(&slots_[home]);
        for (std::size_t j = 0; j < L; ++j) {            // Phase 1
            const FastSlot& s = slots_[(home + j) & mask_];
            if (s.key == key) [[likely]] return Outcome::Found;
            if (s.key == 0) return Outcome::Absent;      // free absence certificate
        }
        Stats::trigger();
        std::size_t a = 0, b = 0;                        // interleaved staged walk
        const std::size_t na = insSteps_.size(), nb = qrySteps_.size();
        while (a < na || b < nb) {
            if (a < na) {
                const FastSlot& s = slots_[pos(key, insSteps_[a++])];
                if (s.key == key) return Outcome::Found;
                if (s.key == 0) return Outcome::Absent;  // empty on the insertion path
            }
            if (b < nb) {
                const FastSlot& s = slots_[pos(key, qrySteps_[b++])];
                if (s.key == key) return Outcome::Found;
            }
        }
        for (std::size_t p = n_; p-- > 0; ) {            // terminal stage
            const FastSlot& s = slots_[p];
            if (s.key == key) return Outcome::Found;
            if (s.key == 0) return Outcome::Absent;
        }
        return Outcome::Absent;
    }

private:
    struct Step { std::uint32_t region; std::uint32_t t; };

    std::size_t pos(std::uint64_t key, Step st) const noexcept {
        const std::uint64_t h = mix64(key ^ ((st.region + 1ULL) * 0xC2B2AE3D27D4EB4FULL)
                                          ^ (std::uint64_t(st.t) * 0x165667B19E3779F9ULL));
        return regionStart_[st.region] + h % regionSize_[st.region];
    }

    void buildRegions() {
        std::size_t bits = 0;
        for (std::size_t v = n_; v > 1; v >>= 1) ++bits;
        const std::size_t k = bits > 6 ? bits - 4 : 2;
        std::size_t start = 0;
        for (std::size_t i = 1; i < k; ++i) {
            std::size_t size = n_ >> i;
            if (size == 0) size = 1;
            if (size > n_ - start - (k - i)) size = n_ - start - (k - i);
            regionStart_.push_back(start); regionSize_.push_back(size);
            start += size;
        }
        regionStart_.push_back(start); regionSize_.push_back(n_ - start);
    }

    void expandSchedules(std::size_t c = 1, std::size_t sMax = 6) {
        const std::size_t k = regionStart_.size();
        std::vector<std::uint32_t> ci(k, 0), cq(k, 0);
        for (std::size_t s = 1; s <= sMax; ++s)                       // balanced
            for (std::size_t i = 1; i <= (s < k ? s : k); ++i)
                for (std::size_t b = 0; b < (c << (s - i)); ++b)
                    insSteps_.push_back({std::uint32_t(i - 1), ci[i - 1]++});
        for (std::size_t s = 1; s <= sMax; ++s)                       // imbalanced
            for (std::size_t j = 1; j <= s; ++j) {
                std::size_t reach = 1;
                for (std::size_t x = 1; x < j && reach < k; ++x) reach *= 4;
                if (reach > k) reach = k;
                for (std::size_t i = 1; i <= reach; ++i)
                    for (std::size_t b = 0; b < (c << (s - j)); ++b)
                        qrySteps_.push_back({std::uint32_t(i - 1), cq[i - 1]++});
            }
    }

    std::size_t n_, mask_, count_ = 0;
    std::vector<FastSlot> slots_;                 // flat, contiguous, 16-byte slots
    std::vector<std::size_t> regionStart_, regionSize_;
    std::vector<Step> insSteps_, qrySteps_;
};
