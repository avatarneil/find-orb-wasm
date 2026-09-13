// GPL-2.0-or-later. Links source-extracted upstream functions without rewrites.
#include <algorithm>
#include <cassert>
#include <cfloat>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <limits>
#include <vector>

extern void *bsearch_ext_r(const void *, const void *, size_t, size_t,
    int (*)(const void *, const void *, void *), void *, bool *);
extern void *bsearch_ext(const void *, const void *, size_t, size_t,
    int (*)(const void *, const void *), bool *);
extern double dot_product(const double *, const double *);
extern void vector_cross_product(double *, const double *, const double *);
static_assert(sizeof(double) == 8 && DBL_MANT_DIG == 53 && FLT_RADIX == 2,
              "The engine requires binary64 double");
#ifdef __FAST_MATH__
#error Fast math violates the verification contract
#endif
#ifdef __EMSCRIPTEN__
static_assert(sizeof(void *) == 4 && sizeof(size_t) == 4, "Expected wasm32 ABI");
static_assert(sizeof(long double) == 16 && LDBL_MANT_DIG == 113,
              "Pinned Emscripten long double ABI changed");
#endif

static uint64_t state = 0x43d1f1198ee275a1ULL;
static uint64_t random_word()
{
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    return state;
}
static uint64_t hash = 14695981039346656037ULL;
static void record(double value)
{
    uint64_t bits;
    memcpy(&bits, &value, sizeof bits);
    // NaN payload/sign propagation is intentionally unspecified by this test.
    if (std::isnan(value)) bits = 0x7ff8000000000000ULL;
    for (unsigned i = 0; i < 8; ++i) {
        hash ^= (bits >> (8 * i)) & 255;
        hash *= 1099511628211ULL;
    }
}
static int compare(const void *a, const void *b)
{
    const int x = *static_cast<const int *>(a), y = *static_cast<const int *>(b);
    return (x > y) - (x < y);
}
static int contextual_compare(const void *a, const void *b, void *context)
{
    ++*static_cast<size_t *>(context);
    return compare(a, b);
}
static size_t searches = 0;
static void check_search(const std::vector<int>& values, int key)
{
    // Keep a valid pointer even for zero-length arrays, avoiding null arithmetic.
    const int empty = 0;
    const int *base = values.empty() ? &empty : values.data();
    size_t expected = 0, calls = 0;
    while (expected < values.size() && values[expected] < key) ++expected;
    const bool expected_found = expected < values.size() && values[expected] == key;
    bool found = !expected_found;
    const int *result = static_cast<const int *>(bsearch_ext_r(
        &key, base, values.size(), sizeof(int), contextual_compare, &calls, &found));
    assert(result == base + expected && found == expected_found && calls <= 32);
    result = static_cast<const int *>(bsearch_ext(
        &key, base, values.size(), sizeof(int), compare, &found));
    assert(result == base + expected && found == expected_found);
    result = static_cast<const int *>(bsearch_ext(
        &key, base, values.size(), sizeof(int), compare, nullptr));
    assert(result == (expected_found ? base + expected : nullptr));
    ++searches;
}
static bool nested = false;
static int nested_compare(const void *a, const void *b)
{
    if (!nested) {
        nested = true;
        const int data[] = {1, 1, 2, 4}, key = 1;
        bool found = false;
        assert(bsearch_ext(&key, data, 4, sizeof(int), compare, &found) == data && found);
        nested = false;
    }
    return compare(a, b);
}
static void check_kernels(const double a[3], const double b[3])
{
    double cross[3];
    record(dot_product(a, b));
    vector_cross_product(cross, a, b);
    for (double value : cross) record(value);
}
int main()
{
    // Every sorted ternary array up to length 16, including all duplicate runs.
    for (int n = 0; n <= 16; ++n)
        for (int left = 0; left <= n; ++left)
            for (int equal = 0; equal <= n - left; ++equal) {
                std::vector<int> data(left, -1);
                data.insert(data.end(), equal, 0);
                data.insert(data.end(), n - left - equal, 1);
                for (int key = -2; key <= 2; ++key) check_search(data, key);
            }
    for (int trial = 0; trial < 256; ++trial) {
        const size_t count = random_word() % 1025;
        std::vector<int> data;
        int value = -500;
        for (size_t i = 0; i < count; ++i) {
            value += random_word() % 3;
            data.push_back(value);
        }
        for (int i = 0; i < 64; ++i) check_search(data, int(random_word() % 2049) - 750);
    }
    const int data[] = {1, 2, 2, 3}, key = 2;
    bool found = false;
    assert(bsearch_ext(&key, data, 4, sizeof(int), nested_compare, &found) == data + 1 && found);

    for (int i = 0; i < 50000; ++i) {
        double a[3], b[3];
        for (int j = 0; j < 3; ++j) {
            // Exact power-of-two scaling, finite products without overflow.
            a[j] = std::ldexp(double(int64_t(random_word() % 2097153) - 1048576),
                              int(random_word() % 801) - 420);
            b[j] = std::ldexp(double(int64_t(random_word() % 2097153) - 1048576),
                              int(random_word() % 801) - 420);
        }
        check_kernels(a, b);
    }
    const double special[] = {0., -0., DBL_MIN, -DBL_MIN, DBL_MAX, -DBL_MAX,
        std::numeric_limits<double>::denorm_min(), 1., -1.,
        std::numeric_limits<double>::infinity(), std::numeric_limits<double>::quiet_NaN()};
    for (double x : special)
        for (double y : special) {
            const double a[] = {x, y, 1.}, b[] = {y, -x, -1.};
            check_kernels(a, b);
        }
    volatile double x = 1. + std::ldexp(1., -27), y = 1. - std::ldexp(1., -27), z = -1.;
    const double split = x * y + z;
    assert(split == 0.);  // Would fail if contracted to FMA on ARM.
    const double fused = std::fma(x, y, z);
    assert(fused == -std::ldexp(1., -54));
    volatile double denormal = std::numeric_limits<double>::denorm_min();
    assert(denormal * 1. == denormal && denormal + denormal > denormal);
    printf("{\"pointerBytes\":%zu,\"doubleBytes\":%zu,\"doubleMantissaBits\":%d,"
           "\"longDoubleBytes\":%zu,\"longDoubleMantissaBits\":%d,\"searchCases\":%zu,"
           "\"kernelCases\":50121,\"kernelHash\":\"%016llx\",\"splitWitness\":%.17g,\"fmaWitness\":%.17g}\n",
           sizeof(void *), sizeof(double), DBL_MANT_DIG, sizeof(long double), LDBL_MANT_DIG,
           searches, (unsigned long long)hash, split, fused);
}
