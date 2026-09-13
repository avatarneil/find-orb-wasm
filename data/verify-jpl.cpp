// SPDX-License-Identifier: GPL-2.0-or-later
// Differential test against the pinned, unmodified native jpl_eph reader.
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include "jpleph.h"

int main(int argc, char **argv) {
  if (argc != 3) {std::fprintf(stderr, "Usage: verify-jpl FULL.440 COMPACT.440\n"); return 2;}
  void *full = jpl_init_ephemeris(argv[1], nullptr, nullptr);
  void *compact = jpl_init_ephemeris(argv[2], nullptr, nullptr);
  if (!full || !compact) {std::fprintf(stderr, "Cannot initialize JPL files.\n"); return 2;}
  const double start = jpl_get_double(compact, JPL_EPHEM_START_JD);
  const double end = jpl_get_double(compact, JPL_EPHEM_END_JD);
  const double step = jpl_get_double(compact, JPL_EPHEM_STEP);
  std::vector<double> times{std::nextafter(start, end), end};
  for (double jd = start; jd < end; jd += step) {
    times.push_back(jd + step / 2.);
    if (jd > start) {
      times.push_back(std::nextafter(jd, start));
      times.push_back(jd);
      times.push_back(std::nextafter(jd, end));
    }
  }
  uint64_t random = 0x53f2da1101ULL;
  for (int i = 0; i < 1024; ++i) {
    random = random * 6364136223846793005ULL + 1442695040888963407ULL;
    const double fraction = static_cast<double>(random >> 11) / 9007199254740992.;
    times.push_back(start + (end - start) * fraction);
  }
  uint64_t calls = 0, values = 0, missing = 0;
  for (double jd : times) {
    for (int target = 1; target <= 17; ++target) {
      for (int center = target <= 13 ? 1 : 0; center <= (target <= 13 ? 13 : 0); ++center) {
        for (int velocity = 0; velocity <= 1; ++velocity) {
          double expected[6] = {}, actual[6] = {};
          const int a = jpl_pleph(full, jd, target, center, expected, velocity);
          const int b = jpl_pleph(compact, jd, target, center, actual, velocity);
          ++calls;
          if (a != b || (a != 0 && a != JPL_EPH_QUANTITY_NOT_IN_EPHEMERIS)) {
            std::fprintf(stderr, "Return mismatch at %.17g target %d center %d: %d vs %d\n", jd, target, center, a, b); return 1;
          }
          if (a == JPL_EPH_QUANTITY_NOT_IN_EPHEMERIS) {++missing; continue;}
          for (int component = 0; component < 6; ++component) {
            ++values;
            if (!std::isfinite(expected[component]) || std::memcmp(expected + component, actual + component, sizeof(double))) {
              std::fprintf(stderr, "Bit mismatch at %.17g target %d center %d velocity %d component %d: %.17g vs %.17g\n", jd, target, center, velocity, component, expected[component], actual[component]); return 1;
            }
          }
        }
      }
    }
  }
  double state[6] = {};
  if (jpl_pleph(compact, std::nextafter(start, -INFINITY), 3, 11, state, 1) != JPL_EPH_OUTSIDE_RANGE ||
      jpl_pleph(compact, std::nextafter(end, INFINITY), 3, 11, state, 1) != JPL_EPH_OUTSIDE_RANGE) {
    std::fprintf(stderr, "JPL reader did not reject out-of-range epochs.\n"); return 1;
  }
  std::printf("{\"epochs\":%zu,\"readerCallsPerFile\":%llu,\"bitwiseEqualComponents\":%llu,\"absentQuantityPairs\":%llu,\"supportedStartExclusiveJD\":%.17g,\"supportedEndInclusiveJD\":%.17g,\"outOfRangeRejected\":true}\n",
    times.size(), static_cast<unsigned long long>(calls), static_cast<unsigned long long>(values), static_cast<unsigned long long>(missing), start, end);
  jpl_close_ephemeris(full); jpl_close_ephemeris(compact);
  return 0;
}
