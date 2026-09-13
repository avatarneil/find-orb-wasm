// SPDX-License-Identifier: GPL-2.0-or-later
// Test scaffold only. selector.test.mjs inserts the actual pinned/patched
// selector, sorting, and export functions at the marker below before compiling.
// Observation evaluation is stubbed: this checks selectors and CSV transport,
// not the physical force model, astrometric likelihood, or orbit propagation.
#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <float.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#ifndef _WIN32
#include <alloca.h>
#endif
#define INTENTIONALLY_UNUSED_PARAMETER(x) ((void)(x))
#define FAR
#define ELEM_OUT_NO_COMMENT_DATA 1
#define ELEM_OUT_PRECISE_MEAN_RESIDS 2

struct OBSERVE { double jd, sentinel; };
struct sr_orbit_t { double rparam, vparam, orbit[6], score; };
static double stub_rms = .125;
static int set_locs_calls = 0, residual_calls = 0;
static unsigned generator_calls = 0;
const char *elements_filename = "unused-elements.txt";
int append_elements_to_element_file = 0;

const char *get_environment_ptr(const char *name)
{
   const char *value = getenv(name);
   return value ? value : "";
}

double compute_weighted_rms(const OBSERVE *, int, int *n)
{
   residual_calls++;
   if(n) *n = 8;
   return stub_rms;
}

int set_locs(const double *orbit, double, OBSERVE *obs, int)
{
   set_locs_calls++;
   obs->sentinel += 1.;
   stub_rms = fabs(orbit[3]);
   return 0;
}

// Deterministic generator/refinement failures let the actual get_sr_orbits
// loop prove that attempted and successful counts mean different things.
int find_nth_sr_orbit(sr_orbit_t *candidate, OBSERVE *, int, int index)
{
   generator_calls++;
   for(int j = 0; j < 6; j++) candidate->orbit[j] = index + j * .01;
   candidate->rparam = .25;
   candidate->vparam = -.5;
   return index % 3 == 0 ? -1 : 0;
}

int adjust_herget_results(OBSERVE *, int, double *orbit)
{
   return (int)orbit[0] % 5 == 0 ? -1 : 0;
}

double evaluate_initial_orbit(const OBSERVE *, int, const double *orbit, double)
{
   return orbit[0] / 100.;
}

double find_epoch_shown(const OBSERVE *obs, int) { return obs[0].jd; }
int write_out_elements_to_file(...) { return 0; }

// @SOURCE_FUNCTIONS@

static const double input[30] = {
   1., 4., -3., .003, -.002, .001,
   1.1, 3.8, -2.9, .004, -.0021, .0015,
   .9, 4.2, -3.1, .002, -.0019, .0005,
   1.02, 3.95, -3.03, .0025, -.00205, .0009,
   9., -7., 6., .2, .4, -.5
};

static int identify_first(const double *states)
{
   for(int i = 0; i < 5; i++)
      if(!memcmp(states, input + 6 * i, 6 * sizeof(double)))
         return i;
   return -1;
}

int main(int argc, char **argv)
{
   assert(argc >= 2);
   double a[30], b[30], c[30];
   OBSERVE obs = {2461150.5, 17.25};

   if(!strcmp(argv[1], "default"))
      {
      for(int explicit_mode = 0; explicit_mode < 2; explicit_mode++)
         {
         const OBSERVE saved = obs;
         memcpy(a, input, sizeof a);
         memcpy(b, input, sizeof b);
         if(explicit_mode) setenv("SR_SELECTION", "position", 1);
         else unsetenv("SR_SELECTION");
         find_median_orbit(a, 5);
         research_sr_select_orbit(b, 5, &obs, 1);
         assert(!memcmp(a, b, sizeof a));
         assert(!memcmp(&obs, &saved, sizeof obs));
         assert(set_locs_calls == 0 && residual_calls == 0);
         }
      }
   else if(!strcmp(argv[1], "phase6d"))
      {
      setenv("SR_SELECTION", "phase6d", 1);
      memcpy(a, input, sizeof a);
      research_sr_select_orbit(a, 5, &obs, 1);
      const int selected = identify_first(a);
      assert(selected >= 0);
      for(int i = 0; i < 5; i++)
         {
         int found = 0;
         for(int j = 0; j < 5; j++)
            if(!memcmp(input + 6 * i, a + 6 * j, 6 * sizeof(double))) found++;
         assert(found == 1);
         }
      const double factors[6] = {1000., .1, 7., 86400., .01, 1.e6};
      memcpy(b, input, sizeof b);
      for(int i = 0; i < 30; i++) b[i] *= factors[i % 6];
      research_sr_select_orbit(b, 5, &obs, 1);
      for(int j = 0; j < 6; j++)
         assert(b[j] == input[selected * 6 + j] * factors[j]);
      for(int i = 0; i < 5; i++) memcpy(c + 6 * i, input + 6 * (4 - i), 6 * sizeof(double));
      research_sr_select_orbit(c, 5, &obs, 1);
      assert(!memcmp(a, c, 6 * sizeof(double)));
      assert(set_locs_calls == 0 && residual_calls == 0);
      assert(obs.sentinel == 17.25);
      }
   else if(!strcmp(argv[1], "degenerate"))
      {
      setenv("SR_SELECTION", "phase6d", 1);
      for(int i = 0; i < 30; i++) c[i] = i % 6 ? 1. : 0.;
      memcpy(b, c, sizeof b);
      research_sr_select_orbit(c, 5, &obs, 1);
      assert(!memcmp(b, c, sizeof b));
      // This near-constant coordinate has a nonzero MAD below its relative
      // roundoff floor. Omitting it gives a deterministic first-state tie.
      for(int i = 0; i < 5; i++) c[6 * i] = 1. + i * DBL_EPSILON;
      memcpy(b, c, sizeof b);
      research_sr_select_orbit(c, 5, &obs, 1);
      assert(!memcmp(b, c, sizeof b));
      double even[4] = {100., 2., -100., 4.};
      assert(research_sr_median(even, 4) == 3.);
      double equal[4] = {1., 1., 1., 1.};
      assert(research_sr_median(equal, 4) == 1.);
      assert(research_sr_compare_double(equal, equal + 1) == 0);
      }
   else if(!strcmp(argv[1], "min-rms"))
      {
      setenv("SR_SELECTION", "min-rms", 1);
      memcpy(a, input, sizeof a);
      research_sr_select_orbit(a, 5, &obs, 1);
      assert(identify_first(a) == 2);
      assert(set_locs_calls == 5 && residual_calls == 5);
      }
   else if(!strcmp(argv[1], "invalid"))
      {
      setenv("SR_SELECTION", "invalid-mode", 1);
      research_sr_selection_mode();
      return 1;
      }
   else if(!strcmp(argv[1], "nonfinite"))
      {
      setenv("SR_SELECTION", "phase6d", 1);
      memcpy(a, input, sizeof a);
      a[4] = NAN;
      research_sr_select_orbit(a, 5, &obs, 1);
      return 1;
      }
   else if(!strcmp(argv[1], "empty"))
      {
      setenv("SR_SELECTION", "phase6d", 1);
      research_sr_select_orbit(a, 0, &obs, 1);
      return 1;
      }
   else if(!strcmp(argv[1], "csv"))
      {
      assert(argc == 3);
      setenv("SR_CANDIDATES_FILE", argv[2], 1);
      sr_orbit_t candidate = {.2, -.4, {1., 2., 3., .004, .005, .006}, .625};
      const OBSERVE saved = obs;
      FILE *file = research_sr_open_candidates(0);
      research_sr_write_candidate(file, 7, &candidate, &obs, 4);
      research_sr_close_candidates(file);
      file = research_sr_open_candidates(47);
      research_sr_write_candidate(file, 48, &candidate, &obs, 4);
      research_sr_close_candidates(file);
      assert(!memcmp(&saved, &obs, sizeof obs));
      assert(set_locs_calls == 0 && residual_calls == 2);
      }
   else if(!strcmp(argv[1], "csv-unset"))
      {
      unsetenv("SR_CANDIDATES_FILE");
      FILE *file = research_sr_open_candidates(0);
      assert(file == NULL);
      research_sr_write_candidate(file, 0, NULL, NULL, 0);
      research_sr_close_candidates(file);
      unsetenv("SR_BATCHES_FILE");
      unsetenv("SR_FAMILY_FILE");
      research_sr_write_batch(0, 4, 10, 10, 7, obs.jd);
      research_sr_write_family(NULL, 0, obs.jd);
      assert(set_locs_calls == 0 && residual_calls == 0);
      }
   else if(!strcmp(argv[1], "family"))
      {
      assert(argc == 3);
      setenv("SR_FAMILY_FILE", argv[2], 1);
      setenv("SR_SELECTION", "position", 1);
      const OBSERVE saved = obs;
      memcpy(a, input, sizeof a);
      research_sr_select_orbit(a, 5, &obs, 1);
      memcpy(b, a, sizeof b);
      research_sr_write_family(a, 5, obs.jd);
      assert(!memcmp(a, b, sizeof a));
      assert(!memcmp(&saved, &obs, sizeof obs));
      assert(set_locs_calls == 0 && residual_calls == 0);
      printf("nominal_source_index=%d\n", identify_first(a));
      }
   else if(!strcmp(argv[1], "family-nonfinite"))
      {
      assert(argc == 3);
      setenv("SR_FAMILY_FILE", argv[2], 1);
      memcpy(a, input, sizeof a);
      a[4] = NAN;
      research_sr_write_family(a, 5, obs.jd);
      return 1;
      }
   else if(!strcmp(argv[1], "batches"))
      {
      assert(argc == 4);
      setenv("SR_BATCHES_FILE", argv[2], 1);
      setenv("SR_CANDIDATES_FILE", argv[3], 1);
      sr_orbit_t candidates[10];
      const OBSERVE saved = obs;
      // max_time=0 ensures this tests the extracted fixed-count branch,
      // rather than accidentally depending on the host being fast enough.
      assert(get_sr_orbits(candidates, &obs, 4, 0, 8, 0., 0., 0) == 4);
      assert(get_sr_orbits(candidates, &obs, 4, 20, 4, 0., 0., 0) == 2);
      // A fresh initial-orbit retry truncates candidate CSV but must retain
      // both earlier batch audit rows. This is the upstream retry behavior.
      assert(get_sr_orbits(candidates, &obs, 4, 0, 10, 0., 0., 0) == 5);
      assert(generator_calls == 22);
      assert(!memcmp(&saved, &obs, sizeof obs));
      assert(set_locs_calls == 0);
      }
   else if(!strcmp(argv[1], "invalid-batch"))
      {
      assert(argc == 3);
      setenv("SR_BATCHES_FILE", argv[2], 1);
      research_sr_write_batch(0, 4, 10, 11, 7, obs.jd);
      return 1;
      }
   else return 2;
   printf("PASS %s\n", argv[1]);
   return 0;
}
