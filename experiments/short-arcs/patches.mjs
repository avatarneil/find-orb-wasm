// SPDX-License-Identifier: GPL-2.0-or-later
// Research-only transformations against the pinned Find_Orb orb_func.cpp.
// They preserve the upstream candidate generator, score gate, and default
// position selector. Exported candidates are heuristic samples, not a posterior.

const support = String.raw`
/* Experimental short-arc diagnostics.  Default selection remains upstream. */
static void research_sr_failure( const char *message)
{
   fprintf( stderr, "Short-arc research error: %s\n", message);
   abort( );
}

static int research_sr_selection_mode( void)
{
   const char *mode = get_environment_ptr( "SR_SELECTION");

   if( !*mode || !strcmp( mode, "position"))
      return( 0);
   if( !strcmp( mode, "phase6d"))
      return( 1);
   if( !strcmp( mode, "min-rms"))
      return( 2);
   research_sr_failure( "SR_SELECTION must be position, phase6d, or min-rms");
   return( -1);
}

static FILE *research_sr_open_candidates( const unsigned starting_orbit)
{
   const char *filename = get_environment_ptr( "SR_CANDIDATES_FILE");
   FILE *ofile = NULL;

   if( *filename)
      {
      ofile = fopen( filename, starting_orbit ? "ab" : "wb");
      if( !ofile)
         research_sr_failure( "Cannot open SR_CANDIDATES_FILE");
      if( !starting_orbit && fprintf( ofile,
                  "source_index,epoch_tt_jd,x_au,y_au,z_au,vx_au_day,vy_au_day,vz_au_day,heuristic_score,weighted_rms,n_residuals,rparam,vparam\n") < 0)
         research_sr_failure( "Cannot write candidate CSV header");
      }
   return( ofile);
}

static void research_sr_write_candidate( FILE *ofile, const unsigned source_index,
               const sr_orbit_t *candidate, const OBSERVE *obs, const int n_obs)
{
   if( ofile)
      {
      int n_residuals;
      const double weighted_rms = compute_weighted_rms( obs, n_obs, &n_residuals);
      int i;

      if( !isfinite( candidate->score) || !isfinite( weighted_rms))
         research_sr_failure( "Nonfinite candidate score or weighted RMS");
      if( fprintf( ofile, "%u,%.17g", source_index, obs[0].jd) < 0)
         research_sr_failure( "Cannot write candidate CSV epoch");
      for( i = 0; i < 6; i++)
         {
         if( !isfinite( candidate->orbit[i]))
            research_sr_failure( "Nonfinite candidate state");
         if( fprintf( ofile, ",%.17g", candidate->orbit[i]) < 0)
            research_sr_failure( "Cannot write candidate CSV state");
         }
      if( fprintf( ofile, ",%.17g,%.17g,%d,%.17g,%.17g\n",
                        candidate->score, weighted_rms, n_residuals,
                        candidate->rparam, candidate->vparam) < 0)
         research_sr_failure( "Cannot write candidate CSV diagnostics");
      }
}

static void research_sr_close_candidates( FILE *ofile)
{
   if( ofile && fclose( ofile))
      research_sr_failure( "Cannot close candidate CSV");
}

/* Unlike candidate CSV, this audit file never truncates on an initial-orbit
   retry. A caller may pre-create it empty when no SR search is performed. */
static void research_sr_write_batch( const unsigned starting_orbit,
               const unsigned n_observations, const unsigned max_orbits,
               const unsigned attempted, const unsigned successful,
               const double epoch)
{
   const char *filename = get_environment_ptr( "SR_BATCHES_FILE");

   if( *filename)
      {
      FILE *ofile = fopen( filename, "ab");
      long size;

      if( !ofile)
         research_sr_failure( "Cannot open SR_BATCHES_FILE");
      if( fseek( ofile, 0, SEEK_END) || (size = ftell( ofile)) < 0)
         research_sr_failure( "Cannot inspect batch CSV");
      if( !size && fprintf( ofile,
               "starting_orbit,n_observations,max_orbits,attempted,successful,epoch_tt_jd\n") < 0)
         research_sr_failure( "Cannot write batch CSV header");
      if( successful > attempted || attempted > max_orbits || !isfinite( epoch))
         research_sr_failure( "Invalid SR batch diagnostics");
      if( fprintf( ofile, "%u,%u,%u,%u,%u,%.17g\n", starting_orbit,
                        n_observations, max_orbits, attempted, successful, epoch) < 0)
         research_sr_failure( "Cannot write batch CSV diagnostics");
      if( fclose( ofile))
         research_sr_failure( "Cannot close batch CSV");
      }
}

/* Written only after SR acceptance and the nominal-state swap. Row i is the
   exact sr_orbits[i] used by subsequent ephemerides, including row 0 nominal.
   No set_locs or sigma evaluation occurs here; all states share epoch. */
static void research_sr_write_family( const double *orbits,
                  const unsigned n_orbits, const double epoch)
{
   const char *filename = get_environment_ptr( "SR_FAMILY_FILE");

   if( *filename)
      {
      FILE *ofile = fopen( filename, "wb");
      unsigned i, j;

      if( !ofile)
         research_sr_failure( "Cannot open SR_FAMILY_FILE");
      if( !isfinite( epoch))
         research_sr_failure( "Nonfinite family epoch");
      if( fprintf( ofile,
                  "family_index,epoch_tt_jd,x_au,y_au,z_au,vx_au_day,vy_au_day,vz_au_day\n") < 0)
         research_sr_failure( "Cannot write family CSV header");
      for( i = 0; i < n_orbits; i++)
         {
         if( fprintf( ofile, "%u,%.17g", i, epoch) < 0)
            research_sr_failure( "Cannot write family CSV epoch");
         for( j = 0; j < 6; j++)
            {
            const double value = orbits[i * 6 + j];

            if( !isfinite( value))
               research_sr_failure( "Nonfinite family state");
            if( fprintf( ofile, ",%.17g", value) < 0)
               research_sr_failure( "Cannot write family CSV state");
            }
         if( fputc( '\n', ofile) == EOF)
            research_sr_failure( "Cannot terminate family CSV row");
         }
      if( fclose( ofile))
         research_sr_failure( "Cannot close family CSV");
      }
}

`;

const selectors = String.raw`

static int research_sr_compare_double( const void *aptr, const void *bptr)
{
   const double a = *(const double *)aptr, b = *(const double *)bptr;

   return( (a > b) - (a < b));
}

static double research_sr_median( double *values, const unsigned n)
{
   qsort( values, n, sizeof( double), research_sr_compare_double);
   return( n % 2 ? values[n / 2] :
                     values[n / 2 - 1] / 2. + values[n / 2] / 2.);
}

/* phase6d is a nearest standardized coordinate-median selector, not a medoid.
   Each axis uses the unscaled median absolute deviation (MAD) in its own units.
   Coordinate medians use the average of the two central values for even n.
   Axes with MAD <= 64 * DBL_EPSILON * max(abs(coordinate)) are omitted.
   All six axes refer to heliocentric J2000 ecliptic states at the same TT epoch;
   the resulting estimator intentionally depends on this coordinate frame.
   Exact score ties retain the first candidate in upstream score-sorted order. */
static void research_sr_select_orbit( double *orbits, const unsigned n_orbits,
                                    OBSERVE *obs, const int n_obs)
{
   const int mode = research_sr_selection_mode( );
   unsigned i, j, best_idx = 0;
   double best_score = 0.;

   if( !mode)
      {
      find_median_orbit( orbits, n_orbits);
      return;
      }
   if( !n_orbits)
      research_sr_failure( "Cannot select an empty candidate family");
   if( mode == 1)
      {
      double median[6], scale[6];
      double *values = (double *)calloc( n_orbits, sizeof( double));

      if( !values)
         research_sr_failure( "Cannot allocate phase6d workspace");
      for( j = 0; j < 6; j++)
         {
         double max_abs = 0.;

         for( i = 0; i < n_orbits; i++)
            {
            values[i] = orbits[i * 6 + j];
            if( !isfinite( values[i]))
               research_sr_failure( "Nonfinite phase6d candidate state");
            if( max_abs < fabs( values[i]))
               max_abs = fabs( values[i]);
            }
         median[j] = research_sr_median( values, n_orbits);
         for( i = 0; i < n_orbits; i++)
            values[i] = fabs( orbits[i * 6 + j] - median[j]);
         scale[j] = research_sr_median( values, n_orbits);
         if( scale[j] <= 64. * DBL_EPSILON * max_abs)
            scale[j] = 0.;
         }
      for( i = 0; i < n_orbits; i++)
         {
         double score = 0.;

         for( j = 0; j < 6; j++)
            if( scale[j])
               {
               const double delta = (orbits[i * 6 + j] - median[j]) / scale[j];

               score += delta * delta;
               }
         if( !isfinite( score))
            research_sr_failure( "Nonfinite phase6d selection score");
         if( !i || score < best_score)
            {
            best_score = score;
            best_idx = i;
            }
         }
      free( values);
      }
   else                       /* diagnostic only: minimum weighted residual RMS */
      for( i = 0; i < n_orbits; i++)
         {
         double score;

         if( set_locs( orbits + i * 6, obs[0].jd, obs, n_obs))
            research_sr_failure( "Cannot evaluate min-rms candidate");
         score = compute_weighted_rms( obs, n_obs, NULL);
         if( !isfinite( score))
            research_sr_failure( "Nonfinite min-rms selection score");
         if( !i || score < best_score)
            {
            best_score = score;
            best_idx = i;
            }
         }
   for( j = 0; j < 6; j++)
      {
      const double value = orbits[j];

      orbits[j] = orbits[best_idx * 6 + j];
      orbits[best_idx * 6 + j] = value;
      }
}

`;

export const patches = [{
  file: 'orb_func.cpp',
  from: '#include <math.h>',
  to: '#include <math.h>\n#include <float.h> /* experimental MAD degeneracy floor */',
  reason: 'Define the documented binary64 relative roundoff floor for experimental phase6d axis scaling.',
}, {
  file: 'orb_func.cpp',
  from: 'int get_sr_orbits( sr_orbit_t *orbits, OBSERVE FAR *obs,',
  to: support + 'int get_sr_orbits( sr_orbit_t *orbits, OBSERVE FAR *obs,',
  reason: 'Add opt-in CSV diagnostics and reject invalid experimental selection modes explicitly.',
}, {
  file: 'orb_func.cpp',
  from: '   sr_orbit_t *tptr = orbits;\n\n   INTENTIONALLY_UNUSED_PARAMETER( noise_in_sigmas);',
  to: '   sr_orbit_t *tptr = orbits;\n   FILE *research_candidates = research_sr_open_candidates( starting_orbit);\n\n   INTENTIONALLY_UNUSED_PARAMETER( noise_in_sigmas);',
  reason: 'Open requested diagnostic output once per SR batch; an initial batch starts a new CSV.',
}, {
  file: 'orb_func.cpp',
  from: '         tptr->score = evaluate_initial_orbit( obs, n_obs, tptr->orbit, obs[0].jd);\n         tptr++;',
  to: '         tptr->score = evaluate_initial_orbit( obs, n_obs, tptr->orbit, obs[0].jd);\n         research_sr_write_candidate( research_candidates, i + starting_orbit, tptr, obs, n_obs);\n         tptr++;',
  reason: 'Export every successful generated state and its contemporaneous weighted residuals before qsort or nominal selection; no candidate membership changes.',
}, {
  file: 'orb_func.cpp',
  from: '   rval = (unsigned)( tptr - orbits);\n   qsort( orbits, rval, sizeof( sr_orbit_t), sr_orbit_compare);',
  to: '   research_sr_close_candidates( research_candidates);\n   rval = (unsigned)( tptr - orbits);\n   research_sr_write_batch( starting_orbit, n_obs, max_orbits, i, rval, (n_obs ? obs[0].jd : 0.));\n   qsort( orbits, rval, sizeof( sr_orbit_t), sr_orbit_compare);',
  reason: 'Close candidate output and append actual attempt/success counts for every completed SR batch, including retries that truncate candidate CSV.',
}, {
  file: 'orb_func.cpp',
  from: '#define INITIAL_ORBIT_NOT_YET_FOUND       -2',
  to: selectors + '#define INITIAL_ORBIT_NOT_YET_FOUND       -2',
  reason: 'Add phase6d and minimum-weighted-RMS representative selectors; preserve the original position selector verbatim.',
}, {
  file: 'orb_func.cpp',
  from: '   const int max_time = atoi( get_environment_ptr( "IOD_TIMEOUT"));\n\n   for( i = 0; i < 6; i++)',
  to: '   const int max_time = atoi( get_environment_ptr( "IOD_TIMEOUT"));\n\n   (void)research_sr_selection_mode( );\n   for( i = 0; i < 6; i++)',
  reason: 'Reject an invalid SR_SELECTION before an initial fit, including cases which later bypass SR.',
}, {
  file: 'orb_func.cpp',
  from: '         find_median_orbit( sr_orbits, n_sr_orbits);',
  to: '         research_sr_select_orbit( sr_orbits, n_sr_orbits, obs, n_obs);\n         research_sr_write_family( sr_orbits, n_sr_orbits, orbit_epoch);',
  reason: 'Dispatch nominal selection and optionally export exact accepted-family order after its swap; unset or position uses the unchanged upstream selector.',
}];

export function applyShortArcPatches(source) {
  for (const patch of patches) {
    if (source.split(patch.from).length !== 2) {
      throw new Error('Short-arc experiment patch context changed: ' + patch.reason);
    }
    source = source.replace(patch.from, patch.to);
  }
  return source;
}
