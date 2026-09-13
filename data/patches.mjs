// GPL-2.0-or-later. Checked against pinned Find_Orb pl_cache.cpp.
// Compact JPL ephemerides must never silently switch to analytic positions.
export const strictEphemerisPatches = [{
  file: 'pl_cache.cpp',
  from: '   if( jpl_eph)\n      {\n      double state[6];',
  to: `   // -2 loads metadata without calculating an arbitrary J2000 position.
   if( planet_no == -2)
      {
      if( !jpl_eph)
         {
         fprintf( stderr, "Required JPL ephemeris could not be loaded.\\n");
         exit( 70);
         }
      return( 0);
      }
   if( planet_no > 0 && (!jpl_eph
       || !(jd > jpl_get_double( jpl_eph, JPL_EPHEM_START_JD)
         && jd <= jpl_get_double( jpl_eph, JPL_EPHEM_END_JD))))
      {
      fprintf( stderr, "JPL ephemeris unavailable or JD %.17g outside supported (start, end] range.\\n", jd);
      exit( 70);
      }

   if( jpl_eph)
      {
      double state[6];`,
  reason: 'Fail closed for missing data and all actual JPL queries outside the exact supported interval; lower endpoint is exclusive because a cropped file lacks the preceding Chebyshev record used by the full file at that instant.',
}, {
  file: 'pl_cache.cpp',
  from: '   planet_posn_raw( 3, J2000, vect_2000);',
  to: '   planet_posn_raw( -2, 0., NULL);  // Load JPL metadata without a synthetic epoch query.',
  reason: 'Metadata inspection must not demand J2000 coverage from a modern compact ephemeris.',
}, {
  file: 'pl_cache.cpp',
  from: '   if( planet_no < 0)          /* flag to unload everything */\n      rval = 0;',
  to: `   if( planet_no >= 0)
      {
      fprintf( stderr, "JPL ephemeris evaluation failed at JD %.17g; analytic fallback is disabled.\\n", jd);
      exit( 70);
      }
   if( planet_no < 0)          /* flag to unload everything */
      rval = 0;`,
  reason: 'Reject JPL read/evaluation errors instead of returning rough analytic planetary coordinates as successful results.',
}];
