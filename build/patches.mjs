// Explicit, checked portability patches against the pinned upstream sources.
// No orbital arithmetic is changed. Keep this file with corresponding source.
export const patches=[{
  file:'fo.cpp',
  from:'#if defined( __linux) || defined( __unix__) || defined( __APPLE__)',
  to:'#if !defined(__EMSCRIPTEN__) && (defined( __linux) || defined( __unix__) || defined( __APPLE__))',
  reason:'Browser worker termination replaces POSIX fork and CPU limits.',
},{
  file:'shellsor.cpp',
  from:`   void (*p)() = (void (*)())compar;

   return( bsearch_ext_r( key, base0, nmemb, size,
               (int (*)( const void *, const void *, void *))p,
               NULL, found));`,
  to:`   // WebAssembly requires exact indirect-call signatures.
   const auto adapter = [](const void *a, const void *b, void *context) -> int
      {
      const auto compare = static_cast<int (**)(const void *, const void *)>(context);
      return( (*compare)(a, b));
      };
   return( bsearch_ext_r( key, base0, nmemb, size, adapter, &compar, found));`,
  reason:'Replace undefined function-pointer cast with a typed context adapter.',
},{
  file:'orb_func.cpp',
  from:'   for( i = 0; i < max_orbits && clock( ) < end_clock; i++)',
  to:`#ifdef __EMSCRIPTEN__
   // Complete the configured candidate count; the worker enforces wall time.
   // A CPU-speed-dependent partial search must not become a completed fit.
   (void)end_clock;
   for( i = 0; i < max_orbits; i++)
#else
   for( i = 0; i < max_orbits && clock( ) < end_clock; i++)
#endif`,
  reason:'Finish the candidate count instead of silently truncating the search after half a CPU-second.',
}];
