// Explicit, checked portability and correctness patches against pinned sources.
// Keep this file with corresponding source; scientific changes need evidence.
import {strictEphemerisPatches} from '../data/patches.mjs';
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
},{
  file:'runge.cpp',
  from:`   const ldouble avals[N_EVALS_PLUS_ONE] = { 0, A_1, A_2, A_3, A_4, A_5,
             A_6, A_7, A_8, A_9, A_10, A_11, A_12, A_13 };`,
  to:`   const ldouble avals[N_EVALS_PLUS_ONE] = { A_1, A_2, A_3, A_4, A_5,
             A_6, A_7, A_8, A_9, A_10, A_11, A_12, A_13, 1. };`,
  reason:'PD stage j uses A_(j+1); the extra leading zero shifted time-dependent force evaluations. Source-extracted native/WASM counterexamples and corrected-step checks: verification/integrator/.',
},{
  file:'runge.cpp',
  from:`      rval += tval * tval;
      }
   return( sqrtl( rval * step * step));
}

#define ORIGINAL_FEHLBERG_CONSTANTS`,
  to:`      rval += tval * tval;
      }
   free( ivals[0]);
   return( sqrtl( rval * step * step));
}

#define ORIGINAL_FEHLBERG_CONSTANTS`,
  reason:'Release the PD step workspace after its last use; checked allocation-balance and native sanitizer evidence: verification/integrator/.',
},...strictEphemerisPatches];
