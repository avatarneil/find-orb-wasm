/* Extracted Project Pluto GPL-2.0-or-later source; see root LICENSE. */
#include <math.h>
#define DLL_FUNC
extern "C" {
double DLL_FUNC dot_product( const double *a, const double *b)
{
   return( a[0] * b[0] + a[1] * b[1] + a[2] * b[2]);
}

void DLL_FUNC vector_cross_product( double *xprod, const double *a, const double *b)
{
   xprod[0] = a[1] * b[2] - a[2] * b[1];
   xprod[1] = a[2] * b[0] - a[0] * b[2];
   xprod[2] = a[0] * b[1] - a[1] * b[0];
}

double DLL_FUNC vector3_length( const double *vect)
{
   return( sqrt( vect[0] * vect[0] + vect[1] * vect[1] + vect[2] * vect[2]));
}

double DLL_FUNC normalize_vect3( double *vect)
{
   const double d2 = vect[0] * vect[0] + vect[1] * vect[1]
                                       + vect[2] * vect[2];
   const double d = sqrt( d2);
   if( d)
      {
      vect[0] /= d;
      vect[1] /= d;
      vect[2] /= d;
      }
   return( d);
}
}
