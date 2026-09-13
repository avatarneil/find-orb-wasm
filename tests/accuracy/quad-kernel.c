/* SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception */
#include <stdint.h>
extern long double reference_multf3(long double, long double);
extern long double candidate_multf3(long double, long double);
typedef union { long double f; uint32_t words[4]; uint64_t halves[2]; } bits;
static uint32_t next(uint32_t *state) {
  uint32_t x=*state; x^=x<<13; x^=x>>17; x^=x<<5; return *state=x;
}
static int mismatch(bits a,bits b) {
  bits ref,out;ref.f=reference_multf3(a.f,b.f);out.f=candidate_multf3(a.f,b.f);
  return ref.halves[0]!=out.halves[0] || ref.halves[1]!=out.halves[1];
}
int run_random(uint32_t seed,int count) {
  for(int i=0;i<count;++i) {
    bits a,b;for(int j=0;j<4;++j){a.words[j]=next(&seed);b.words[j]=next(&seed);}
    if(mismatch(a,b))return i+1;
  }
  return 0;
}
int run_edges(void) {
  // Both signs; zeros, tiny subnormals, normal boundaries, unit values,
  // maximum finite numbers, infinities, signaling and quiet NaN payloads.
  const uint64_t exponents[]={0,1,0x3ffe,0x3fff,0x7ffe,0x7fff};
  const uint64_t fractions[]={0,1,UINT64_C(0x800000000000),UINT64_C(0xffffffffffff)};
  const uint64_t lows[]={0,1,UINT64_C(0x8000000000000000),UINT64_MAX};
  bits values[192];int n=0;
  for(int sign=0;sign<2;++sign)for(int e=0;e<6;++e)for(int f=0;f<4;++f)for(int l=0;l<4;++l){
    bits x;x.halves[1]=((uint64_t)sign<<63)|(exponents[e]<<48)|fractions[f];x.halves[0]=lows[l];values[n++]=x;
  }
  for(int i=0;i<n;++i)for(int j=0;j<n;++j)if(mismatch(values[i],values[j]))return i*n+j+1;
  return 0;
}
uint32_t run_perf(int candidate,uint32_t seed,int count,int narrowed) {
  uint32_t checksum=0;
  for(int i=0;i<count;++i) {
    bits a,b,out;for(int j=0;j<4;++j){a.words[j]=next(&seed);b.words[j]=next(&seed);}
    // Normal finite operands of order unity, with full-width significands.
    a.words[3]=(a.words[3]&0xffff)|0x3fff0000;
    b.words[3]=(b.words[3]&0xffff)|0x3fff0000;
    if(narrowed){b.words[0]=0;b.words[1]&=0xf0000000;}
    out.f=candidate?candidate_multf3(a.f,b.f):reference_multf3(a.f,b.f);
    checksum^=out.words[0]^out.words[1]^out.words[2]^out.words[3];
  }
  return checksum;
}
