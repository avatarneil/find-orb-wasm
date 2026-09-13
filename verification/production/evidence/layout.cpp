// GPL-2.0-or-later. Actual wasm32 C++ layout contract.
#include <cstdio>
#include <cstdint>
#include <cstddef>
#include "jpl_int.h"
static_assert(sizeof(void*)==4 && sizeof(unsigned)==4 && sizeof(double)==8);
static_assert(offsetof(jpl_eph_data,ipt)==48);
static_assert(offsetof(jpl_eph_data,pvsun)==256);
static_assert(offsetof(jpl_eph_data,cache)==336);
static_assert(offsetof(jpl_eph_data,iinfo)==344);
static_assert(offsetof(jpl_eph_data,iinfo)+offsetof(interpolation_info,vel_coeff)==488);
static_assert(offsetof(jpl_eph_data,iinfo)+offsetof(interpolation_info,twot)==632);
static_assert(offsetof(jpl_eph_data,iinfo)+offsetof(interpolation_info,n_posn_avail)==640);
static_assert(offsetof(jpl_eph_data,iinfo)+offsetof(interpolation_info,n_vel_avail)==644);
static_assert(MAX_CHEBY==18);
