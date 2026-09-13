/* SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 * Exact unsigned 128 x 128 -> 256 multiplication for LLVM compiler-rt.
 * Each base-2^32 update is <= (B-1)^2 + 2(B-1) = 2^64-1.
 * Only native WebAssembly i64 operations are needed in the hot loop.
 * IEEE binary128 normalization, special values, and rounding are unchanged.
 */
static __inline void wideMultiply(rep_t a, rep_t b, rep_t *hi, rep_t *lo) {
  // Compiler-rt shifts one significand left by 15 before this call. Values
  // widened from binary64 therefore often have an all-zero low 64-bit limb.
  // Multiplication is commutative; put such an operand second when available.
  if ((uint64_t)a == 0) { const rep_t swap = a; a = b; b = swap; }
  if ((uint64_t)b == 0) {
    const uint32_t av[4] = {(uint32_t)a, (uint32_t)(a >> 32),
                           (uint32_t)(a >> 64), (uint32_t)(a >> 96)};
    const uint32_t bv[2] = {(uint32_t)(b >> 64), (uint32_t)(b >> 96)};
    uint32_t out[6] = {0};
    // Compute a*(b/2^64) in six limbs, then apply the exact 64-bit shift.
    for (unsigned i = 0; i < 4; ++i) {
      uint64_t carry = 0;
      for (unsigned j = 0; j < 2; ++j) {
        const uint64_t value = (uint64_t)av[i] * bv[j] + out[i + j] + carry;
        out[i + j] = (uint32_t)value;
        carry = value >> 32;
      }
      out[i + 2] = (uint32_t)carry;
    }
    *lo = ((rep_t)out[0] << 64) | ((rep_t)out[1] << 96);
    *hi = (rep_t)out[2] | ((rep_t)out[3] << 32) |
          ((rep_t)out[4] << 64) | ((rep_t)out[5] << 96);
    return;
  }
  const uint32_t av[4] = {(uint32_t)a, (uint32_t)(a >> 32),
                         (uint32_t)(a >> 64), (uint32_t)(a >> 96)};
  const uint32_t bv[4] = {(uint32_t)b, (uint32_t)(b >> 32),
                         (uint32_t)(b >> 64), (uint32_t)(b >> 96)};
  uint32_t out[8] = {0};
  for (unsigned i = 0; i < 4; ++i) {
    uint64_t carry = 0;
    for (unsigned j = 0; j < 4; ++j) {
      const uint64_t value = (uint64_t)av[i] * bv[j] + out[i + j] + carry;
      out[i + j] = (uint32_t)value;
      carry = value >> 32;
    }
    // This digit has not been touched by an earlier row (whose last is i+3).
    out[i + 4] = (uint32_t)carry;
  }
  *lo = (rep_t)out[0] | ((rep_t)out[1] << 32) |
        ((rep_t)out[2] << 64) | ((rep_t)out[3] << 96);
  *hi = (rep_t)out[4] | ((rep_t)out[5] << 32) |
        ((rep_t)out[6] << 64) | ((rep_t)out[7] << 96);
}
