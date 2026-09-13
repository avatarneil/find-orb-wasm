import SpacingBound
import BridgeSupport

/- GPL-2.0-or-later. Concrete binary64/binary128 format instantiations. -/
namespace FindOrbRounding
noncomputable section

theorem power_scale (a b c k : ℕ) (h : a + c = k + b) :
    (2 : ℝ)^a * (1 / (2 : ℝ)^b) * (2 : ℝ)^c = (2 : ℝ)^k := by
  have he : (2 : ℝ)^a * (2 : ℝ)^c = (2 : ℝ)^k * (2 : ℝ)^b := by
    rw [← pow_add, ← pow_add, h]
  calc
    (2 : ℝ)^a * (1 / (2 : ℝ)^b) * (2 : ℝ)^c =
        ((2 : ℝ)^a * (2 : ℝ)^c) / (2 : ℝ)^b := by ring
    _ = (2 : ℝ)^k := (div_eq_iff (by positivity)).2 he

theorem half_minimum_subnormal (e : ℕ) :
    (1 / (2 : ℝ)^e) / 2 = 1 / (2 : ℝ)^(e+1) := by
  rw [pow_succ, div_div]

theorem conservative_subnormal (a b : ℕ) (h : a ≤ b) :
    (1 : ℝ) / (2 : ℝ)^b ≤ 1 / (2 : ℝ)^a := by
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) h

def roundBinary64 : ℝ → ℝ := roundFormat 52 2044 (1 / (2 : ℝ)^1074)
def roundBinary128 : ℝ → ℝ := roundFormat 112 32764 (1 / (2 : ℝ)^16494)

theorem binary64_error (x : ℝ) (hx : |x| < (2 : ℝ)^1023) :
    |roundBinary64 x - x| ≤ (1 : ℝ)/(2 : ℝ)^53 * |x| + 1/(2 : ℝ)^1075 := by
  have hmax : |x| < (2 : ℝ)^(52+1) * (1/(2 : ℝ)^1074) * (2 : ℝ)^2044 := by
    rw [power_scale 53 1074 2044 1023 (by decide)]
    exact hx
  have he := roundFormat_error 52 2044 (1/(2 : ℝ)^1074) x (by positivity) hmax
  rw [half_minimum_subnormal] at he
  simpa only [roundBinary64, div_eq_mul_inv, one_mul, mul_comm] using he

theorem binary128_error (x : ℝ) (hx : |x| < (2 : ℝ)^16383) :
    |roundBinary128 x - x| ≤ (1 : ℝ)/(2 : ℝ)^113 * |x| + 1/(2 : ℝ)^16495 := by
  have hmax : |x| < (2 : ℝ)^(112+1) * (1/(2 : ℝ)^16494) * (2 : ℝ)^32764 := by
    rw [power_scale 113 16494 32764 16383 (by decide)]
    exact hx
  have he := roundFormat_error 112 32764 (1/(2 : ℝ)^16494) x (by positivity) hmax
  rw [half_minimum_subnormal] at he
  simpa only [roundBinary128, div_eq_mul_inv, one_mul, mul_comm] using he

theorem binary64_roundingModel : FindOrbEphemerisBridge.RoundingModel roundBinary64 := by
  intro x hx
  exact le_trans (binary64_error x hx) (add_le_add_left
    (conservative_subnormal 100 1075 (by decide)) _)

theorem binary128_conservative_error (x : ℝ) (hx : |x| < (2 : ℝ)^16383) :
    |roundBinary128 x - x| ≤ (1 : ℝ)/(2 : ℝ)^113 * |x| + 1/(2 : ℝ)^200 :=
  le_trans (binary128_error x hx) (add_le_add_left
    (conservative_subnormal 200 16495 (by decide)) _)

theorem binary128_bounded_error (x : ℝ) (hx : |x| < 100) :
    |roundBinary128 x - x| ≤ (1 : ℝ)/(2 : ℝ)^113 * |x| + 1/(2 : ℝ)^200 := by
  have hpow : (2 : ℝ)^7 ≤ (2 : ℝ)^16383 :=
    pow_le_pow_right₀ (by norm_num) (by decide)
  have hbound : (100 : ℝ) < (2 : ℝ)^16383 :=
    lt_of_lt_of_le (by norm_num : (100 : ℝ) < (2 : ℝ)^7) hpow
  exact binary128_conservative_error x (lt_trans hx hbound)

#print axioms power_scale
#print axioms half_minimum_subnormal
#print axioms conservative_subnormal
#print axioms binary64_error
#print axioms binary128_error
#print axioms binary64_roundingModel
#print axioms binary128_conservative_error
#print axioms binary128_bounded_error
end
end FindOrbRounding
