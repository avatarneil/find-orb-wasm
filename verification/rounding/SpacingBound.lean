import FiniteFormat
import Mathlib.Data.Nat.Find

/- GPL-2.0-or-later. Derive universal rounding error from finite format spacing. -/
namespace FindOrbRounding
noncomputable section

theorem grid_value_representable (f N n q : ℕ) (delta : ℝ)
    (hn : n ≤ N) (hq : q ≤ 2^(f+1)) (hl : n = 0 ∨ 2^f ≤ q) :
    ∃ v : Encoding f N, value delta v = (q : ℝ) * delta * (2 : ℝ)^n := by
  by_cases hcarry : q = 2^(f+1)
  · refine ⟨(false, ⟨n+2, by omega⟩, ⟨0, by positivity⟩), ?_⟩
    simp [value, magnitude, significand, hcarry, Nat.cast_pow, Nat.cast_ofNat,
      pow_succ]
    ring
  · have hqstrict : q < 2^(f+1) := by omega
    by_cases hnormal : 2^f ≤ q
    · have hfrac : q - 2^f < 2^f := by
        rw [pow_succ] at hqstrict
        omega
      refine ⟨(false, ⟨n+1, by omega⟩, ⟨q-2^f, hfrac⟩), ?_⟩
      simp [value, magnitude, significand, Nat.cast_sub hnormal]
    · have hnzero : n = 0 := hl.resolve_right hnormal
      have hqsmall : q < 2^f := by omega
      refine ⟨(false, ⟨0, by omega⟩, ⟨q, hqsmall⟩), ?_⟩
      simp [value, magnitude, significand, hnzero]

theorem exists_close_value_nonnegative (f N : ℕ) (delta a : ℝ)
    (hd : 0 < delta) (ha : 0 ≤ a)
    (hmax : a < (2 : ℝ)^(f+1) * delta * (2 : ℝ)^N) :
    ∃ v : Encoding f N,
      |value delta v - a| ≤ a / (2 : ℝ)^(f+1) + delta/2 := by
  classical
  have exists_bin : ∃ n : ℕ, a < (2 : ℝ)^(f+1) * delta * (2 : ℝ)^n := ⟨N, hmax⟩
  let n := Nat.find exists_bin
  have hn : n ≤ N := Nat.find_min' exists_bin hmax
  have hupper : a < (2 : ℝ)^(f+1) * delta * (2 : ℝ)^n := Nat.find_spec exists_bin
  let step : ℝ := delta * (2 : ℝ)^n
  have hs : 0 < step := mul_pos hd (by positivity)
  have hlower : n = 0 ∨ (2 : ℝ)^f * step ≤ a := by
    by_cases hzero : n = 0
    · exact Or.inl hzero
    · right
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hmin := Nat.find_min exists_bin (show k < n by omega)
      have hprev : (2 : ℝ)^(f+1) * delta * (2 : ℝ)^k ≤ a := le_of_not_gt hmin
      dsimp [step]
      rw [hk, pow_succ, pow_succ] at *
      nlinarith
  let y := a / step
  have hy : 0 ≤ y := div_nonneg ha hs.le
  let q := nearestNat y
  have hyupper : y < (2 : ℝ)^(f+1) := by
    apply (div_lt_iff₀ hs).2
    dsimp [step]
    nlinarith [hupper]
  have hq : q ≤ 2^(f+1) := by
    have hf : ⌊y⌋₊ < 2^(f+1) := (Nat.floor_lt hy).2 (by exact_mod_cast hyupper)
    have h := nearestNat_upper y
    dsimp [q]
    omega
  have hqlower : n = 0 ∨ 2^f ≤ q := by
    rcases hlower with hzero | hnorm
    · exact Or.inl hzero
    · right
      have hratio : (2 : ℝ)^f ≤ y := (le_div_iff₀ hs).2 hnorm
      have hfloor : 2^f ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).2 (by exact_mod_cast hratio)
      exact le_trans hfloor (nearestNat_lower y)
  obtain ⟨v, hv⟩ := grid_value_representable f N n q delta hn hq hqlower
  refine ⟨v, ?_⟩
  have hlocal : |value delta v - a| ≤ step/2 := by
    have he := mul_le_mul_of_nonneg_right (nearestNat_error y hy) hs.le
    have hid : value delta v - a = ((q : ℝ) - y) * step := by
      rw [hv]
      dsimp [y, step]
      field_simp
    rw [hid, abs_mul, abs_of_pos hs]
    dsimp [q] at *
    linarith
  rcases hlower with hzero | hnorm
  · have hstep : step = delta := by simp [step, hzero]
    rw [hstep] at hlocal
    have hnonneg : 0 ≤ a / (2 : ℝ)^(f+1) := by positivity
    linarith
  · have hnrelative : step/2 ≤ a / (2 : ℝ)^(f+1) := by
      apply (le_div_iff₀ (by positivity)).2
      rw [pow_succ]
      nlinarith [hnorm]
    linarith

def negateEncoding {f n : ℕ} (v : Encoding f n) : Encoding f n := (!v.1, v.2)

theorem value_negate {f n : ℕ} (delta : ℝ) (v : Encoding f n) :
    value delta (negateEncoding v) = -value delta v := by
  rcases v with ⟨s, fields⟩
  cases s <;> simp [negateEncoding, value, magnitude, significand]

theorem roundFormat_error (f N : ℕ) (delta x : ℝ)
    (hd : 0 < delta)
    (hmax : |x| < (2 : ℝ)^(f+1) * delta * (2 : ℝ)^N) :
    |roundFormat f N delta x - x| ≤ |x| / (2 : ℝ)^(f+1) + delta/2 := by
  obtain ⟨v, hv⟩ := exists_close_value_nonnegative f N delta |x| hd (abs_nonneg x) hmax
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx] at hv ⊢
    exact le_trans (roundFormat_le_candidate f N delta x v) hv
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hsame : |value delta (negateEncoding v) - x| = |value delta v - (|x|)| := by
      rw [value_negate, abs_of_nonpos hx']
      have heq : -value delta v - x = -(value delta v - -x) := by ring
      rw [heq, abs_neg]
    rw [← hsame] at hv
    exact le_trans (roundFormat_le_candidate f N delta x (negateEncoding v)) hv

theorem any_nearest_error (f N : ℕ) (delta x : ℝ) (v : Encoding f N)
    (hd : 0 < delta)
    (hmax : |x| < (2 : ℝ)^(f+1) * delta * (2 : ℝ)^N)
    (hv : IsNearest delta x v) :
    |value delta v - x| ≤ |x| / (2 : ℝ)^(f+1) + delta/2 :=
  le_trans (hv (nearestEvenEncoding f N delta x)) (roundFormat_error f N delta x hd hmax)

#print axioms grid_value_representable
#print axioms exists_close_value_nonnegative
#print axioms value_negate
#print axioms roundFormat_error
#print axioms any_nearest_error
end
end FindOrbRounding
