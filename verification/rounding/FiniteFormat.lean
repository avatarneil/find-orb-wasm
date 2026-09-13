import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- GPL-2.0-or-later. Finite binary values and nearest-even selection.
No arithmetic error bound is an assumption of the rounding definition. -/
namespace FindOrbRounding
noncomputable section

def nearestNat (x : ℝ) : ℕ :=
  if x - (⌊x⌋₊ : ℝ) < 1/2 ∨
      (x - (⌊x⌋₊ : ℝ) = 1/2 ∧ ⌊x⌋₊ % 2 = 0)
  then ⌊x⌋₊ else ⌊x⌋₊ + 1

theorem nearestNat_lower (x : ℝ) : ⌊x⌋₊ ≤ nearestNat x := by
  unfold nearestNat
  split_ifs <;> omega

theorem nearestNat_upper (x : ℝ) : nearestNat x ≤ ⌊x⌋₊ + 1 := by
  unfold nearestNat
  split_ifs <;> omega

theorem nearestNat_error (x : ℝ) (hx : 0 ≤ x) :
    |(nearestNat x : ℝ) - x| ≤ 1/2 := by
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one x
  unfold nearestNat
  split_ifs with h
  · rw [abs_le]
    rcases h with h | ⟨h, _⟩ <;> constructor <;> linarith
  · have hhalf : (1 : ℝ)/2 ≤ x - (⌊x⌋₊ : ℝ) := by
      by_contra hn
      exact h (Or.inl (lt_of_not_ge hn))
    rw [Nat.cast_add, Nat.cast_one, abs_le]
    constructor <;> linarith

theorem nearestNat_half_even (m : ℕ) :
    nearestNat ((m : ℝ) + 1/2) % 2 = 0 := by
  have hf : ⌊(m : ℝ) + 1/2⌋₊ = m := by
    apply (Nat.floor_eq_iff (by positivity)).2
    constructor <;> linarith
  unfold nearestNat
  rw [hf]
  have hfrac : (m : ℝ) + 1/2 - m = 1/2 := by ring
  rw [hfrac]
  by_cases h : m % 2 = 0
  · simp [h]
  · simp [h]
    omega

abbrev Encoding (fractionBits maxBin : ℕ) :=
  Bool × Fin (maxBin + 3) × Fin (2 ^ fractionBits)

def zeroEncoding (f n : ℕ) : Encoding f n :=
  (false, ⟨0, by omega⟩, ⟨0, by positivity⟩)

instance (f n : ℕ) : Nonempty (Encoding f n) := ⟨zeroEncoding f n⟩

def significand {f n : ℕ} (v : Encoding f n) : ℕ :=
  if v.2.1.val = 0 then v.2.2.val else 2^f + v.2.2.val

def magnitude {f n : ℕ} (delta : ℝ) (v : Encoding f n) : ℝ :=
  (significand v : ℝ) * delta * (2 : ℝ)^(v.2.1.val - 1)

def value {f n : ℕ} (delta : ℝ) (v : Encoding f n) : ℝ :=
  if v.1 then -magnitude delta v else magnitude delta v

def IsNearest {f n : ℕ} (delta x : ℝ) (v : Encoding f n) : Prop :=
  ∀ w : Encoding f n, |value delta v - x| ≤ |value delta w - x|

theorem exists_nearest (f n : ℕ) (delta x : ℝ) :
    ∃ v : Encoding f n, IsNearest delta x v := by
  classical
  obtain ⟨v, _, hv⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Encoding f n)) (fun w => |value delta w - x|)
    Finset.univ_nonempty
  exact ⟨v, fun w => hv w (Finset.mem_univ w)⟩

def nearestEvenEncoding (f n : ℕ) (delta x : ℝ) : Encoding f n := by
  classical
  exact if h : ∃ v : Encoding f n, IsNearest delta x v ∧ significand v % 2 = 0
  then Classical.choose h
  else Classical.choose (exists_nearest f n delta x)

def roundFormat (f n : ℕ) (delta x : ℝ) : ℝ :=
  value delta (nearestEvenEncoding f n delta x)

theorem nearestEven_is_nearest (f n : ℕ) (delta x : ℝ) :
    IsNearest delta x (nearestEvenEncoding f n delta x) := by
  unfold nearestEvenEncoding
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact Classical.choose_spec (exists_nearest f n delta x)

theorem nearestEven_tie_policy (f n : ℕ) (delta x : ℝ)
    (h : ∃ v : Encoding f n, IsNearest delta x v ∧ significand v % 2 = 0) :
    significand (nearestEvenEncoding f n delta x) % 2 = 0 := by
  simp only [nearestEvenEncoding, dif_pos h]
  exact (Classical.choose_spec h).2

theorem roundFormat_le_candidate (f n : ℕ) (delta x : ℝ) (v : Encoding f n) :
    |roundFormat f n delta x - x| ≤ |value delta v - x| :=
  nearestEven_is_nearest f n delta x v

theorem signed_zero_quotient (f n : ℕ) (delta : ℝ) :
    value delta (zeroEncoding f n) = 0 ∧
      value delta (true, (zeroEncoding f n).2) = 0 := by
  simp [value, magnitude, significand, zeroEncoding]

theorem roundFormat_exact {f n : ℕ} (delta : ℝ) (v : Encoding f n) :
    roundFormat f n delta (value delta v) = value delta v := by
  have h := roundFormat_le_candidate f n delta (value delta v) v
  have hz : |roundFormat f n delta (value delta v) - value delta v| = 0 := by
    apply le_antisymm
    · simpa using h
    · exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

#print axioms nearestNat_lower
#print axioms nearestNat_upper
#print axioms nearestNat_error
#print axioms nearestNat_half_even
#print axioms exists_nearest
#print axioms nearestEven_is_nearest
#print axioms nearestEven_tie_policy
#print axioms roundFormat_le_candidate
#print axioms signed_zero_quotient
#print axioms roundFormat_exact
end
end FindOrbRounding
