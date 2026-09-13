import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-! GPL-2.0-or-later. Universal polynomial magnitude bound used by the exact
node certificates. Root Foundations.lean supplies the generic arithmetic
error-composition lemmas; actual IEEE/source correspondence remains explicit.
-/
namespace FindOrbEphemeris

noncomputable def evalCoefficients : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => c + x * evalCoefficients cs x

theorem polynomial_l1_bound (cs : List ℝ) (x : ℝ) (hx : |x| ≤ 1) :
    |evalCoefficients cs x| ≤ (cs.map abs).sum := by
  induction cs with
  | nil => simp [evalCoefficients]
  | cons c cs ih =>
    have product : |x| * |evalCoefficients cs x| ≤ 1 * (cs.map abs).sum :=
      mul_le_mul hx ih (abs_nonneg _) (by norm_num)
    simp only [evalCoefficients, List.map_cons, List.sum_cons]
    calc
      |c + x * evalCoefficients cs x| ≤ |c| + |x * evalCoefficients cs x| := abs_add_le _ _
      _ = |c| + |x| * |evalCoefficients cs x| := by rw [abs_mul]
      _ ≤ |c| + (cs.map abs).sum := by simpa using add_le_add_left product |c|

#print axioms polynomial_l1_bound
end FindOrbEphemeris
