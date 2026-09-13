import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Copyright 2026. GPL-2.0-or-later.

Kernel-checked mathematical foundations for the source-anchored certificates.
These theorems do not assert that the complete C++ solver implements their
models. Floating-point rounding and step stability appear as explicit premises.
There are no custom axioms, admitted proofs, or native_decide invocations.
-/

namespace FindOrb
noncomputable section
theorem error_trans {a b c e₁ e₂ : ℝ}
    (h₁ : |a - b| ≤ e₁) (h₂ : |b - c| ≤ e₂) : |a - c| ≤ e₁ + e₂ :=
  le_trans (abs_sub_le a b c) (add_le_add h₁ h₂)

theorem add_error {x y rx ry ex ey : ℝ}
    (hx : |rx - x| ≤ ex) (hy : |ry - y| ≤ ey) :
    |(rx + ry) - (x + y)| ≤ ex + ey := by
  calc
    |(rx + ry) - (x + y)| = |(rx - x) + (ry - y)| := by congr 1; ring
    _ ≤ |rx - x| + |ry - y| := abs_add_le _ _
    _ ≤ ex + ey := add_le_add hx hy

theorem sub_error {x y rx ry ex ey : ℝ}
    (hx : |rx - x| ≤ ex) (hy : |ry - y| ≤ ey) :
    |(rx - ry) - (x - y)| ≤ ex + ey := by
  calc
    |(rx - ry) - (x - y)| = |(rx - x) - (ry - y)| := by congr 1; ring
    _ ≤ |rx - x| + |ry - y| := abs_sub _ _
    _ ≤ ex + ey := add_le_add hx hy

theorem mul_error {x y rx ry mx my ex ey : ℝ}
    (hmx : |x| ≤ mx) (hmy : |y| ≤ my)
    (hx : |rx - x| ≤ ex) (hy : |ry - y| ≤ ey) :
    |rx * ry - x * y| ≤ mx * ey + my * ex + ex * ey := by
  have hmx0 : 0 ≤ mx := le_trans (abs_nonneg x) hmx
  have hmy0 : 0 ≤ my := le_trans (abs_nonneg y) hmy
  have hex0 : 0 ≤ ex := le_trans (abs_nonneg (rx - x)) hx
  have h₁ : |x| * |ry - y| ≤ mx * ey :=
    mul_le_mul hmx hy (abs_nonneg _) hmx0
  have h₂ : |y| * |rx - x| ≤ my * ex :=
    mul_le_mul hmy hx (abs_nonneg _) hmy0
  have h₃ : |rx - x| * |ry - y| ≤ ex * ey :=
    mul_le_mul hx hy (abs_nonneg _) hex0
  calc
    |rx * ry - x * y| =
        |(x * (ry - y) + y * (rx - x)) + (rx - x) * (ry - y)| := by
      congr 1; ring
    _ ≤ |x * (ry - y) + y * (rx - x)| + |(rx - x) * (ry - y)| := abs_add_le _ _
    _ ≤ (|x * (ry - y)| + |y * (rx - x)|) + |(rx - x) * (ry - y)| :=
      add_le_add_right (abs_add_le _ _) _
    _ = |x| * |ry - y| + |y| * |rx - x| + |rx - x| * |ry - y| := by simp [abs_mul]
    _ ≤ mx * ey + my * ex + ex * ey := add_le_add (add_le_add h₁ h₂) h₃

theorem rounding_envelope {r z u eta magnitude : ℝ}
    (hu : 0 ≤ u) (hm : |z| ≤ magnitude)
    (hr : |r - z| ≤ u * |z| + eta) : |r - z| ≤ u * magnitude + eta :=
  le_trans hr (add_le_add_right (mul_le_mul_of_nonneg_left hm hu) eta)

theorem rounded_add_error {x y rx ry rounded ex ey rounding : ℝ}
    (hx : |rx - x| ≤ ex) (hy : |ry - y| ≤ ey)
    (hr : |rounded - (rx + ry)| ≤ rounding) :
    |rounded - (x + y)| ≤ rounding + (ex + ey) :=
  error_trans hr (add_error hx hy)

theorem rounded_mul_error {x y rx ry rounded mx my ex ey rounding : ℝ}
    (hmx : |x| ≤ mx) (hmy : |y| ≤ my)
    (hx : |rx - x| ≤ ex) (hy : |ry - y| ≤ ey)
    (hr : |rounded - (rx * ry)| ≤ rounding) :
    |rounded - x * y| ≤ rounding + (mx * ey + my * ex + ex * ey) :=
  error_trans hr (mul_error hmx hmy hx hy)

def errorBudget (a b e₀ : ℝ) : Nat → ℝ
  | 0 => e₀
  | n + 1 => a * errorBudget a b e₀ n + b

theorem global_error_bound (error : Nat → ℝ) {a b e₀ : ℝ}
    (ha : 0 ≤ a) (initial : error 0 ≤ e₀)
    (step : ∀ n, error (n + 1) ≤ a * error n + b) :
    ∀ n, error n ≤ errorBudget a b e₀ n := by
  intro n
  induction n with
  | zero => exact initial
  | succ n ih =>
    exact le_trans (step n) (add_le_add_right (mul_le_mul_of_nonneg_left ih ha) b)

theorem error_budget_nonnegative {a b e₀ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e₀) (n : Nat) :
    0 ≤ errorBudget a b e₀ n := by
  induction n with
  | zero => exact he
  | succ n ih => exact add_nonneg (mul_nonneg ha ih) hb

theorem error_budget_geometric (a b e₀ : ℝ) (n : Nat) :
    (a - 1) * errorBudget a b e₀ n =
      (a - 1) * a^n * e₀ + b * (a^n - 1) := by
  induction n with
  | zero => simp [errorBudget]
  | succ n ih =>
    simp only [errorBudget, pow_succ]
    calc
      (a - 1) * (a * errorBudget a b e₀ n + b) =
          a * ((a - 1) * errorBudget a b e₀ n) + (a - 1) * b := by ring
      _ = a * ((a - 1) * a^n * e₀ + b * (a^n - 1)) + (a - 1) * b := by rw [ih]
      _ = (a - 1) * (a^n * a) * e₀ + b * (a^n * a - 1) := by ring

theorem error_budget_unit (b e₀ : ℝ) (n : Nat) :
    errorBudget 1 b e₀ n = e₀ + (n : ℝ) * b := by
  induction n with
  | zero => simp [errorBudget]
  | succ n ih => simp [errorBudget, ih, Nat.cast_add]; ring

end
end FindOrb

#print axioms FindOrb.error_trans
#print axioms FindOrb.add_error
#print axioms FindOrb.sub_error
#print axioms FindOrb.mul_error
#print axioms FindOrb.rounding_envelope
#print axioms FindOrb.rounded_add_error
#print axioms FindOrb.rounded_mul_error
#print axioms FindOrb.global_error_bound
#print axioms FindOrb.error_budget_nonnegative
#print axioms FindOrb.error_budget_geometric
#print axioms FindOrb.error_budget_unit
