import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/-! GPL-2.0-or-later. Exact semantics of the source interp recurrences.
The error certificates handle floating-point arithmetic separately.
-/
namespace FindOrbEphemeris
open Polynomial
noncomputable section

def position : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (2 * X) * position (n + 1) - position n

def velocity : ℕ → ℚ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => (2 * X) * velocity (n + 1) + position (n + 1) + position (n + 1) - velocity n

def acceleration : ℕ → ℚ[X]
  | 0 => 0
  | 1 => 0
  | n + 2 => 4 * velocity (n + 1) + (2 * X) * acceleration (n + 1) - acceleration n

theorem position_derivative (n : ℕ) : derivative (position n) = velocity n := by
  have both : ∀ m, derivative (position m) = velocity m ∧
      derivative (position (m + 1)) = velocity (m + 1) := by
    intro m
    induction m with
    | zero => simp [position, velocity]
    | succ m ih =>
      constructor
      · exact ih.2
      · simp [position, velocity, derivative_mul, ih.1, ih.2]
        ring
  exact (both n).1

theorem velocity_derivative (n : ℕ) : derivative (velocity n) = acceleration n := by
  have both : ∀ m, derivative (velocity m) = acceleration m ∧
      derivative (velocity (m + 1)) = acceleration (m + 1) := by
    intro m
    induction m with
    | zero => simp [velocity, acceleration]
    | succ m ih =>
      constructor
      · exact ih.2
      · simp [velocity, acceleration, derivative_mul, position_derivative, ih.1, ih.2]
        ring
  exact (both n).1

theorem position_second_derivative (n : ℕ) :
    derivative (derivative (position n)) = acceleration n := by
  rw [position_derivative, velocity_derivative]

/- The same arithmetic scale in the implementation gives the chain-rule
factors for a constant subinterval length: d/dt = scale * d/dx. -/
theorem linear_combination_derivative (c : Fin 17 → ℚ) :
    derivative (∑ k : Fin 17, C (c k) * position k.val) =
      ∑ k : Fin 17, C (c k) * velocity k.val := by
  simp [derivative_mul, position_derivative]

theorem position_affine_time_derivative (n : ℕ) (scale offset : ℚ) :
    derivative ((position n).comp (C scale * X + C offset)) =
      C scale * (velocity n).comp (C scale * X + C offset) := by
  simp [derivative_comp, position_derivative, derivative_mul]

theorem velocity_affine_time_derivative (n : ℕ) (scale offset : ℚ) :
    derivative ((velocity n).comp (C scale * X + C offset)) =
      C scale * (acceleration n).comp (C scale * X + C offset) := by
  simp [derivative_comp, velocity_derivative, derivative_mul]

theorem position_affine_time_second_derivative (n : ℕ) (scale offset : ℚ) :
    derivative (derivative ((position n).comp (C scale * X + C offset))) =
      (C scale * (acceleration n).comp (C scale * X + C offset)) * C scale := by
  rw [position_affine_time_derivative]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add,
    velocity_affine_time_derivative]
  ring

#print axioms position_derivative
#print axioms velocity_derivative
#print axioms position_second_derivative
#print axioms linear_combination_derivative
#print axioms position_affine_time_derivative
#print axioms velocity_affine_time_derivative
#print axioms position_affine_time_second_derivative
end
end FindOrbEphemeris
