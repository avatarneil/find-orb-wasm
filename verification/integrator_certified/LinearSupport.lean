import Foundations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity

/- GPL-2.0-or-later. Connected bounds for a source-ordered scalar RK graph.
The explicit rounding premise is kept separate from C++/WASM correspondence. -/
namespace FindOrbLinear
noncomputable section

def RoundingModel (rnd : ℝ → ℝ) : Prop :=
  ∀ z, |z| < 100 → |rnd z - z| ≤ (1 : ℝ) / 2^113 * |z| + (1 : ℝ) / 2^200

theorem rounded_step (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    {z exact magnitude propagation error : ℝ}
    (hp : |z - exact| ≤ propagation) (hm : |exact| ≤ magnitude)
    (hsafe : magnitude + propagation < 100)
    (hbudget : propagation + (1 : ℝ) / 2^113 * (magnitude + propagation) +
      (1 : ℝ) / 2^200 ≤ error) :
    |rnd z - exact| ≤ error := by
  have hz : |z| ≤ magnitude + propagation := by
    calc
      |z| = |exact + (z - exact)| := by congr 1; ring
      _ ≤ |exact| + |z - exact| := abs_add_le _ _
      _ ≤ magnitude + propagation := add_le_add hm hp
  have round := FindOrb.rounding_envelope (by positivity : (0 : ℝ) ≤ 1 / 2^113)
    hz (hrnd z (lt_of_le_of_lt hz hsafe))
  exact le_trans (FindOrb.error_trans round hp) (by linarith)

-- A bivariate monomial list, sufficient for the source graph in h and y0.
abbrev Terms := List (ℝ × Nat × Nat)
def evaluate : Terms → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | (a, i, j) :: xs, h, y => a * h^i * y^j + evaluate xs h y
def magnitude : Terms → ℝ
  | [] => 0
  | (a, i, j) :: xs => |a| * (1/16)^i * (1/2)^j + magnitude xs

theorem evaluate_bound (terms : Terms) (h y : ℝ)
    (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |evaluate terms h y| ≤ magnitude terms := by
  induction terms with
  | nil => simp [evaluate, magnitude]
  | cons a xs ih =>
    obtain ⟨a, i, j⟩ := a
    have hi : |h|^i ≤ (1/16 : ℝ)^i := pow_le_pow_left₀ (abs_nonneg h) hh i
    have hj : |y|^j ≤ (1/2 : ℝ)^j := pow_le_pow_left₀ (abs_nonneg y) hy j
    have hm : |a * h^i * y^j| ≤ |a| * (1/16 : ℝ)^i * (1/2 : ℝ)^j := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hi (abs_nonneg a)) hj
        (pow_nonneg (abs_nonneg y) _) (by positivity)
    exact le_trans (abs_add_le _ _) (add_le_add hm ih)

theorem exp_taylor_bound (h : ℝ) (hh : |h| ≤ 1/16) :
    |Real.exp h - ∑ m ∈ Finset.range 16, h^m / m.factorial| ≤
      (1/16 : ℝ)^16 * (17 / ((16 : Nat).factorial * 16)) := by
  have h1 : |h| ≤ 1 := le_trans hh (by norm_num)
  have hexp := Real.exp_bound h1 (by norm_num : 0 < (16 : Nat))
  exact le_trans hexp (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg h) hh 16) (by positivity))

theorem solution_derivative (y t : ℝ) :
    HasDerivAt (fun s : ℝ => y * Real.exp s) (y * Real.exp t) t := by
  exact (Real.hasDerivAt_exp t).const_mul y

theorem solution_initial (y : ℝ) : y * Real.exp 0 = y := by simp

theorem exp_small_bound (h : ℝ) (hh : |h| ≤ 1/16) : |Real.exp h| ≤ 16/15 := by
  rw [abs_of_pos (Real.exp_pos h)]
  have hle : h ≤ (1/16 : ℝ) := le_trans (le_abs_self h) hh
  exact le_trans (Real.exp_le_exp.mpr hle)
    (by convert Real.exp_bound_div_one_sub_of_interval
          (by norm_num : (0 : ℝ) ≤ 1/16) (by norm_num : (1/16 : ℝ) < 1) using 1 <;> norm_num)

theorem accumulated_step {out current exact h localError : ℝ}
    (hh : |h| ≤ 1/16) (hl : |out - current * Real.exp h| ≤ localError) :
    |out - exact * Real.exp h| ≤ (16/15) * |current - exact| + localError := by
  have stability : |current * Real.exp h - exact * Real.exp h| ≤
      (16/15) * |current - exact| := by
    rw [← sub_mul, abs_mul]
    have bound := mul_le_mul_of_nonneg_left (exp_small_bound h hh) (abs_nonneg (current-exact))
    simpa [mul_comm] using bound
  exact le_trans (FindOrb.error_trans hl stability) (by linarith)

def elapsedTime (steps : Nat → ℝ) : Nat → ℝ
  | 0 => 0
  | n+1 => elapsedTime steps n + steps n

theorem sampled_solution_step (initial : ℝ) (steps : Nat → ℝ) (n : Nat) :
    initial * Real.exp (elapsedTime steps (n+1)) =
      (initial * Real.exp (elapsedTime steps n)) * Real.exp (steps n) := by
  simp only [elapsedTime, Real.exp_add]
  ring

#print axioms rounded_step
#print axioms evaluate_bound
#print axioms exp_taylor_bound
#print axioms solution_derivative
#print axioms solution_initial
#print axioms exp_small_bound
#print axioms accumulated_step
#print axioms sampled_solution_step
end
end FindOrbLinear
