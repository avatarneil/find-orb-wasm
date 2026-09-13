import Foundations
import Roundoff

/- GPL-2.0-or-later. Conditional real model of one bounded rounding operation. -/
namespace FindOrbEphemerisBridge
noncomputable section

def RoundingModel (rnd : ℝ → ℝ) : Prop :=
  ∀ z, |z| < (2 : ℝ)^1023 →
    |rnd z - z| ≤ (1 : ℝ) / 2^53 * |z| + (1 : ℝ) / 2^100

theorem rounded_step (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    {z exact magnitude propagation error : ℝ}
    (hp : |z - exact| ≤ propagation)
    (hm : |exact| ≤ magnitude)
    (hsafe : magnitude + propagation < (2 : ℝ)^1023)
    (hbudget : propagation + (1 : ℝ) / 2^53 * (magnitude + propagation) +
      (1 : ℝ) / 2^100 ≤ error) :
    |rnd z - exact| ≤ error := by
  have hz : |z| ≤ magnitude + propagation := by
    calc
      |z| = |exact + (z - exact)| := by congr 1; ring
      _ ≤ |exact| + |z - exact| := abs_add_le _ _
      _ ≤ magnitude + propagation := add_le_add hm hp
  have round := FindOrb.rounding_envelope (by positivity : (0 : ℝ) ≤ 1 / 2^53)
    hz (hrnd z (lt_of_le_of_lt hz hsafe))
  have composed := FindOrb.error_trans round hp
  exact le_trans composed (by linarith)

#print axioms rounded_step
end
end FindOrbEphemerisBridge
