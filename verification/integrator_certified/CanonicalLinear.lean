import RKFLinear
import PDLinear
import IEEEBounds

/- GPL-2.0-or-later. Instantiate the complete source-ordered step graph with
the explicitly defined finite binary128 nearest-rounding model. No premise
postulates that model's arithmetic error bound. C++/WASM correspondence and
the chosen RHS/reference/buffer preconditions remain separate boundaries. -/
namespace FindOrbLinear
noncomputable section

theorem binary128_rounding_model : RoundingModel FindOrbRounding.roundBinary128 := by
  intro z hz
  exact FindOrbRounding.binary128_bounded_error z hz

theorem fehlberg_binary128_local (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |RKFLinear.step FindOrbRounding.roundBinary128 h y - y * Real.exp h| ≤
      (43/4000000000000 : ℝ) :=
  RKFLinear.local_error _ binary128_rounding_model h y hh hy

theorem pd_binary128_local (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |PDLinear.step FindOrbRounding.roundBinary128 h y - y * Real.exp h| ≤
      (579/200000000000000000000 : ℝ) :=
  PDLinear.local_error _ binary128_rounding_model h y hh hy

theorem fehlberg_binary128_multiple_steps (values steps : Nat → ℝ) (initial initialError : ℝ)
    (hstep : ∀ n, |steps n| ≤ 1/16) (hstate : ∀ n, |values n| ≤ 1/2)
    (hrec : ∀ n, values (n+1) = RKFLinear.step FindOrbRounding.roundBinary128 (steps n) (values n))
    (hzero : |values 0 - initial| ≤ initialError) :
    ∀ n, |values n - initial * Real.exp (elapsedTime steps n)| ≤
      FindOrb.errorBudget (16/15) (43/4000000000000 : ℝ) initialError n :=
  RKFLinear.multiple_steps _ binary128_rounding_model values steps initial initialError
    hstep hstate hrec hzero

theorem pd_binary128_multiple_steps (values steps : Nat → ℝ) (initial initialError : ℝ)
    (hstep : ∀ n, |steps n| ≤ 1/16) (hstate : ∀ n, |values n| ≤ 1/2)
    (hrec : ∀ n, values (n+1) = PDLinear.step FindOrbRounding.roundBinary128 (steps n) (values n))
    (hzero : |values 0 - initial| ≤ initialError) :
    ∀ n, |values n - initial * Real.exp (elapsedTime steps n)| ≤
      FindOrb.errorBudget (16/15) (579/200000000000000000000 : ℝ) initialError n :=
  PDLinear.multiple_steps _ binary128_rounding_model values steps initial initialError
    hstep hstate hrec hzero

#print axioms binary128_rounding_model
#print axioms fehlberg_binary128_local
#print axioms pd_binary128_local
#print axioms fehlberg_binary128_multiple_steps
#print axioms pd_binary128_multiple_steps
end
end FindOrbLinear
