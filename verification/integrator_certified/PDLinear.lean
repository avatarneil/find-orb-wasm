import LinearSupport
/- GPL-2.0-or-later. Generated connected proof; see generate.py. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
set_option linter.unusedVariables false
namespace FindOrbLinear
noncomputable section
namespace PDLinear
def exact0 (h y : ℝ) : ℝ := h
def rounded0 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := h
theorem polynomial0 (h y : ℝ) : exact0 h y = evaluate [((1/1 : ℝ), 1, 0)] h y := by
  simp only [exact0, evaluate] <;> ring
theorem bound0 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact0 h y| ≤ (1/16 : ℝ) := by
  rw [polynomial0]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error0 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded0 rnd h y - exact0 h y| ≤ (0/1 : ℝ) := by
  simp [rounded0, exact0]
def exact1 (h y : ℝ) : ℝ := y
def rounded1 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := y
theorem polynomial1 (h y : ℝ) : exact1 h y = evaluate [((1/1 : ℝ), 0, 1)] h y := by
  simp only [exact1, evaluate] <;> ring
theorem bound1 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact1 h y| ≤ (1/2 : ℝ) := by
  rw [polynomial1]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error1 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded1 rnd h y - exact1 h y| ≤ (0/1 : ℝ) := by
  simp [rounded1, exact1]
def exact2 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded2 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial2 (h y : ℝ) : exact2 h y = evaluate [] h y := by
  simp only [exact2, evaluate] <;> ring
theorem bound2 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact2 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial2]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error2 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded2 rnd h y - exact2 h y| ≤ (0/1 : ℝ) := by
  simp [rounded2, exact2]
def exact3 (h y : ℝ) : ℝ := exact1 h y + exact2 h y
def rounded3 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded1 rnd h y + rounded2 rnd h y)
theorem polynomial3 (h y : ℝ) : exact3 h y = evaluate [((1/1 : ℝ), 0, 1)] h y := by
  simp only [exact3, polynomial1, polynomial2, evaluate] <;> ring
theorem bound3 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact3 h y| ≤ (1/2 : ℝ) := by
  rw [polynomial3]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error3 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded3 rnd h y - exact3 h y| ≤ (75557863725914323419137/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded3 exact3
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (1/2 : ℝ))
  · convert FindOrb.add_error (error1 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound3 h y hh hy
  · norm_num
  · norm_num
def exact4 (h y : ℝ) : ℝ := exact1 h y + exact2 h y
def rounded4 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded1 rnd h y + rounded2 rnd h y)
theorem polynomial4 (h y : ℝ) : exact4 h y = evaluate [((1/1 : ℝ), 0, 1)] h y := by
  simp only [exact4, polynomial1, polynomial2, evaluate] <;> ring
theorem bound4 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact4 h y| ≤ (1/2 : ℝ) := by
  rw [polynomial4]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error4 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded4 rnd h y - exact4 h y| ≤ (75557863725914323419137/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded4 exact4
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (1/2 : ℝ))
  · convert FindOrb.add_error (error1 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound4 h y hh hy
  · norm_num
  · norm_num
def exact5 (h y : ℝ) : ℝ := (2001599834386887/36028797018963968 : ℝ)
def rounded5 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (2001599834386887/36028797018963968 : ℝ)
theorem polynomial5 (h y : ℝ) : exact5 h y = evaluate [((2001599834386887/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact5, evaluate] <;> ring
theorem bound5 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact5 h y| ≤ (61083979321/1099511627776 : ℝ) := by
  rw [polynomial5]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error5 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded5 rnd h y - exact5 h y| ≤ (0/1 : ℝ) := by
  simp [rounded5, exact5]
def exact6 (h y : ℝ) : ℝ := exact5 h y * exact4 h y
def rounded6 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded5 rnd h y * rounded4 rnd h y)
theorem polynomial6 (h y : ℝ) : exact6 h y = evaluate [((2001599834386887/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact6, polynomial5, polynomial4, evaluate] <;> ring
theorem bound6 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact6 h y| ≤ (30541989661/1099511627776 : ℝ) := by
  rw [polynomial6]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error6 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded6 rnd h y - exact6 h y| ≤ (8395318191852248629249/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded6 exact6
  apply rounded_step rnd hrnd (propagation := (4615374985372686543552270523665977/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (30541989661/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound5 h y hh hy) (bound4 h y hh hy)
      (error5 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound6 h y hh hy
  · norm_num
  · norm_num
def exact7 (h y : ℝ) : ℝ := exact2 h y + exact6 h y
def rounded7 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded6 rnd h y)
theorem polynomial7 (h y : ℝ) : exact7 h y = evaluate [((2001599834386887/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact7, polynomial2, polynomial6, evaluate] <;> ring
theorem bound7 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact7 h y| ≤ (30541989661/1099511627776 : ℝ) := by
  rw [polynomial7]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error7 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded7 rnd h y - exact7 h y| ≤ (6296488643906366341121/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded7 exact7
  apply rounded_step rnd hrnd (propagation := (8395318191852248629249/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (30541989661/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error6 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound7 h y hh hy
  · norm_num
  · norm_num
def exact8 (h y : ℝ) : ℝ := exact7 h y * exact0 h y
def rounded8 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded7 rnd h y * rounded0 rnd h y)
theorem polynomial8 (h y : ℝ) : exact8 h y = evaluate [((2001599834386887/36028797018963968 : ℝ), 1, 1)] h y := by
  simp only [exact8, polynomial7, polynomial0, evaluate] <;> ring
theorem bound8 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact8 h y| ≤ (954437177/549755813888 : ℝ) := by
  rw [polynomial8]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error8 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded8 rnd h y - exact8 h y| ≤ (1049414774011595849729/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded8 exact8
  apply rounded_step rnd hrnd (propagation := (6296488643906366341121/12554203470773361527671578846415332832204710888928069025792 : ℝ)) (magnitude := (954437177/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound7 h y hh hy) (bound0 h y hh hy)
      (error7 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound8 h y hh hy
  · norm_num
  · norm_num
def exact9 (h y : ℝ) : ℝ := exact8 h y + exact3 h y
def rounded9 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded8 rnd h y + rounded3 rnd h y)
theorem polynomial9 (h y : ℝ) : exact9 h y = evaluate [((1/1 : ℝ), 0, 1), ((2001599834386887/36028797018963968 : ℝ), 1, 1)] h y := by
  simp only [exact9, polynomial8, polynomial3, evaluate] <;> ring
theorem bound9 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact9 h y| ≤ (275832344121/549755813888 : ℝ) := by
  rw [polynomial9]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error9 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded9 rnd h y - exact9 h y| ≤ (152427495919363542745091/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded9 exact9
  apply rounded_step rnd hrnd (propagation := (38303639249962959634433/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (275832344121/549755813888 : ℝ))
  · convert FindOrb.add_error (error8 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound9 h y hh hy
  · norm_num
  · norm_num
def exact10 (h y : ℝ) : ℝ := exact9 h y + exact2 h y
def rounded10 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded9 rnd h y + rounded2 rnd h y)
theorem polynomial10 (h y : ℝ) : exact10 h y = evaluate [((1/1 : ℝ), 0, 1), ((2001599834386887/36028797018963968 : ℝ), 1, 1)] h y := by
  simp only [exact10, polynomial9, polynomial2, evaluate] <;> ring
theorem bound10 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact10 h y| ≤ (275832344121/549755813888 : ℝ) := by
  rw [polynomial10]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error10 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded10 rnd h y - exact10 h y| ≤ (57061928334700291555329/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded10 exact10
  apply rounded_step rnd hrnd (propagation := (152427495919363542745091/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (275832344121/549755813888 : ℝ))
  · convert FindOrb.add_error (error9 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound10 h y hh hy
  · norm_num
  · norm_num
def exact11 (h y : ℝ) : ℝ := exact10 h y + exact2 h y
def rounded11 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded10 rnd h y + rounded2 rnd h y)
theorem polynomial11 (h y : ℝ) : exact11 h y = evaluate [((1/1 : ℝ), 0, 1), ((2001599834386887/36028797018963968 : ℝ), 1, 1)] h y := by
  simp only [exact11, polynomial10, polynomial2, evaluate] <;> ring
theorem bound11 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact11 h y| ≤ (275832344121/549755813888 : ℝ) := by
  rw [polynomial11]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error11 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded11 rnd h y - exact11 h y| ≤ (304067930758238789697541/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded11 exact11
  apply rounded_step rnd hrnd (propagation := (57061928334700291555329/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (275832344121/549755813888 : ℝ))
  · convert FindOrb.add_error (error10 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound11 h y hh hy
  · norm_num
  · norm_num
def exact12 (h y : ℝ) : ℝ := (6004799503160661/288230376151711744 : ℝ)
def rounded12 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (6004799503160661/288230376151711744 : ℝ)
theorem polynomial12 (h y : ℝ) : exact12 h y = evaluate [((6004799503160661/288230376151711744 : ℝ), 0, 0)] h y := by
  simp only [exact12, evaluate] <;> ring
theorem bound12 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact12 h y| ≤ (11453246123/549755813888 : ℝ) := by
  rw [polynomial12]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error12 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded12 rnd h y - exact12 h y| ≤ (0/1 : ℝ) := by
  simp [rounded12, exact12]
def exact13 (h y : ℝ) : ℝ := exact12 h y * exact4 h y
def rounded13 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded12 rnd h y * rounded4 rnd h y)
theorem polynomial13 (h y : ℝ) : exact13 h y = evaluate [((6004799503160661/288230376151711744 : ℝ), 0, 1)] h y := by
  simp only [exact13, polynomial12, polynomial4, evaluate] <;> ring
theorem bound13 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact13 h y| ≤ (11453246123/1099511627776 : ℝ) := by
  rw [polynomial13]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error13 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded13 rnd h y - exact13 h y| ≤ (3148244322004722778113/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded13 exact13
  apply rounded_step rnd hrnd (propagation := (865382809780990559330398949255851/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (11453246123/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound12 h y hh hy) (bound4 h y hh hy)
      (error12 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound13 h y hh hy
  · norm_num
  · norm_num
def exact14 (h y : ℝ) : ℝ := exact2 h y + exact13 h y
def rounded14 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded13 rnd h y)
theorem polynomial14 (h y : ℝ) : exact14 h y = evaluate [((6004799503160661/288230376151711744 : ℝ), 0, 1)] h y := by
  simp only [exact14, polynomial2, polynomial13, evaluate] <;> ring
theorem bound14 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact14 h y| ≤ (11453246123/1099511627776 : ℝ) := by
  rw [polynomial14]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error14 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded14 rnd h y - exact14 h y| ≤ (2361183241503542083585/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded14 exact14
  apply rounded_step rnd hrnd (propagation := (3148244322004722778113/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (11453246123/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error13 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound14 h y hh hy
  · norm_num
  · norm_num
def exact15 (h y : ℝ) : ℝ := (1/16 : ℝ)
def rounded15 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1/16 : ℝ)
theorem polynomial15 (h y : ℝ) : exact15 h y = evaluate [((1/16 : ℝ), 0, 0)] h y := by
  simp only [exact15, evaluate] <;> ring
theorem bound15 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact15 h y| ≤ (1/16 : ℝ) := by
  rw [polynomial15]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error15 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded15 rnd h y - exact15 h y| ≤ (0/1 : ℝ) := by
  simp [rounded15, exact15]
def exact16 (h y : ℝ) : ℝ := exact15 h y * exact11 h y
def rounded16 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded15 rnd h y * rounded11 rnd h y)
theorem polynomial16 (h y : ℝ) : exact16 h y = evaluate [((1/16 : ℝ), 0, 1), ((2001599834386887/576460752303423488 : ℝ), 1, 1)] h y := by
  simp only [exact16, polynomial15, polynomial11, evaluate] <;> ring
theorem bound16 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact16 h y| ≤ (4309880377/137438953472 : ℝ) := by
  rw [polynomial16]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error16 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded16 rnd h y - exact16 h y| ≤ (23743009261225034907649/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded16 exact16
  apply rounded_step rnd hrnd (propagation := (304067930758238789697541/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (4309880377/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound15 h y hh hy) (bound11 h y hh hy)
      (error15 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound16 h y hh hy
  · norm_num
  · norm_num
def exact17 (h y : ℝ) : ℝ := exact14 h y + exact16 h y
def rounded17 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded14 rnd h y + rounded16 rnd h y)
theorem polynomial17 (h y : ℝ) : exact17 h y = evaluate [((24019198012642645/288230376151711744 : ℝ), 0, 1), ((2001599834386887/576460752303423488 : ℝ), 1, 1)] h y := by
  simp only [exact17, polynomial14, polynomial16, evaluate] <;> ring
theorem bound17 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact17 h y| ≤ (22966144569/549755813888 : ℝ) := by
  rw [polynomial17]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error17 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded17 rnd h y - exact17 h y| ≤ (8694565373483038015489/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded17 exact17
  apply rounded_step rnd hrnd (propagation := (28465375744232119074819/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (22966144569/549755813888 : ℝ))
  · convert FindOrb.add_error (error14 rnd hrnd h y hh hy) (error16 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound17 h y hh hy
  · norm_num
  · norm_num
def exact18 (h y : ℝ) : ℝ := exact17 h y * exact0 h y
def rounded18 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded17 rnd h y * rounded0 rnd h y)
theorem polynomial18 (h y : ℝ) : exact18 h y = evaluate [((24019198012642645/288230376151711744 : ℝ), 1, 1), ((2001599834386887/576460752303423488 : ℝ), 2, 1)] h y := by
  simp only [exact18, polynomial17, polynomial0, evaluate] <;> ring
theorem bound18 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact18 h y| ≤ (358846009/137438953472 : ℝ) := by
  rw [polynomial18]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error18 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded18 rnd h y - exact18 h y| ≤ (2568196702847270649857/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded18 exact18
  apply rounded_step rnd hrnd (propagation := (8694565373483038015489/6277101735386680763835789423207666416102355444464034512896 : ℝ)) (magnitude := (358846009/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound17 h y hh hy) (bound0 h y hh hy)
      (error17 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound18 h y hh hy
  · norm_num
  · norm_num
def exact19 (h y : ℝ) : ℝ := exact18 h y + exact3 h y
def rounded19 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded18 rnd h y + rounded3 rnd h y)
theorem polynomial19 (h y : ℝ) : exact19 h y = evaluate [((1/1 : ℝ), 0, 1), ((24019198012642645/288230376151711744 : ℝ), 1, 1), ((2001599834386887/576460752303423488 : ℝ), 2, 1)] h y := by
  simp only [exact19, polynomial18, polynomial3, evaluate] <;> ring
theorem bound19 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact19 h y| ≤ (69078322745/137438953472 : ℝ) := by
  rw [polynomial19]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error19 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded19 rnd h y - exact19 h y| ≤ (154078479514152428634115/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded19 exact19
  apply rounded_step rnd hrnd (propagation := (39063030214380797034497/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (69078322745/137438953472 : ℝ))
  · convert FindOrb.add_error (error18 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound19 h y hh hy
  · norm_num
  · norm_num
def exact20 (h y : ℝ) : ℝ := exact19 h y + exact2 h y
def rounded20 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded19 rnd h y + rounded2 rnd h y)
theorem polynomial20 (h y : ℝ) : exact20 h y = evaluate [((1/1 : ℝ), 0, 1), ((24019198012642645/288230376151711744 : ℝ), 1, 1), ((2001599834386887/576460752303423488 : ℝ), 2, 1)] h y := by
  simp only [exact20, polynomial19, polynomial2, evaluate] <;> ring
theorem bound20 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact20 h y| ≤ (69078322745/137438953472 : ℝ) := by
  rw [polynomial20]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error20 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded20 rnd h y - exact20 h y| ≤ (57507724649885815799809/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded20 exact20
  apply rounded_step rnd hrnd (propagation := (154078479514152428634115/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (69078322745/137438953472 : ℝ))
  · convert FindOrb.add_error (error19 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound20 h y hh hy
  · norm_num
  · norm_num
def exact21 (h y : ℝ) : ℝ := exact20 h y + exact2 h y
def rounded21 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded20 rnd h y + rounded2 rnd h y)
theorem polynomial21 (h y : ℝ) : exact21 h y = evaluate [((1/1 : ℝ), 0, 1), ((24019198012642645/288230376151711744 : ℝ), 1, 1), ((2001599834386887/576460752303423488 : ℝ), 2, 1)] h y := by
  simp only [exact21, polynomial20, polynomial2, evaluate] <;> ring
theorem bound21 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact21 h y| ≤ (69078322745/137438953472 : ℝ) := by
  rw [polynomial21]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error21 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded21 rnd h y - exact21 h y| ≤ (305983317684934097764357/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded21 exact21
  apply rounded_step rnd hrnd (propagation := (57507724649885815799809/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (69078322745/137438953472 : ℝ))
  · convert FindOrb.add_error (error20 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound21 h y hh hy
  · norm_num
  · norm_num
def exact22 (h y : ℝ) : ℝ := (1/32 : ℝ)
def rounded22 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1/32 : ℝ)
theorem polynomial22 (h y : ℝ) : exact22 h y = evaluate [((1/32 : ℝ), 0, 0)] h y := by
  simp only [exact22, evaluate] <;> ring
theorem bound22 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact22 h y| ≤ (1/32 : ℝ) := by
  rw [polynomial22]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error22 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded22 rnd h y - exact22 h y| ≤ (0/1 : ℝ) := by
  simp [rounded22, exact22]
def exact23 (h y : ℝ) : ℝ := exact22 h y * exact4 h y
def rounded23 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded22 rnd h y * rounded4 rnd h y)
theorem polynomial23 (h y : ℝ) : exact23 h y = evaluate [((1/32 : ℝ), 0, 1)] h y := by
  simp only [exact23, polynomial22, polynomial4, evaluate] <;> ring
theorem bound23 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact23 h y| ≤ (1/64 : ℝ) := by
  rw [polynomial23]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error23 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded23 rnd h y - exact23 h y| ≤ (4722366482869645213697/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded23 exact23
  apply rounded_step rnd hrnd (propagation := (75557863725914323419137/50216813883093446110686315385661331328818843555712276103168 : ℝ)) (magnitude := (1/64 : ℝ))
  · convert FindOrb.mul_error (bound22 h y hh hy) (bound4 h y hh hy)
      (error22 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound23 h y hh hy
  · norm_num
  · norm_num
def exact24 (h y : ℝ) : ℝ := exact2 h y + exact23 h y
def rounded24 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded23 rnd h y)
theorem polynomial24 (h y : ℝ) : exact24 h y = evaluate [((1/32 : ℝ), 0, 1)] h y := by
  simp only [exact24, polynomial2, polynomial23, evaluate] <;> ring
theorem bound24 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact24 h y| ≤ (1/64 : ℝ) := by
  rw [polynomial24]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error24 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded24 rnd h y - exact24 h y| ≤ (3541774862152233910273/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded24 exact24
  apply rounded_step rnd hrnd (propagation := (4722366482869645213697/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (1/64 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error23 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound24 h y hh hy
  · norm_num
  · norm_num
def exact25 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded25 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial25 (h y : ℝ) : exact25 h y = evaluate [] h y := by
  simp only [exact25, evaluate] <;> ring
theorem bound25 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact25 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial25]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error25 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded25 rnd h y - exact25 h y| ≤ (0/1 : ℝ) := by
  simp [rounded25, exact25]
def exact26 (h y : ℝ) : ℝ := exact25 h y * exact11 h y
def rounded26 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded25 rnd h y * rounded11 rnd h y)
theorem polynomial26 (h y : ℝ) : exact26 h y = evaluate [] h y := by
  simp only [exact26, polynomial25, polynomial11, evaluate] <;> ring
theorem bound26 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact26 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial26]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error26 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded26 rnd h y - exact26 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded26 exact26
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound25 h y hh hy) (bound11 h y hh hy)
      (error25 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound26 h y hh hy
  · norm_num
  · norm_num
def exact27 (h y : ℝ) : ℝ := exact24 h y + exact26 h y
def rounded27 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded24 rnd h y + rounded26 rnd h y)
theorem polynomial27 (h y : ℝ) : exact27 h y = evaluate [((1/32 : ℝ), 0, 1)] h y := by
  simp only [exact27, polynomial24, polynomial26, evaluate] <;> ring
theorem bound27 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact27 h y| ≤ (1/64 : ℝ) := by
  rw [polynomial27]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error27 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded27 rnd h y - exact27 h y| ≤ (2361183241434822606849/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded27 exact27
  apply rounded_step rnd hrnd (propagation := (7083549724304467820547/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (1/64 : ℝ))
  · convert FindOrb.add_error (error24 rnd hrnd h y hh hy) (error26 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound27 h y hh hy
  · norm_num
  · norm_num
def exact28 (h y : ℝ) : ℝ := (3/32 : ℝ)
def rounded28 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (3/32 : ℝ)
theorem polynomial28 (h y : ℝ) : exact28 h y = evaluate [((3/32 : ℝ), 0, 0)] h y := by
  simp only [exact28, evaluate] <;> ring
theorem bound28 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact28 h y| ≤ (3/32 : ℝ) := by
  rw [polynomial28]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error28 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded28 rnd h y - exact28 h y| ≤ (0/1 : ℝ) := by
  simp [rounded28, exact28]
def exact29 (h y : ℝ) : ℝ := exact28 h y * exact21 h y
def rounded29 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded28 rnd h y * rounded21 rnd h y)
theorem polynomial29 (h y : ℝ) : exact29 h y = evaluate [((3/32 : ℝ), 0, 1), ((72057594037927935/9223372036854775808 : ℝ), 1, 1), ((6004799503160661/18446744073709551616 : ℝ), 2, 1)] h y := by
  simp only [exact29, polynomial28, polynomial21, evaluate] <;> ring
theorem bound29 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact29 h y| ≤ (51808742059/1099511627776 : ℝ) := by
  rw [polynomial29]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error29 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded29 rnd h y - exact29 h y| ≤ (35806475322252322144257/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded29 exact29
  apply rounded_step rnd hrnd (propagation := (917949953054802293293071/50216813883093446110686315385661331328818843555712276103168 : ℝ)) (magnitude := (51808742059/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound28 h y hh hy) (bound21 h y hh hy)
      (error28 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound29 h y hh hy
  · norm_num
  · norm_num
def exact30 (h y : ℝ) : ℝ := exact27 h y + exact29 h y
def rounded30 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded27 rnd h y + rounded29 rnd h y)
theorem polynomial30 (h y : ℝ) : exact30 h y = evaluate [((1/8 : ℝ), 0, 1), ((72057594037927935/9223372036854775808 : ℝ), 1, 1), ((6004799503160661/18446744073709551616 : ℝ), 2, 1)] h y := by
  simp only [exact30, polynomial27, polynomial29, evaluate] <;> ring
theorem bound30 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact30 h y| ≤ (68988611243/1099511627776 : ℝ) := by
  rw [polynomial30]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error30 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded30 rnd h y - exact30 h y| ≤ (27366465409358092828675/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded30 exact30
  apply rounded_step rnd hrnd (propagation := (45251208287991612571653/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (68988611243/1099511627776 : ℝ))
  · convert FindOrb.add_error (error27 rnd hrnd h y hh hy) (error29 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound30 h y hh hy
  · norm_num
  · norm_num
def exact31 (h y : ℝ) : ℝ := exact30 h y * exact0 h y
def rounded31 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded30 rnd h y * rounded0 rnd h y)
theorem polynomial31 (h y : ℝ) : exact31 h y = evaluate [((1/8 : ℝ), 1, 1), ((72057594037927935/9223372036854775808 : ℝ), 2, 1), ((6004799503160661/18446744073709551616 : ℝ), 3, 1)] h y := by
  simp only [exact31, polynomial30, polynomial0, evaluate] <;> ring
theorem bound31 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact31 h y| ≤ (4311788203/1099511627776 : ℝ) := by
  rw [polynomial31]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error31 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded31 rnd h y - exact31 h y| ≤ (4013415834382997094401/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded31 exact31
  apply rounded_step rnd hrnd (propagation := (27366465409358092828675/12554203470773361527671578846415332832204710888928069025792 : ℝ)) (magnitude := (4311788203/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound30 h y hh hy) (bound0 h y hh hy)
      (error30 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound31 h y hh hy
  · norm_num
  · norm_num
def exact32 (h y : ℝ) : ℝ := exact31 h y + exact3 h y
def rounded32 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded31 rnd h y + rounded3 rnd h y)
theorem polynomial32 (h y : ℝ) : exact32 h y = evaluate [((1/1 : ℝ), 0, 1), ((1/8 : ℝ), 1, 1), ((72057594037927935/9223372036854775808 : ℝ), 2, 1), ((6004799503160661/18446744073709551616 : ℝ), 3, 1)] h y := by
  simp only [exact32, polynomial31, polynomial3, evaluate] <;> ring
theorem bound32 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact32 h y| ≤ (554067602091/1099511627776 : ℝ) := by
  rw [polynomial32]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error32 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded32 rnd h y - exact32 h y| ≤ (155721750944424879423491/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded32 exact32
  apply rounded_step rnd hrnd (propagation := (39785639780148660256769/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (554067602091/1099511627776 : ℝ))
  · convert FindOrb.add_error (error31 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound32 h y hh hy
  · norm_num
  · norm_num
def exact33 (h y : ℝ) : ℝ := exact32 h y + exact2 h y
def rounded33 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded32 rnd h y + rounded2 rnd h y)
theorem polynomial33 (h y : ℝ) : exact33 h y = evaluate [((1/1 : ℝ), 0, 1), ((1/8 : ℝ), 1, 1), ((72057594037927935/9223372036854775808 : ℝ), 2, 1), ((6004799503160661/18446744073709551616 : ℝ), 3, 1)] h y := by
  simp only [exact33, polynomial32, polynomial2, evaluate] <;> ring
theorem bound33 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact33 h y| ≤ (554067602091/1099511627776 : ℝ) := by
  rw [polynomial33]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error33 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded33 rnd h y - exact33 h y| ≤ (57968055582138109583361/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded33 exact33
  apply rounded_step rnd hrnd (propagation := (155721750944424879423491/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (554067602091/1099511627776 : ℝ))
  · convert FindOrb.add_error (error32 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound33 h y hh hy
  · norm_num
  · norm_num
def exact34 (h y : ℝ) : ℝ := exact33 h y + exact2 h y
def rounded34 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded33 rnd h y + rounded2 rnd h y)
theorem polynomial34 (h y : ℝ) : exact34 h y = evaluate [((1/1 : ℝ), 0, 1), ((1/8 : ℝ), 1, 1), ((72057594037927935/9223372036854775808 : ℝ), 2, 1), ((6004799503160661/18446744073709551616 : ℝ), 3, 1)] h y := by
  simp only [exact34, polynomial33, polynomial2, evaluate] <;> ring
theorem bound34 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact34 h y| ≤ (554067602091/1099511627776 : ℝ) := by
  rw [polynomial34]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error34 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded34 rnd h y - exact34 h y| ≤ (308022693712679997243397/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded34 exact34
  apply rounded_step rnd hrnd (propagation := (57968055582138109583361/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (554067602091/1099511627776 : ℝ))
  · convert FindOrb.add_error (error33 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound34 h y hh hy
  · norm_num
  · norm_num
def exact35 (h y : ℝ) : ℝ := (5/16 : ℝ)
def rounded35 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (5/16 : ℝ)
theorem polynomial35 (h y : ℝ) : exact35 h y = evaluate [((5/16 : ℝ), 0, 0)] h y := by
  simp only [exact35, evaluate] <;> ring
theorem bound35 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact35 h y| ≤ (5/16 : ℝ) := by
  rw [polynomial35]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error35 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded35 rnd h y - exact35 h y| ≤ (0/1 : ℝ) := by
  simp [rounded35, exact35]
def exact36 (h y : ℝ) : ℝ := exact35 h y * exact4 h y
def rounded36 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded35 rnd h y * rounded4 rnd h y)
theorem polynomial36 (h y : ℝ) : exact36 h y = evaluate [((5/16 : ℝ), 0, 1)] h y := by
  simp only [exact36, polynomial35, polynomial4, evaluate] <;> ring
theorem bound36 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact36 h y| ≤ (5/32 : ℝ) := by
  rw [polynomial36]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error36 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded36 rnd h y - exact36 h y| ≤ (47223664828696452136961/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded36 exact36
  apply rounded_step rnd hrnd (propagation := (377789318629571617095685/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (5/32 : ℝ))
  · convert FindOrb.mul_error (bound35 h y hh hy) (bound4 h y hh hy)
      (error35 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound36 h y hh hy
  · norm_num
  · norm_num
def exact37 (h y : ℝ) : ℝ := exact2 h y + exact36 h y
def rounded37 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded36 rnd h y)
theorem polynomial37 (h y : ℝ) : exact37 h y = evaluate [((5/16 : ℝ), 0, 1)] h y := by
  simp only [exact37, polynomial2, polynomial36, evaluate] <;> ring
theorem bound37 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact37 h y| ≤ (5/32 : ℝ) := by
  rw [polynomial37]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error37 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded37 rnd h y - exact37 h y| ≤ (35417748621522339102721/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded37 exact37
  apply rounded_step rnd hrnd (propagation := (47223664828696452136961/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (5/32 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error36 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound37 h y hh hy
  · norm_num
  · norm_num
def exact38 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded38 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial38 (h y : ℝ) : exact38 h y = evaluate [] h y := by
  simp only [exact38, evaluate] <;> ring
theorem bound38 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact38 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial38]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error38 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded38 rnd h y - exact38 h y| ≤ (0/1 : ℝ) := by
  simp [rounded38, exact38]
def exact39 (h y : ℝ) : ℝ := exact38 h y * exact11 h y
def rounded39 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded38 rnd h y * rounded11 rnd h y)
theorem polynomial39 (h y : ℝ) : exact39 h y = evaluate [] h y := by
  simp only [exact39, polynomial38, polynomial11, evaluate] <;> ring
theorem bound39 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact39 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial39]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error39 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded39 rnd h y - exact39 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded39 exact39
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound38 h y hh hy) (bound11 h y hh hy)
      (error38 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound39 h y hh hy
  · norm_num
  · norm_num
def exact40 (h y : ℝ) : ℝ := exact37 h y + exact39 h y
def rounded40 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded37 rnd h y + rounded39 rnd h y)
theorem polynomial40 (h y : ℝ) : exact40 h y = evaluate [((5/16 : ℝ), 0, 1)] h y := by
  simp only [exact40, polynomial37, polynomial39, evaluate] <;> ring
theorem bound40 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact40 h y| ≤ (5/32 : ℝ) := by
  rw [polynomial40]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error40 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded40 rnd h y - exact40 h y| ≤ (23611832414348226068481/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded40 exact40
  apply rounded_step rnd hrnd (propagation := (70835497243044678205443/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (5/32 : ℝ))
  · convert FindOrb.add_error (error37 rnd hrnd h y hh hy) (error39 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound40 h y hh hy
  · norm_num
  · norm_num
def exact41 (h y : ℝ) : ℝ := (-75/64 : ℝ)
def rounded41 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-75/64 : ℝ)
theorem polynomial41 (h y : ℝ) : exact41 h y = evaluate [((-75/64 : ℝ), 0, 0)] h y := by
  simp only [exact41, evaluate] <;> ring
theorem bound41 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact41 h y| ≤ (75/64 : ℝ) := by
  rw [polynomial41]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error41 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded41 rnd h y - exact41 h y| ≤ (0/1 : ℝ) := by
  simp [rounded41, exact41]
def exact42 (h y : ℝ) : ℝ := exact41 h y * exact21 h y
def rounded42 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded41 rnd h y * rounded21 rnd h y)
theorem polynomial42 (h y : ℝ) : exact42 h y = evaluate [((-75/64 : ℝ), 0, 1), ((-1801439850948198375/18446744073709551616 : ℝ), 1, 1), ((-150119987579016525/36893488147419103232 : ℝ), 2, 1)] h y := by
  simp only [exact42, polynomial41, polynomial21, evaluate] <;> ring
theorem bound42 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact42 h y| ≤ (323804637867/549755813888 : ℝ) := by
  rw [polynomial42]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error42 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded42 rnd h y - exact42 h y| ≤ (223790470763836495233027/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded42 exact42
  apply rounded_step rnd hrnd (propagation := (22948748826370057332326775/100433627766186892221372630771322662657637687111424552206336 : ℝ)) (magnitude := (323804637867/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound41 h y hh hy) (bound21 h y hh hy)
      (error41 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound42 h y hh hy
  · norm_num
  · norm_num
def exact43 (h y : ℝ) : ℝ := exact40 h y + exact42 h y
def rounded43 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded40 rnd h y + rounded42 rnd h y)
theorem polynomial43 (h y : ℝ) : exact43 h y = evaluate [((-55/64 : ℝ), 0, 1), ((-1801439850948198375/18446744073709551616 : ℝ), 1, 1), ((-150119987579016525/36893488147419103232 : ℝ), 2, 1)] h y := by
  simp only [exact43, polynomial40, polynomial42, evaluate] <;> ring
theorem bound43 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact43 h y| ≤ (237905291947/549755813888 : ℝ) := by
  rw [polynomial43]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error43 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded43 rnd h y - exact43 h y| ≤ (607423179886358513319947/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded43 exact43
  apply rounded_step rnd hrnd (propagation := (271014135592532947369989/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (237905291947/549755813888 : ℝ))
  · convert FindOrb.add_error (error40 rnd hrnd h y hh hy) (error42 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound43 h y hh hy
  · norm_num
  · norm_num
def exact44 (h y : ℝ) : ℝ := (75/64 : ℝ)
def rounded44 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (75/64 : ℝ)
theorem polynomial44 (h y : ℝ) : exact44 h y = evaluate [((75/64 : ℝ), 0, 0)] h y := by
  simp only [exact44, evaluate] <;> ring
theorem bound44 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact44 h y| ≤ (75/64 : ℝ) := by
  rw [polynomial44]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error44 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded44 rnd h y - exact44 h y| ≤ (0/1 : ℝ) := by
  simp [rounded44, exact44]
def exact45 (h y : ℝ) : ℝ := exact44 h y * exact34 h y
def rounded45 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded44 rnd h y * rounded34 rnd h y)
theorem polynomial45 (h y : ℝ) : exact45 h y = evaluate [((75/64 : ℝ), 0, 1), ((75/512 : ℝ), 1, 1), ((5404319552844595125/590295810358705651712 : ℝ), 2, 1), ((450359962737049575/1180591620717411303424 : ℝ), 3, 1)] h y := by
  simp only [exact45, polynomial44, polynomial34, evaluate] <;> ring
theorem bound45 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact45 h y| ≤ (317040025/536870912 : ℝ) := by
  rw [polynomial45]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error45 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded45 rnd h y - exact45 h y| ≤ (225101463923883833888003/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded45 exact45
  apply rounded_step rnd hrnd (propagation := (23101702028450999793254775/100433627766186892221372630771322662657637687111424552206336 : ℝ)) (magnitude := (317040025/536870912 : ℝ))
  · convert FindOrb.mul_error (bound44 h y hh hy) (bound34 h y hh hy)
      (error44 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound45 h y hh hy
  · norm_num
  · norm_num
def exact46 (h y : ℝ) : ℝ := exact43 h y + exact45 h y
def rounded46 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded43 rnd h y + rounded45 rnd h y)
theorem polynomial46 (h y : ℝ) : exact46 h y = evaluate [((5/16 : ℝ), 0, 1), ((900719925474099225/18446744073709551616 : ℝ), 1, 1), ((3002399751580330725/590295810358705651712 : ℝ), 2, 1), ((450359962737049575/1180591620717411303424 : ℝ), 3, 1)] h y := by
  simp only [exact46, polynomial43, polynomial45, evaluate] <;> ring
theorem bound46 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact46 h y| ≤ (173487387307/1099511627776 : ℝ) := by
  rw [polynomial46]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error46 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded46 rnd h y - exact46 h y| ≤ (540735016343095898737929/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded46 exact46
  apply rounded_step rnd hrnd (propagation := (1057626107734126181095953/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (173487387307/1099511627776 : ℝ))
  · convert FindOrb.add_error (error43 rnd hrnd h y hh hy) (error45 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound46 h y hh hy
  · norm_num
  · norm_num
def exact47 (h y : ℝ) : ℝ := exact46 h y * exact0 h y
def rounded47 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded46 rnd h y * rounded0 rnd h y)
theorem polynomial47 (h y : ℝ) : exact47 h y = evaluate [((5/16 : ℝ), 1, 1), ((900719925474099225/18446744073709551616 : ℝ), 2, 1), ((3002399751580330725/590295810358705651712 : ℝ), 3, 1), ((450359962737049575/1180591620717411303424 : ℝ), 4, 1)] h y := by
  simp only [exact47, polynomial46, polynomial0, evaluate] <;> ring
theorem bound47 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact47 h y| ≤ (10842961707/1099511627776 : ℝ) := by
  rw [polynomial47]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error47 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded47 rnd h y - exact47 h y| ≤ (34541061176217019019473/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded47 exact47
  apply rounded_step rnd hrnd (propagation := (540735016343095898737929/12554203470773361527671578846415332832204710888928069025792 : ℝ)) (magnitude := (10842961707/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound46 h y hh hy) (bound0 h y hh hy)
      (error46 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound47 h y hh hy
  · norm_num
  · norm_num
def exact48 (h y : ℝ) : ℝ := exact47 h y + exact3 h y
def rounded48 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded47 rnd h y + rounded3 rnd h y)
theorem polynomial48 (h y : ℝ) : exact48 h y = evaluate [((1/1 : ℝ), 0, 1), ((5/16 : ℝ), 1, 1), ((900719925474099225/18446744073709551616 : ℝ), 2, 1), ((3002399751580330725/590295810358705651712 : ℝ), 3, 1), ((450359962737049575/1180591620717411303424 : ℝ), 4, 1)] h y := by
  simp only [exact48, polynomial47, polynomial3, evaluate] <;> ring
theorem bound48 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact48 h y| ≤ (560598775595/1099511627776 : ℝ) := by
  rw [polynomial48]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error48 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded48 rnd h y - exact48 h y| ≤ (55422023778452433893481/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded48 exact48
  apply rounded_step rnd hrnd (propagation := (144639986078348361458083/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (560598775595/1099511627776 : ℝ))
  · convert FindOrb.add_error (error47 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound48 h y hh hy
  · norm_num
  · norm_num
def exact49 (h y : ℝ) : ℝ := exact48 h y + exact2 h y
def rounded49 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded48 rnd h y + rounded2 rnd h y)
theorem polynomial49 (h y : ℝ) : exact49 h y = evaluate [((1/1 : ℝ), 0, 1), ((5/16 : ℝ), 1, 1), ((900719925474099225/18446744073709551616 : ℝ), 2, 1), ((3002399751580330725/590295810358705651712 : ℝ), 3, 1), ((450359962737049575/1180591620717411303424 : ℝ), 4, 1)] h y := by
  simp only [exact49, polynomial48, polynomial2, evaluate] <;> ring
theorem bound49 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact49 h y| ≤ (560598775595/1099511627776 : ℝ) := by
  rw [polynomial49]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error49 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded49 rnd h y - exact49 h y| ≤ (298736204149271109689765/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded49 exact49
  apply rounded_step rnd hrnd (propagation := (55422023778452433893481/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (560598775595/1099511627776 : ℝ))
  · convert FindOrb.add_error (error48 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound49 h y hh hy
  · norm_num
  · norm_num
def exact50 (h y : ℝ) : ℝ := exact49 h y + exact2 h y
def rounded50 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded49 rnd h y + rounded2 rnd h y)
theorem polynomial50 (h y : ℝ) : exact50 h y = evaluate [((1/1 : ℝ), 0, 1), ((5/16 : ℝ), 1, 1), ((900719925474099225/18446744073709551616 : ℝ), 2, 1), ((3002399751580330725/590295810358705651712 : ℝ), 3, 1), ((450359962737049575/1180591620717411303424 : ℝ), 4, 1)] h y := by
  simp only [exact50, polynomial49, polynomial2, evaluate] <;> ring
theorem bound50 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact50 h y| ≤ (560598775595/1099511627776 : ℝ) := by
  rw [polynomial50]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error50 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded50 rnd h y - exact50 h y| ≤ (187892156592366241902803/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded50 exact50
  apply rounded_step rnd hrnd (propagation := (298736204149271109689765/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (560598775595/1099511627776 : ℝ))
  · convert FindOrb.add_error (error49 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound50 h y hh hy
  · norm_num
  · norm_num
def exact51 (h y : ℝ) : ℝ := (5404319552844595/144115188075855872 : ℝ)
def rounded51 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (5404319552844595/144115188075855872 : ℝ)
theorem polynomial51 (h y : ℝ) : exact51 h y = evaluate [((5404319552844595/144115188075855872 : ℝ), 0, 0)] h y := by
  simp only [exact51, evaluate] <;> ring
theorem bound51 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact51 h y| ≤ (20615843021/549755813888 : ℝ) := by
  rw [polynomial51]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error51 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded51 rnd h y - exact51 h y| ≤ (0/1 : ℝ) := by
  simp [rounded51, exact51]
def exact52 (h y : ℝ) : ℝ := exact51 h y * exact4 h y
def rounded52 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded51 rnd h y * rounded4 rnd h y)
theorem polynomial52 (h y : ℝ) : exact52 h y = evaluate [((5404319552844595/144115188075855872 : ℝ), 0, 1)] h y := by
  simp only [exact52, polynomial51, polynomial4, evaluate] <;> ring
theorem bound52 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact52 h y| ≤ (20615843021/1099511627776 : ℝ) := by
  rw [polynomial52]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error52 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded52 rnd h y - exact52 h y| ≤ (5666839779498549837825/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded52 exact52
  apply rounded_step rnd hrnd (propagation := (1557689057575559861304352379292877/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (20615843021/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound51 h y hh hy) (bound4 h y hh hy)
      (error51 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound52 h y hh hy
  · norm_num
  · norm_num
def exact53 (h y : ℝ) : ℝ := exact2 h y + exact52 h y
def rounded53 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded52 rnd h y)
theorem polynomial53 (h y : ℝ) : exact53 h y = evaluate [((5404319552844595/144115188075855872 : ℝ), 0, 1)] h y := by
  simp only [exact53, polynomial2, polynomial52, evaluate] <;> ring
theorem bound53 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact53 h y| ≤ (20615843021/1099511627776 : ℝ) := by
  rw [polynomial53]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error53 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded53 rnd h y - exact53 h y| ≤ (4250129834623912378369/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded53 exact53
  apply rounded_step rnd hrnd (propagation := (5666839779498549837825/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (20615843021/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error52 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound53 h y hh hy
  · norm_num
  · norm_num
def exact54 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded54 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial54 (h y : ℝ) : exact54 h y = evaluate [] h y := by
  simp only [exact54, evaluate] <;> ring
theorem bound54 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact54 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial54]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error54 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded54 rnd h y - exact54 h y| ≤ (0/1 : ℝ) := by
  simp [rounded54, exact54]
def exact55 (h y : ℝ) : ℝ := exact54 h y * exact11 h y
def rounded55 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded54 rnd h y * rounded11 rnd h y)
theorem polynomial55 (h y : ℝ) : exact55 h y = evaluate [] h y := by
  simp only [exact55, polynomial54, polynomial11, evaluate] <;> ring
theorem bound55 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact55 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial55]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error55 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded55 rnd h y - exact55 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded55 exact55
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound54 h y hh hy) (bound11 h y hh hy)
      (error54 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound55 h y hh hy
  · norm_num
  · norm_num
def exact56 (h y : ℝ) : ℝ := exact53 h y + exact55 h y
def rounded56 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded53 rnd h y + rounded55 rnd h y)
theorem polynomial56 (h y : ℝ) : exact56 h y = evaluate [((5404319552844595/144115188075855872 : ℝ), 0, 1)] h y := by
  simp only [exact56, polynomial53, polynomial55, evaluate] <;> ring
theorem bound56 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact56 h y| ≤ (20615843021/1099511627776 : ℝ) := by
  rw [polynomial56]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error56 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded56 rnd h y - exact56 h y| ≤ (2833419889749274918913/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded56 exact56
  apply rounded_step rnd hrnd (propagation := (8500259669247824756739/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (20615843021/1099511627776 : ℝ))
  · convert FindOrb.add_error (error53 rnd hrnd h y hh hy) (error55 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound56 h y hh hy
  · norm_num
  · norm_num
def exact57 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded57 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial57 (h y : ℝ) : exact57 h y = evaluate [] h y := by
  simp only [exact57, evaluate] <;> ring
theorem bound57 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact57 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial57]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error57 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded57 rnd h y - exact57 h y| ≤ (0/1 : ℝ) := by
  simp [rounded57, exact57]
def exact58 (h y : ℝ) : ℝ := exact57 h y * exact21 h y
def rounded58 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded57 rnd h y * rounded21 rnd h y)
theorem polynomial58 (h y : ℝ) : exact58 h y = evaluate [] h y := by
  simp only [exact58, polynomial57, polynomial21, evaluate] <;> ring
theorem bound58 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact58 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial58]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error58 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded58 rnd h y - exact58 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded58 exact58
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound57 h y hh hy) (bound21 h y hh hy)
      (error57 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound58 h y hh hy
  · norm_num
  · norm_num
def exact59 (h y : ℝ) : ℝ := exact56 h y + exact58 h y
def rounded59 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded56 rnd h y + rounded58 rnd h y)
theorem polynomial59 (h y : ℝ) : exact59 h y = evaluate [((5404319552844595/144115188075855872 : ℝ), 0, 1)] h y := by
  simp only [exact59, polynomial56, polynomial58, evaluate] <;> ring
theorem bound59 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact59 h y| ≤ (20615843021/1099511627776 : ℝ) := by
  rw [polynomial59]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error59 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded59 rnd h y - exact59 h y| ≤ (7083549724373187297283/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded59 exact59
  apply rounded_step rnd hrnd (propagation := (11333679558997099675653/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (20615843021/1099511627776 : ℝ))
  · convert FindOrb.add_error (error56 rnd hrnd h y hh hy) (error58 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound59 h y hh hy
  · norm_num
  · norm_num
def exact60 (h y : ℝ) : ℝ := (3/16 : ℝ)
def rounded60 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (3/16 : ℝ)
theorem polynomial60 (h y : ℝ) : exact60 h y = evaluate [((3/16 : ℝ), 0, 0)] h y := by
  simp only [exact60, evaluate] <;> ring
theorem bound60 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact60 h y| ≤ (3/16 : ℝ) := by
  rw [polynomial60]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error60 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded60 rnd h y - exact60 h y| ≤ (0/1 : ℝ) := by
  simp [rounded60, exact60]
def exact61 (h y : ℝ) : ℝ := exact60 h y * exact34 h y
def rounded61 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded60 rnd h y * rounded34 rnd h y)
theorem polynomial61 (h y : ℝ) : exact61 h y = evaluate [((3/16 : ℝ), 0, 1), ((3/128 : ℝ), 1, 1), ((216172782113783805/147573952589676412928 : ℝ), 2, 1), ((18014398509481983/295147905179352825856 : ℝ), 3, 1)] h y := by
  simp only [exact61, polynomial60, polynomial34, evaluate] <;> ring
theorem bound61 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact61 h y| ≤ (12681601/134217728 : ℝ) := by
  rw [polynomial61]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error61 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded61 rnd h y - exact61 h y| ≤ (72032468455642826844161/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded61 exact61
  apply rounded_step rnd hrnd (propagation := (924068081138039991730191/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (12681601/134217728 : ℝ))
  · convert FindOrb.mul_error (bound60 h y hh hy) (bound34 h y hh hy)
      (error60 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound61 h y hh hy
  · norm_num
  · norm_num
def exact62 (h y : ℝ) : ℝ := exact59 h y + exact61 h y
def rounded62 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded59 rnd h y + rounded61 rnd h y)
theorem polynomial62 (h y : ℝ) : exact62 h y = evaluate [((32425917317067571/144115188075855872 : ℝ), 0, 1), ((3/128 : ℝ), 1, 1), ((216172782113783805/147573952589676412928 : ℝ), 2, 1), ((18014398509481983/295147905179352825856 : ℝ), 3, 1)] h y := by
  simp only [exact62, polynomial59, polynomial61, evaluate] <;> ring
theorem bound62 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact62 h y| ≤ (124503518413/1099511627776 : ℝ) := by
  rw [polynomial62]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error62 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded62 rnd h y - exact62 h y| ≤ (12913900147331725464833/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded62 exact62
  apply rounded_step rnd hrnd (propagation := (86199567904389201438727/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (124503518413/1099511627776 : ℝ))
  · convert FindOrb.add_error (error59 rnd hrnd h y hh hy) (error61 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound62 h y hh hy
  · norm_num
  · norm_num
def exact63 (h y : ℝ) : ℝ := (5404319552844595/36028797018963968 : ℝ)
def rounded63 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (5404319552844595/36028797018963968 : ℝ)
theorem polynomial63 (h y : ℝ) : exact63 h y = evaluate [((5404319552844595/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact63, evaluate] <;> ring
theorem bound63 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact63 h y| ≤ (164926744167/1099511627776 : ℝ) := by
  rw [polynomial63]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error63 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded63 rnd h y - exact63 h y| ≤ (0/1 : ℝ) := by
  simp [rounded63, exact63]
def exact64 (h y : ℝ) : ℝ := exact63 h y * exact50 h y
def rounded64 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded63 rnd h y * rounded50 rnd h y)
theorem polynomial64 (h y : ℝ) : exact64 h y = evaluate [((5404319552844595/36028797018963968 : ℝ), 0, 1), ((27021597764222975/576460752303423488 : ℝ), 1, 1), ((4867778304876400856711344034938875/664613997892457936451903530140172288 : ℝ), 2, 1), ((16225927682921336053929824628681375/21267647932558653966460912964485513216 : ℝ), 3, 1), ((2433889152438200225693688785797125/42535295865117307932921825928971026432 : ℝ), 4, 1)] h y := by
  simp only [exact64, polynomial63, polynomial50, evaluate] <;> ring
theorem bound64 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact64 h y| ≤ (21022454085/274877906944 : ℝ) := by
  rw [polynomial64]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error64 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded64 rnd h y - exact64 h y| ≤ (4245303958333576388027/98079714615416886934934209737619787751599303819750539264 : ℝ) := by
  unfold rounded64 exact64
  apply rounded_step rnd hrnd (propagation := (30988441641295089683470825661200101/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (21022454085/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound63 h y hh hy) (bound50 h y hh hy)
      (error63 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound64 h y hh hy
  · norm_num
  · norm_num
def exact65 (h y : ℝ) : ℝ := exact62 h y + exact64 h y
def rounded65 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded62 rnd h y + rounded64 rnd h y)
theorem polynomial65 (h y : ℝ) : exact65 h y = evaluate [((54043195528445951/144115188075855872 : ℝ), 0, 1), ((40532396646334463/576460752303423488 : ℝ), 1, 1), ((5841333965851681023550013214556155/664613997892457936451903530140172288 : ℝ), 2, 1), ((17524001897555042889004854673058463/21267647932558653966460912964485513216 : ℝ), 3, 1), ((2433889152438200225693688785797125/42535295865117307932921825928971026432 : ℝ), 4, 1)] h y := by
  simp only [exact65, polynomial62, polynomial64, evaluate] <;> ring
theorem bound65 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact65 h y| ≤ (6518541711/34359738368 : ℝ) := by
  rw [polynomial65]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error65 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded65 rnd h y - exact65 h y| ≤ (199904914141540474586041/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded65 exact65
  apply rounded_step rnd hrnd (propagation := (21404508063998878240887/196159429230833773869868419475239575503198607639501078528 : ℝ)) (magnitude := (6518541711/34359738368 : ℝ))
  · convert FindOrb.add_error (error62 rnd hrnd h y hh hy) (error64 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound65 h y hh hy
  · norm_num
  · norm_num
def exact66 (h y : ℝ) : ℝ := exact65 h y * exact0 h y
def rounded66 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded65 rnd h y * rounded0 rnd h y)
theorem polynomial66 (h y : ℝ) : exact66 h y = evaluate [((54043195528445951/144115188075855872 : ℝ), 1, 1), ((40532396646334463/576460752303423488 : ℝ), 2, 1), ((5841333965851681023550013214556155/664613997892457936451903530140172288 : ℝ), 3, 1), ((17524001897555042889004854673058463/21267647932558653966460912964485513216 : ℝ), 4, 1), ((2433889152438200225693688785797125/42535295865117307932921825928971026432 : ℝ), 5, 1)] h y := by
  simp only [exact66, polynomial65, polynomial0, evaluate] <;> ring
theorem bound66 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact66 h y| ≤ (6518541711/549755813888 : ℝ) := by
  rw [polynomial66]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error66 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded66 rnd h y - exact66 h y| ≤ (3571465058923280050703/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded66 exact66
  apply rounded_step rnd hrnd (propagation := (199904914141540474586041/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (6518541711/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound65 h y hh hy) (bound0 h y hh hy)
      (error65 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound66 h y hh hy
  · norm_num
  · norm_num
def exact67 (h y : ℝ) : ℝ := exact66 h y + exact3 h y
def rounded67 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded66 rnd h y + rounded3 rnd h y)
theorem polynomial67 (h y : ℝ) : exact67 h y = evaluate [((1/1 : ℝ), 0, 1), ((54043195528445951/144115188075855872 : ℝ), 1, 1), ((40532396646334463/576460752303423488 : ℝ), 2, 1), ((5841333965851681023550013214556155/664613997892457936451903530140172288 : ℝ), 3, 1), ((17524001897555042889004854673058463/21267647932558653966460912964485513216 : ℝ), 4, 1), ((2433889152438200225693688785797125/42535295865117307932921825928971026432 : ℝ), 5, 1)] h y := by
  simp only [exact67, polynomial66, polynomial3, evaluate] <;> ring
theorem bound67 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact67 h y| ≤ (281396448655/549755813888 : ℝ) := by
  rw [polynomial67]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error67 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded67 rnd h y - exact67 h y| ≤ (83596695394684303791135/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded67 exact67
  apply rounded_step rnd hrnd (propagation := (89843723961607443621949/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (281396448655/549755813888 : ℝ))
  · convert FindOrb.add_error (error66 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound67 h y hh hy
  · norm_num
  · norm_num
def exact68 (h y : ℝ) : ℝ := exact67 h y + exact2 h y
def rounded68 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded67 rnd h y + rounded2 rnd h y)
theorem polynomial68 (h y : ℝ) : exact68 h y = evaluate [((1/1 : ℝ), 0, 1), ((54043195528445951/144115188075855872 : ℝ), 1, 1), ((40532396646334463/576460752303423488 : ℝ), 2, 1), ((5841333965851681023550013214556155/664613997892457936451903530140172288 : ℝ), 3, 1), ((17524001897555042889004854673058463/21267647932558653966460912964485513216 : ℝ), 4, 1), ((2433889152438200225693688785797125/42535295865117307932921825928971026432 : ℝ), 5, 1)] h y := by
  simp only [exact68, polynomial67, polynomial2, evaluate] <;> ring
theorem bound68 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact68 h y| ≤ (281396448655/549755813888 : ℝ) := by
  rw [polynomial68]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error68 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded68 rnd h y - exact68 h y| ≤ (244543057617129771542591/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded68 exact68
  apply rounded_step rnd hrnd (propagation := (83596695394684303791135/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (281396448655/549755813888 : ℝ))
  · convert FindOrb.add_error (error67 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound68 h y hh hy
  · norm_num
  · norm_num
def exact69 (h y : ℝ) : ℝ := exact68 h y + exact2 h y
def rounded69 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded68 rnd h y + rounded2 rnd h y)
theorem polynomial69 (h y : ℝ) : exact69 h y = evaluate [((1/1 : ℝ), 0, 1), ((54043195528445951/144115188075855872 : ℝ), 1, 1), ((40532396646334463/576460752303423488 : ℝ), 2, 1), ((5841333965851681023550013214556155/664613997892457936451903530140172288 : ℝ), 3, 1), ((17524001897555042889004854673058463/21267647932558653966460912964485513216 : ℝ), 4, 1), ((2433889152438200225693688785797125/42535295865117307932921825928971026432 : ℝ), 5, 1)] h y := by
  simp only [exact69, polynomial68, polynomial2, evaluate] <;> ring
theorem bound69 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact69 h y| ≤ (281396448655/549755813888 : ℝ) := by
  rw [polynomial69]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error69 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded69 rnd h y - exact69 h y| ≤ (5029573819451420867233/24519928653854221733733552434404946937899825954937634816 : ℝ) := by
  unfold rounded69 exact69
  apply rounded_step rnd hrnd (propagation := (244543057617129771542591/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (281396448655/549755813888 : ℝ))
  · convert FindOrb.add_error (error68 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound69 h y hh hy
  · norm_num
  · norm_num
def exact70 (h y : ℝ) : ℝ := (1726144605126955/36028797018963968 : ℝ)
def rounded70 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1726144605126955/36028797018963968 : ℝ)
theorem polynomial70 (h y : ℝ) : exact70 h y = evaluate [((1726144605126955/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact70, evaluate] <;> ring
theorem bound70 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact70 h y| ≤ (52677752843/1099511627776 : ℝ) := by
  rw [polynomial70]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error70 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded70 rnd h y - exact70 h y| ≤ (0/1 : ℝ) := by
  simp [rounded70, exact70]
def exact71 (h y : ℝ) : ℝ := exact70 h y * exact4 h y
def rounded71 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded70 rnd h y * rounded4 rnd h y)
theorem polynomial71 (h y : ℝ) : exact71 h y = evaluate [((1726144605126955/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact71, polynomial70, polynomial4, evaluate] <;> ring
theorem bound71 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact71 h y| ≤ (13169438211/549755813888 : ℝ) := by
  rw [polynomial71]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error71 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded71 rnd h y - exact71 h y| ≤ (7239975222067312197633/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded71 exact71
  apply rounded_step rnd hrnd (propagation := (3980218470698789823266865582356491/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (13169438211/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound70 h y hh hy) (bound4 h y hh hy)
      (error70 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound71 h y hh hy
  · norm_num
  · norm_num
def exact72 (h y : ℝ) : ℝ := exact2 h y + exact71 h y
def rounded72 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded71 rnd h y)
theorem polynomial72 (h y : ℝ) : exact72 h y = evaluate [((1726144605126955/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact72, polynomial2, polynomial71, evaluate] <;> ring
theorem bound72 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact72 h y| ≤ (13169438211/549755813888 : ℝ) := by
  rw [polynomial72]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error72 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded72 rnd h y - exact72 h y| ≤ (5429981416567664017409/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded72 exact72
  apply rounded_step rnd hrnd (propagation := (7239975222067312197633/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (13169438211/549755813888 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error71 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound72 h y hh hy
  · norm_num
  · norm_num
def exact73 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded73 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial73 (h y : ℝ) : exact73 h y = evaluate [] h y := by
  simp only [exact73, evaluate] <;> ring
theorem bound73 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact73 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial73]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error73 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded73 rnd h y - exact73 h y| ≤ (0/1 : ℝ) := by
  simp [rounded73, exact73]
def exact74 (h y : ℝ) : ℝ := exact73 h y * exact11 h y
def rounded74 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded73 rnd h y * rounded11 rnd h y)
theorem polynomial74 (h y : ℝ) : exact74 h y = evaluate [] h y := by
  simp only [exact74, polynomial73, polynomial11, evaluate] <;> ring
theorem bound74 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact74 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial74]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error74 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded74 rnd h y - exact74 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded74 exact74
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound73 h y hh hy) (bound11 h y hh hy)
      (error73 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound74 h y hh hy
  · norm_num
  · norm_num
def exact75 (h y : ℝ) : ℝ := exact72 h y + exact74 h y
def rounded75 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded72 rnd h y + rounded74 rnd h y)
theorem polynomial75 (h y : ℝ) : exact75 h y = evaluate [((1726144605126955/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact75, polynomial72, polynomial74, evaluate] <;> ring
theorem bound75 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact75 h y| ≤ (13169438211/549755813888 : ℝ) := by
  rw [polynomial75]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error75 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded75 rnd h y - exact75 h y| ≤ (3619987611050835968001/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded75 exact75
  apply rounded_step rnd hrnd (propagation := (10859962833135328034819/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (13169438211/549755813888 : ℝ))
  · convert FindOrb.add_error (error72 rnd hrnd h y hh hy) (error74 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound75 h y hh hy
  · norm_num
  · norm_num
def exact76 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded76 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial76 (h y : ℝ) : exact76 h y = evaluate [] h y := by
  simp only [exact76, evaluate] <;> ring
theorem bound76 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact76 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial76]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error76 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded76 rnd h y - exact76 h y| ≤ (0/1 : ℝ) := by
  simp [rounded76, exact76]
def exact77 (h y : ℝ) : ℝ := exact76 h y * exact21 h y
def rounded77 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded76 rnd h y * rounded21 rnd h y)
theorem polynomial77 (h y : ℝ) : exact77 h y = evaluate [] h y := by
  simp only [exact77, polynomial76, polynomial21, evaluate] <;> ring
theorem bound77 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact77 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial77]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error77 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded77 rnd h y - exact77 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded77 exact77
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound76 h y hh hy) (bound21 h y hh hy)
      (error76 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound77 h y hh hy
  · norm_num
  · norm_num
def exact78 (h y : ℝ) : ℝ := exact75 h y + exact77 h y
def rounded78 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded75 rnd h y + rounded77 rnd h y)
theorem polynomial78 (h y : ℝ) : exact78 h y = evaluate [((1726144605126955/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact78, polynomial75, polynomial77, evaluate] <;> ring
theorem bound78 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact78 h y| ≤ (13169438211/549755813888 : ℝ) := by
  rw [polynomial78]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error78 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded78 rnd h y - exact78 h y| ≤ (9049969027635679854595/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded78 exact78
  apply rounded_step rnd hrnd (propagation := (14479950444203343872005/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (13169438211/549755813888 : ℝ))
  · convert FindOrb.add_error (error75 rnd hrnd h y hh hy) (error77 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound78 h y hh hy
  · norm_num
  · norm_num
def exact79 (h y : ℝ) : ℝ := (8088372176621085/72057594037927936 : ℝ)
def rounded79 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (8088372176621085/72057594037927936 : ℝ)
theorem polynomial79 (h y : ℝ) : exact79 h y = evaluate [((8088372176621085/72057594037927936 : ℝ), 0, 0)] h y := by
  simp only [exact79, evaluate] <;> ring
theorem bound79 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact79 h y| ≤ (123418764903/1099511627776 : ℝ) := by
  rw [polynomial79]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error79 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded79 rnd h y - exact79 h y| ≤ (0/1 : ℝ) := by
  simp [rounded79, exact79]
def exact80 (h y : ℝ) : ℝ := exact79 h y * exact34 h y
def rounded80 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded79 rnd h y * rounded34 rnd h y)
theorem polynomial80 (h y : ℝ) : exact80 h y = evaluate [((8088372176621085/72057594037927936 : ℝ), 0, 1), ((8088372176621085/576460752303423488 : ℝ), 1, 1), ((582828638730633688940183031509475/664613997892457936451903530140172288 : ℝ), 2, 1), ((48569053227552805389588875137185/1329227995784915872903807060280344576 : ℝ), 3, 1)] h y := by
  simp only [exact80, polynomial79, polynomial34, evaluate] <;> ring
theorem bound80 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact80 h y| ≤ (62193375127/1099511627776 : ℝ) := by
  rw [polynomial80]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error80 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded80 rnd h y - exact80 h y| ≤ (43122943266203128282351/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded80 exact80
  apply rounded_step rnd hrnd (propagation := (38015780420114028809853502412095491/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (62193375127/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound79 h y hh hy) (bound34 h y hh hy)
      (error79 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound80 h y hh hy
  · norm_num
  · norm_num
def exact81 (h y : ℝ) : ℝ := exact78 h y + exact80 h y
def rounded81 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded78 rnd h y + rounded80 rnd h y)
theorem polynomial81 (h y : ℝ) : exact81 h y = evaluate [((11540661386874995/72057594037927936 : ℝ), 0, 1), ((8088372176621085/576460752303423488 : ℝ), 1, 1), ((582828638730633688940183031509475/664613997892457936451903530140172288 : ℝ), 2, 1), ((48569053227552805389588875137185/1329227995784915872903807060280344576 : ℝ), 3, 1)] h y := by
  simp only [exact81, polynomial78, polynomial80, evaluate] <;> ring
theorem bound81 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact81 h y| ≤ (22133062887/274877906944 : ℝ) := by
  rw [polynomial81]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error81 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded81 rnd h y - exact81 h y| ≤ (36695330661375729983099/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded81 exact81
  apply rounded_step rnd hrnd (propagation := (61222881321474487991541/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (22133062887/274877906944 : ℝ))
  · convert FindOrb.add_error (error78 rnd hrnd h y hh hy) (error80 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound81 h y hh hy
  · norm_num
  · norm_num
def exact82 (h y : ℝ) : ℝ := (-1837877486742935/72057594037927936 : ℝ)
def rounded82 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-1837877486742935/72057594037927936 : ℝ)
theorem polynomial82 (h y : ℝ) : exact82 h y = evaluate [((-1837877486742935/72057594037927936 : ℝ), 0, 0)] h y := by
  simp only [exact82, evaluate] <;> ring
theorem bound82 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact82 h y| ≤ (28043784893/1099511627776 : ℝ) := by
  rw [polynomial82]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error82 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded82 rnd h y - exact82 h y| ≤ (0/1 : ℝ) := by
  simp [rounded82, exact82]
def exact83 (h y : ℝ) : ℝ := exact82 h y * exact50 h y
def rounded83 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded82 rnd h y * rounded50 rnd h y)
theorem polynomial83 (h y : ℝ) : exact83 h y = evaluate [((-1837877486742935/72057594037927936 : ℝ), 0, 1), ((-9189387433714675/1152921504606846976 : ℝ), 1, 1), ((-1655412872889621199589648257725375/1329227995784915872903807060280344576 : ℝ), 2, 1), ((-5518042909632070619351890357177875/42535295865117307932921825928971026432 : ℝ), 3, 1), ((-827706436444810530874418376002625/85070591730234615865843651857942052864 : ℝ), 4, 1)] h y := by
  simp only [exact83, polynomial82, polynomial50, evaluate] <;> ring
theorem bound83 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact83 h y| ≤ (14298449491/1099511627776 : ℝ) := by
  rw [polynomial83]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error83 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded83 rnd h y - exact83 h y| ≤ (5774898018617966768033/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded83 exact83
  apply rounded_step rnd hrnd (propagation := (5269207222558190773797010345755079/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (14298449491/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound82 h y hh hy) (bound50 h y hh hy)
      (error82 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound83 h y hh hy
  · norm_num
  · norm_num
def exact84 (h y : ℝ) : ℝ := exact81 h y + exact83 h y
def rounded84 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded81 rnd h y + rounded83 rnd h y)
theorem polynomial84 (h y : ℝ) : exact84 h y = evaluate [((2425695975033015/18014398509481984 : ℝ), 0, 1), ((6987356919527495/1152921504606846976 : ℝ), 1, 1), ((-489755595428353821709282194706425/1329227995784915872903807060280344576 : ℝ), 2, 1), ((-3963833206350380846885046352787955/42535295865117307932921825928971026432 : ℝ), 3, 1), ((-827706436444810530874418376002625/85070591730234615865843651857942052864 : ℝ), 4, 1)] h y := by
  simp only [exact84, polynomial81, polynomial83, evaluate] <;> ring
theorem bound84 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact84 h y| ≤ (37117704861/549755813888 : ℝ) := by
  rw [polynomial84]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error84 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded84 rnd h y - exact84 h y| ≤ (95143294382744207957049/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded84 exact84
  apply rounded_step rnd hrnd (propagation := (10617557169998424187783/196159429230833773869868419475239575503198607639501078528 : ℝ)) (magnitude := (37117704861/549755813888 : ℝ))
  · convert FindOrb.add_error (error81 rnd hrnd h y hh hy) (error83 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound84 h y hh hy
  · norm_num
  · norm_num
def exact85 (h y : ℝ) : ℝ := (7405689763698481/576460752303423488 : ℝ)
def rounded85 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (7405689763698481/576460752303423488 : ℝ)
theorem polynomial85 (h y : ℝ) : exact85 h y = evaluate [((7405689763698481/576460752303423488 : ℝ), 0, 0)] h y := by
  simp only [exact85, evaluate] <;> ring
theorem bound85 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact85 h y| ≤ (7062616123/549755813888 : ℝ) := by
  rw [polynomial85]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error85 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded85 rnd h y - exact85 h y| ≤ (0/1 : ℝ) := by
  simp [rounded85, exact85]
def exact86 (h y : ℝ) : ℝ := exact85 h y * exact69 h y
def rounded86 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded85 rnd h y * rounded69 rnd h y)
theorem polynomial86 (h y : ℝ) : exact86 h y = evaluate [((7405689763698481/576460752303423488 : ℝ), 0, 1), ((400227139922567699875404069300431/83076749736557242056487941267521536 : ℝ), 1, 1), ((300170354941925773055130611050703/332306998946228968225951765070086144 : ℝ), 2, 1), ((43259107157252046522247742794563476452257662700555/383123885216472214589586756787577295904684780545900544 : ℝ), 3, 1), ((129777321471756138221535341421726771236506817294703/12259964326927110866866776217202473468949912977468817408 : ℝ), 4, 1), ((18024627982188351230648227146528421844123736667125/24519928653854221733733552434404946937899825954937634816 : ℝ), 5, 1)] h y := by
  simp only [exact86, polynomial85, polynomial69, evaluate] <;> ring
theorem bound86 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact86 h y| ≤ (3615050619/549755813888 : ℝ) := by
  rw [polynomial86]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error86 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded86 rnd h y - exact86 h y| ≤ (2564498344878530941509/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded86 exact86
  apply rounded_step rnd hrnd (propagation := (35521949149076296032178428197659/13479973333575319897333507543509815336818572211270286240551805124608 : ℝ)) (magnitude := (3615050619/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound85 h y hh hy) (bound69 h y hh hy)
      (error85 rnd hrnd h y hh hy) (error69 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound86 h y hh hy
  · norm_num
  · norm_num
def exact87 (h y : ℝ) : ℝ := exact84 h y + exact86 h y
def rounded87 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded84 rnd h y + rounded86 rnd h y)
theorem polynomial87 (h y : ℝ) : exact87 h y = evaluate [((85027960964754961/576460752303423488 : ℝ), 0, 1), ((903719268227986632475430049900751/83076749736557242056487941267521536 : ℝ), 1, 1), ((710925824339349270511240249496387/1329227995784915872903807060280344576 : ℝ), 2, 1), ((7556071655095299400328883657481343089027040349195/383123885216472214589586756787577295904684780545900544 : ℝ), 3, 1), ((10492252711915823443655050079191852463503823630703/12259964326927110866866776217202473468949912977468817408 : ℝ), 4, 1), ((18024627982188351230648227146528421844123736667125/24519928653854221733733552434404946937899825954937634816 : ℝ), 5, 1)] h y := by
  simp only [exact87, polynomial84, polynomial86, evaluate] <;> ring
theorem bound87 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact87 h y| ≤ (81463903295/1099511627776 : ℝ) := by
  rw [polynomial87]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error87 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded87 rnd h y - exact87 h y| ≤ (27867151171777570582577/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded87 exact87
  apply rounded_step rnd hrnd (propagation := (100272291072501269840067/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (81463903295/1099511627776 : ℝ))
  · convert FindOrb.add_error (error84 rnd hrnd h y hh hy) (error86 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound87 h y hh hy
  · norm_num
  · norm_num
def exact88 (h y : ℝ) : ℝ := exact87 h y * exact0 h y
def rounded88 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded87 rnd h y * rounded0 rnd h y)
theorem polynomial88 (h y : ℝ) : exact88 h y = evaluate [((85027960964754961/576460752303423488 : ℝ), 1, 1), ((903719268227986632475430049900751/83076749736557242056487941267521536 : ℝ), 2, 1), ((710925824339349270511240249496387/1329227995784915872903807060280344576 : ℝ), 3, 1), ((7556071655095299400328883657481343089027040349195/383123885216472214589586756787577295904684780545900544 : ℝ), 4, 1), ((10492252711915823443655050079191852463503823630703/12259964326927110866866776217202473468949912977468817408 : ℝ), 5, 1), ((18024627982188351230648227146528421844123736667125/24519928653854221733733552434404946937899825954937634816 : ℝ), 6, 1)] h y := by
  simp only [exact88, polynomial87, polynomial0, evaluate] <;> ring
theorem bound88 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact88 h y| ≤ (1272873489/274877906944 : ℝ) := by
  rw [polynomial88]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error88 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded88 rnd h y - exact88 h y| ≤ (7666557393866045860877/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded88 exact88
  apply rounded_step rnd hrnd (propagation := (27867151171777570582577/6277101735386680763835789423207666416102355444464034512896 : ℝ)) (magnitude := (1272873489/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound87 h y hh hy) (bound0 h y hh hy)
      (error87 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound88 h y hh hy
  · norm_num
  · norm_num
def exact89 (h y : ℝ) : ℝ := exact88 h y + exact3 h y
def rounded89 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded88 rnd h y + rounded3 rnd h y)
theorem polynomial89 (h y : ℝ) : exact89 h y = evaluate [((1/1 : ℝ), 0, 1), ((85027960964754961/576460752303423488 : ℝ), 1, 1), ((903719268227986632475430049900751/83076749736557242056487941267521536 : ℝ), 2, 1), ((710925824339349270511240249496387/1329227995784915872903807060280344576 : ℝ), 3, 1), ((7556071655095299400328883657481343089027040349195/383123885216472214589586756787577295904684780545900544 : ℝ), 4, 1), ((10492252711915823443655050079191852463503823630703/12259964326927110866866776217202473468949912977468817408 : ℝ), 5, 1), ((18024627982188351230648227146528421844123736667125/24519928653854221733733552434404946937899825954937634816 : ℝ), 6, 1)] h y := by
  simp only [exact89, polynomial88, polynomial3, evaluate] <;> ring
theorem bound89 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact89 h y| ≤ (138711826961/274877906944 : ℝ) := by
  rw [polynomial89]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error89 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded89 rnd h y - exact89 h y| ≤ (159482054446616345914383/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded89 exact89
  apply rounded_step rnd hrnd (propagation := (41612210559890184640007/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (138711826961/274877906944 : ℝ))
  · convert FindOrb.add_error (error88 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound89 h y hh hy
  · norm_num
  · norm_num
def exact90 (h y : ℝ) : ℝ := exact89 h y + exact2 h y
def rounded90 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded89 rnd h y + rounded2 rnd h y)
theorem polynomial90 (h y : ℝ) : exact90 h y = evaluate [((1/1 : ℝ), 0, 1), ((85027960964754961/576460752303423488 : ℝ), 1, 1), ((903719268227986632475430049900751/83076749736557242056487941267521536 : ℝ), 2, 1), ((710925824339349270511240249496387/1329227995784915872903807060280344576 : ℝ), 3, 1), ((7556071655095299400328883657481343089027040349195/383123885216472214589586756787577295904684780545900544 : ℝ), 4, 1), ((10492252711915823443655050079191852463503823630703/12259964326927110866866776217202473468949912977468817408 : ℝ), 5, 1), ((18024627982188351230648227146528421844123736667125/24519928653854221733733552434404946937899825954937634816 : ℝ), 6, 1)] h y := by
  simp only [exact90, polynomial89, polynomial2, evaluate] <;> ring
theorem bound90 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact90 h y| ≤ (138711826961/274877906944 : ℝ) := by
  rw [polynomial90]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error90 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded90 rnd h y - exact90 h y| ≤ (14733730485840770159297/98079714615416886934934209737619787751599303819750539264 : ℝ) := by
  unfold rounded90 exact90
  apply rounded_step rnd hrnd (propagation := (159482054446616345914383/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (138711826961/274877906944 : ℝ))
  · convert FindOrb.add_error (error89 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound90 h y hh hy
  · norm_num
  · norm_num
def exact91 (h y : ℝ) : ℝ := exact90 h y + exact2 h y
def rounded91 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded90 rnd h y + rounded2 rnd h y)
theorem polynomial91 (h y : ℝ) : exact91 h y = evaluate [((1/1 : ℝ), 0, 1), ((85027960964754961/576460752303423488 : ℝ), 1, 1), ((903719268227986632475430049900751/83076749736557242056487941267521536 : ℝ), 2, 1), ((710925824339349270511240249496387/1329227995784915872903807060280344576 : ℝ), 3, 1), ((7556071655095299400328883657481343089027040349195/383123885216472214589586756787577295904684780545900544 : ℝ), 4, 1), ((10492252711915823443655050079191852463503823630703/12259964326927110866866776217202473468949912977468817408 : ℝ), 5, 1), ((18024627982188351230648227146528421844123736667125/24519928653854221733733552434404946937899825954937634816 : ℝ), 6, 1)] h y := by
  simp only [exact91, polynomial90, polynomial2, evaluate] <;> ring
theorem bound91 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact91 h y| ≤ (138711826961/274877906944 : ℝ) := by
  rw [polynomial91]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error91 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded91 rnd h y - exact91 h y| ≤ (311997321100288299183121/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded91 exact91
  apply rounded_step rnd hrnd (propagation := (14733730485840770159297/98079714615416886934934209737619787751599303819750539264 : ℝ)) (magnitude := (138711826961/274877906944 : ℝ))
  · convert FindOrb.add_error (error90 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound91 h y hh hy
  · norm_num
  · norm_num
def exact92 (h y : ℝ) : ℝ := (609534820015259/36028797018963968 : ℝ)
def rounded92 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (609534820015259/36028797018963968 : ℝ)
theorem polynomial92 (h y : ℝ) : exact92 h y = evaluate [((609534820015259/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact92, evaluate] <;> ring
theorem bound92 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact92 h y| ≤ (9300763245/549755813888 : ℝ) := by
  rw [polynomial92]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error92 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded92 rnd h y - exact92 h y| ≤ (0/1 : ℝ) := by
  simp [rounded92, exact92]
def exact93 (h y : ℝ) : ℝ := exact92 h y * exact4 h y
def rounded93 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded92 rnd h y * rounded4 rnd h y)
theorem polynomial93 (h y : ℝ) : exact93 h y = evaluate [((609534820015259/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact93, polynomial92, polynomial4, evaluate] <;> ring
theorem bound93 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact93 h y| ≤ (9300763245/1099511627776 : ℝ) := by
  rw [polynomial93]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error93 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded93 rnd h y - exact93 h y| ≤ (2556574333767285473281/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded93 exact93
  apply rounded_step rnd hrnd (propagation := (702745801812702693275752139219565/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (9300763245/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound92 h y hh hy) (bound4 h y hh hy)
      (error92 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound93 h y hh hy
  · norm_num
  · norm_num
def exact94 (h y : ℝ) : ℝ := exact2 h y + exact93 h y
def rounded94 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded93 rnd h y)
theorem polynomial94 (h y : ℝ) : exact94 h y = evaluate [((609534820015259/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact94, polynomial2, polynomial93, evaluate] <;> ring
theorem bound94 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact94 h y| ≤ (9300763245/1099511627776 : ℝ) := by
  rw [polynomial94]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error94 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded94 rnd h y - exact94 h y| ≤ (1917430750325464104961/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded94 exact94
  apply rounded_step rnd hrnd (propagation := (2556574333767285473281/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (9300763245/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error93 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound94 h y hh hy
  · norm_num
  · norm_num
def exact95 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded95 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial95 (h y : ℝ) : exact95 h y = evaluate [] h y := by
  simp only [exact95, evaluate] <;> ring
theorem bound95 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact95 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial95]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error95 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded95 rnd h y - exact95 h y| ≤ (0/1 : ℝ) := by
  simp [rounded95, exact95]
def exact96 (h y : ℝ) : ℝ := exact95 h y * exact11 h y
def rounded96 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded95 rnd h y * rounded11 rnd h y)
theorem polynomial96 (h y : ℝ) : exact96 h y = evaluate [] h y := by
  simp only [exact96, polynomial95, polynomial11, evaluate] <;> ring
theorem bound96 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact96 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial96]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error96 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded96 rnd h y - exact96 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded96 exact96
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound95 h y hh hy) (bound11 h y hh hy)
      (error95 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound96 h y hh hy
  · norm_num
  · norm_num
def exact97 (h y : ℝ) : ℝ := exact94 h y + exact96 h y
def rounded97 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded94 rnd h y + rounded96 rnd h y)
theorem polynomial97 (h y : ℝ) : exact97 h y = evaluate [((609534820015259/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact97, polynomial94, polynomial96, evaluate] <;> ring
theorem bound97 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact97 h y| ≤ (9300763245/1099511627776 : ℝ) := by
  rw [polynomial97]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error97 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded97 rnd h y - exact97 h y| ≤ (1278287166883642736641/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded97 exact97
  apply rounded_step rnd hrnd (propagation := (3834861500650928209923/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (9300763245/1099511627776 : ℝ))
  · convert FindOrb.add_error (error94 rnd hrnd h y hh hy) (error96 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound97 h y hh hy
  · norm_num
  · norm_num
def exact98 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded98 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial98 (h y : ℝ) : exact98 h y = evaluate [] h y := by
  simp only [exact98, evaluate] <;> ring
theorem bound98 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact98 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial98]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error98 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded98 rnd h y - exact98 h y| ≤ (0/1 : ℝ) := by
  simp [rounded98, exact98]
def exact99 (h y : ℝ) : ℝ := exact98 h y * exact21 h y
def rounded99 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded98 rnd h y * rounded21 rnd h y)
theorem polynomial99 (h y : ℝ) : exact99 h y = evaluate [] h y := by
  simp only [exact99, polynomial98, polynomial21, evaluate] <;> ring
theorem bound99 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact99 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial99]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error99 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded99 rnd h y - exact99 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded99 exact99
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound98 h y hh hy) (bound21 h y hh hy)
      (error98 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound99 h y hh hy
  · norm_num
  · norm_num
def exact100 (h y : ℝ) : ℝ := exact97 h y + exact99 h y
def rounded100 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded97 rnd h y + rounded99 rnd h y)
theorem polynomial100 (h y : ℝ) : exact100 h y = evaluate [((609534820015259/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact100, polynomial97, polynomial99, evaluate] <;> ring
theorem bound100 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact100 h y| ≤ (9300763245/1099511627776 : ℝ) := by
  rw [polynomial100]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error100 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded100 rnd h y - exact100 h y| ≤ (3195717917209106841603/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded100 exact100
  apply rounded_step rnd hrnd (propagation := (5113148667534570946565/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (9300763245/1099511627776 : ℝ))
  · convert FindOrb.add_error (error97 rnd hrnd h y hh hy) (error99 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound100 h y hh hy
  · norm_num
  · norm_num
def exact101 (h y : ℝ) : ℝ := (3493426724932065/9007199254740992 : ℝ)
def rounded101 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (3493426724932065/9007199254740992 : ℝ)
theorem polynomial101 (h y : ℝ) : exact101 h y = evaluate [((3493426724932065/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact101, evaluate] <;> ring
theorem bound101 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact101 h y| ≤ (426443692009/1099511627776 : ℝ) := by
  rw [polynomial101]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error101 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded101 rnd h y - exact101 h y| ≤ (0/1 : ℝ) := by
  simp [rounded101, exact101]
def exact102 (h y : ℝ) : ℝ := exact101 h y * exact34 h y
def rounded102 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded101 rnd h y * rounded34 rnd h y)
theorem polynomial102 (h y : ℝ) : exact102 h y = evaluate [((3493426724932065/9007199254740992 : ℝ), 0, 1), ((3493426724932065/72057594037927936 : ℝ), 1, 1), ((251727924746402879102096240735775/83076749736557242056487941267521536 : ℝ), 2, 1), ((20977327062200239051818005494965/166153499473114484112975882535043072 : ℝ), 3, 1)] h y := by
  simp only [exact102, polynomial101, polynomial34, evaluate] <;> ring
theorem bound102 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact102 h y| ≤ (53723541409/274877906944 : ℝ) := by
  rw [polynomial102]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error102 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded102 rnd h y - exact102 h y| ≤ (9312556295221301464107/98079714615416886934934209737619787751599303819750539264 : ℝ) := by
  unfold rounded102 exact102
  apply rounded_step rnd hrnd (propagation := (131354334729392649482438159276914573/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (53723541409/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound101 h y hh hy) (bound34 h y hh hy)
      (error101 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound102 h y hh hy
  · norm_num
  · norm_num
def exact103 (h y : ℝ) : ℝ := exact100 h y + exact102 h y
def rounded103 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded100 rnd h y + rounded102 rnd h y)
theorem polynomial103 (h y : ℝ) : exact103 h y = evaluate [((14583241719743519/36028797018963968 : ℝ), 0, 1), ((3493426724932065/72057594037927936 : ℝ), 1, 1), ((251727924746402879102096240735775/83076749736557242056487941267521536 : ℝ), 2, 1), ((20977327062200239051818005494965/166153499473114484112975882535043072 : ℝ), 3, 1)] h y := by
  simp only [exact103, polynomial100, polynomial102, evaluate] <;> ring
theorem bound103 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact103 h y| ≤ (224194928881/1099511627776 : ℝ) := by
  rw [polynomial103]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error103 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded103 rnd h y - exact103 h y| ≤ (186205452957093145133751/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded103 exact103
  apply rounded_step rnd hrnd (propagation := (77696168278979518554459/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (224194928881/1099511627776 : ℝ))
  · convert FindOrb.add_error (error100 rnd hrnd h y hh hy) (error102 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound103 h y hh hy
  · norm_num
  · norm_num
def exact104 (h y : ℝ) : ℝ := (5184885422623597/144115188075855872 : ℝ)
def rounded104 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (5184885422623597/144115188075855872 : ℝ)
theorem polynomial104 (h y : ℝ) : exact104 h y = evaluate [((5184885422623597/144115188075855872 : ℝ), 0, 0)] h y := by
  simp only [exact104, evaluate] <;> ring
theorem bound104 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact104 h y| ≤ (39557536489/1099511627776 : ℝ) := by
  rw [polynomial104]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error104 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded104 rnd h y - exact104 h y| ≤ (0/1 : ℝ) := by
  simp [rounded104, exact104]
def exact105 (h y : ℝ) : ℝ := exact104 h y * exact50 h y
def rounded105 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded104 rnd h y * rounded50 rnd h y)
theorem polynomial105 (h y : ℝ) : exact105 h y = evaluate [((5184885422623597/144115188075855872 : ℝ), 0, 1), ((25924427113117985/2305843009213693952 : ℝ), 1, 1), ((4670129611457269753649869804412325/2658455991569831745807614120560689152 : ℝ), 2, 1), ((15567098704857565715877430449117825/85070591730234615865843651857942052864 : ℝ), 3, 1), ((2335064805728634682391731553821275/170141183460469231731687303715884105728 : ℝ), 4, 1)] h y := by
  simp only [exact105, polynomial104, polynomial50, evaluate] <;> ring
theorem bound105 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact105 h y| ≤ (1260554343/68719476736 : ℝ) := by
  rw [polynomial105]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error105 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded105 rnd h y - exact105 h y| ≤ (16291719535146485041755/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded105 exact105
  apply rounded_step rnd hrnd (propagation := (7432550840399429512921930463878667/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (1260554343/68719476736 : ℝ))
  · convert FindOrb.mul_error (bound104 h y hh hy) (bound50 h y hh hy)
      (error104 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound105 h y hh hy
  · norm_num
  · norm_num
def exact106 (h y : ℝ) : ℝ := exact103 h y + exact105 h y
def rounded106 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded103 rnd h y + rounded105 rnd h y)
theorem polynomial106 (h y : ℝ) : exact106 h y = evaluate [((63517852301597673/144115188075855872 : ℝ), 0, 1), ((137714082310944065/2305843009213693952 : ℝ), 1, 1), ((12725423203342161884916949507957125/2658455991569831745807614120560689152 : ℝ), 2, 1), ((26307490160704088110408249262539905/85070591730234615865843651857942052864 : ℝ), 3, 1), ((2335064805728634682391731553821275/170141183460469231731687303715884105728 : ℝ), 4, 1)] h y := by
  simp only [exact106, polynomial103, polynomial105, evaluate] <;> ring
theorem bound106 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact106 h y| ≤ (244363798369/1099511627776 : ℝ) := by
  rw [polynomial106]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error106 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded106 rnd h y - exact106 h y| ≤ (236082277206517810662675/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded106 exact106
  apply rounded_step rnd hrnd (propagation := (101248586246119815087753/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (244363798369/1099511627776 : ℝ))
  · convert FindOrb.add_error (error103 rnd hrnd h y hh hy) (error105 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound106 h y hh hy
  · norm_num
  · norm_num
def exact107 (h y : ℝ) : ℝ := (1774149966689521/9007199254740992 : ℝ)
def rounded107 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1774149966689521/9007199254740992 : ℝ)
theorem polynomial107 (h y : ℝ) : exact107 h y = evaluate [((1774149966689521/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact107, evaluate] <;> ring
theorem bound107 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact107 h y| ≤ (27071380107/137438953472 : ℝ) := by
  rw [polynomial107]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error107 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded107 rnd h y - exact107 h y| ≤ (0/1 : ℝ) := by
  simp [rounded107, exact107]
def exact108 (h y : ℝ) : ℝ := exact107 h y * exact69 h y
def rounded108 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded107 rnd h y * rounded69 rnd h y)
theorem polynomial108 (h y : ℝ) : exact108 h y = evaluate [((1774149966689521/9007199254740992 : ℝ), 0, 1), ((95880733546587654223457246579471/1298074214633706907132624082305024 : ℝ), 1, 1), ((71910550159940740224055443262223/5192296858534827628530496329220096 : ℝ), 2, 1), ((10363402460938127486442118094943581760054704551755/5986310706507378352962293074805895248510699696029696 : ℝ), 3, 1), ((31090207382814382137060555419911129646484202466223/191561942608236107294793378393788647952342390272950272 : ℝ), 4, 1), ((4318084358724219429793990543557088586919369427125/383123885216472214589586756787577295904684780545900544 : ℝ), 5, 1)] h y := by
  simp only [exact108, polynomial107, polynomial69, evaluate] <;> ring
theorem bound108 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact108 h y| ≤ (110853437543/1099511627776 : ℝ) := by
  rw [polynomial108]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error108 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded108 rnd h y - exact108 h y| ≤ (78638859333159345766663/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded108 exact108
  apply rounded_step rnd hrnd (propagation := (136157504642585204518096124333931/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ)) (magnitude := (110853437543/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound107 h y hh hy) (bound69 h y hh hy)
      (error107 rnd hrnd h y hh hy) (error69 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound108 h y hh hy
  · norm_num
  · norm_num
def exact109 (h y : ℝ) : ℝ := exact106 h y + exact108 h y
def rounded109 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded106 rnd h y + rounded108 rnd h y)
theorem polynomial109 (h y : ℝ) : exact109 h y = evaluate [((91904251768630009/144115188075855872 : ℝ), 0, 1), ((173406869768992342447424657492751/1298074214633706907132624082305024 : ℝ), 1, 1), ((49543624885231820879633336458215301/2658455991569831745807614120560689152 : ℝ), 2, 1), ((12214627506013126254348211032835012321763914233675/5986310706507378352962293074805895248510699696029696 : ℝ), 3, 1), ((33719256630055741834336030902151387518591450491823/191561942608236107294793378393788647952342390272950272 : ℝ), 4, 1), ((4318084358724219429793990543557088586919369427125/383123885216472214589586756787577295904684780545900544 : ℝ), 5, 1)] h y := by
  simp only [exact109, polynomial106, polynomial108, evaluate] <;> ring
theorem bound109 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact109 h y| ≤ (355217235911/1099511627776 : ℝ) := by
  rw [polynomial109]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error109 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded109 rnd h y - exact109 h y| ≤ (363541821698501532962331/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded109 exact109
  apply rounded_step rnd hrnd (propagation := (157360568269838578214669/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (355217235911/1099511627776 : ℝ))
  · convert FindOrb.add_error (error106 rnd hrnd h y hh hy) (error108 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound109 h y hh hy
  · norm_num
  · norm_num
def exact110 (h y : ℝ) : ℝ := (-777834041042407/4503599627370496 : ℝ)
def rounded110 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-777834041042407/4503599627370496 : ℝ)
theorem polynomial110 (h y : ℝ) : exact110 h y = evaluate [((-777834041042407/4503599627370496 : ℝ), 0, 0)] h y := by
  simp only [exact110, evaluate] <;> ring
theorem bound110 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact110 h y| ≤ (189900888927/1099511627776 : ℝ) := by
  rw [polynomial110]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error110 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded110 rnd h y - exact110 h y| ≤ (0/1 : ℝ) := by
  simp [rounded110, exact110]
def exact111 (h y : ℝ) : ℝ := exact110 h y * exact91 h y
def rounded111 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded110 rnd h y * rounded91 rnd h y)
theorem polynomial111 (h y : ℝ) : exact111 h y = evaluate [((-777834041042407/4503599627370496 : ℝ), 0, 1), ((-66137642478811390630059764631127/2596148429267413814265248164610048 : ℝ), 1, 1), ((-702943610373661774640089818050518361390932147657/374144419156711147060143317175368453031918731001856 : ℝ), 2, 1), ((-552982306827280429824918923702193080370260283509/5986310706507378352962293074805895248510699696029696 : ℝ), 3, 1), ((-5877369749888765303340318665987319946308136869460767647083312365/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 4, 1), ((-8161231326547638761774957737930248324671273041040812809530222121/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 5, 1), ((-14020169221671611659703094981508200852970268980953465902967769875/110427941548649020598956093796432407239217743554726184882600387580788736 : ℝ), 6, 1)] h y := by
  simp only [exact111, polynomial110, polynomial91, evaluate] <;> ring
theorem bound111 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact111 h y| ≤ (95829815999/1099511627776 : ℝ) := by
  rw [polynomial111]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error111 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded111 rnd h y - exact111 h y| ≤ (67057008869643299561577/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded111 exact111
  apply rounded_step rnd hrnd (propagation := (59248568619787401730851605854201167/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (95829815999/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound110 h y hh hy) (bound91 h y hh hy)
      (error110 rnd hrnd h y hh hy) (error91 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound111 h y hh hy
  · norm_num
  · norm_num
def exact112 (h y : ℝ) : ℝ := exact109 h y + exact111 h y
def rounded112 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded109 rnd h y + rounded111 rnd h y)
theorem polynomial112 (h y : ℝ) : exact112 h y = evaluate [((67013562455272985/144115188075855872 : ℝ), 0, 1), ((280676097059173294264789550354375/2596148429267413814265248164610048 : ℝ), 1, 1), ((6269701719992390136845108765655874241537682326071/374144419156711147060143317175368453031918731001856 : ℝ), 2, 1), ((5830822599592922912261646054566409620696826975083/2993155353253689176481146537402947624255349848014848 : ℝ), 3, 1), ((297838693438769565934126034714499928916460648071441407135795596051/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 4, 1), ((614140308158404738916825263083387695153144929332547423275177105879/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 5, 1), ((-14020169221671611659703094981508200852970268980953465902967769875/110427941548649020598956093796432407239217743554726184882600387580788736 : ℝ), 6, 1)] h y := by
  simp only [exact112, polynomial109, polynomial111, evaluate] <;> ring
theorem bound112 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact112 h y| ≤ (259387419913/1099511627776 : ℝ) := by
  rw [polynomial112]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error112 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded112 rnd h y - exact112 h y| ≤ (466248766104789765811845/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded112 exact112
  apply rounded_step rnd hrnd (propagation := (107649707642036208130977/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (259387419913/1099511627776 : ℝ))
  · convert FindOrb.add_error (error109 rnd hrnd h y hh hy) (error111 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound112 h y hh hy
  · norm_num
  · norm_num
def exact113 (h y : ℝ) : ℝ := exact112 h y * exact0 h y
def rounded113 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded112 rnd h y * rounded0 rnd h y)
theorem polynomial113 (h y : ℝ) : exact113 h y = evaluate [((67013562455272985/144115188075855872 : ℝ), 1, 1), ((280676097059173294264789550354375/2596148429267413814265248164610048 : ℝ), 2, 1), ((6269701719992390136845108765655874241537682326071/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((5830822599592922912261646054566409620696826975083/2993155353253689176481146537402947624255349848014848 : ℝ), 4, 1), ((297838693438769565934126034714499928916460648071441407135795596051/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 5, 1), ((614140308158404738916825263083387695153144929332547423275177105879/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 6, 1), ((-14020169221671611659703094981508200852970268980953465902967769875/110427941548649020598956093796432407239217743554726184882600387580788736 : ℝ), 7, 1)] h y := by
  simp only [exact113, polynomial112, polynomial0, evaluate] <;> ring
theorem bound113 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact113 h y| ≤ (16211713745/1099511627776 : ℝ) := by
  rw [polynomial113]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error113 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded113 rnd h y - exact113 h y| ≤ (31368668852649798235881/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded113 exact113
  apply rounded_step rnd hrnd (propagation := (466248766104789765811845/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (16211713745/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound112 h y hh hy) (bound0 h y hh hy)
      (error112 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound113 h y hh hy
  · norm_num
  · norm_num
def exact114 (h y : ℝ) : ℝ := exact113 h y + exact3 h y
def rounded114 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded113 rnd h y + rounded3 rnd h y)
theorem polynomial114 (h y : ℝ) : exact114 h y = evaluate [((1/1 : ℝ), 0, 1), ((67013562455272985/144115188075855872 : ℝ), 1, 1), ((280676097059173294264789550354375/2596148429267413814265248164610048 : ℝ), 2, 1), ((6269701719992390136845108765655874241537682326071/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((5830822599592922912261646054566409620696826975083/2993155353253689176481146537402947624255349848014848 : ℝ), 4, 1), ((297838693438769565934126034714499928916460648071441407135795596051/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 5, 1), ((614140308158404738916825263083387695153144929332547423275177105879/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 6, 1), ((-14020169221671611659703094981508200852970268980953465902967769875/110427941548649020598956093796432407239217743554726184882600387580788736 : ℝ), 7, 1)] h y := by
  simp only [exact114, polynomial113, polynomial3, evaluate] <;> ring
theorem bound114 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact114 h y| ≤ (565967527633/1099511627776 : ℝ) := by
  rw [polynomial114]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error114 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded114 rnd h y - exact114 h y| ≤ (184712517275578882946795/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded114 exact114
  apply rounded_step rnd hrnd (propagation := (53463266289282060827509/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (565967527633/1099511627776 : ℝ))
  · convert FindOrb.add_error (error113 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound114 h y hh hy
  · norm_num
  · norm_num
def exact115 (h y : ℝ) : ℝ := exact114 h y + exact2 h y
def rounded115 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded114 rnd h y + rounded2 rnd h y)
theorem polynomial115 (h y : ℝ) : exact115 h y = evaluate [((1/1 : ℝ), 0, 1), ((67013562455272985/144115188075855872 : ℝ), 1, 1), ((280676097059173294264789550354375/2596148429267413814265248164610048 : ℝ), 2, 1), ((6269701719992390136845108765655874241537682326071/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((5830822599592922912261646054566409620696826975083/2993155353253689176481146537402947624255349848014848 : ℝ), 4, 1), ((297838693438769565934126034714499928916460648071441407135795596051/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 5, 1), ((614140308158404738916825263083387695153144929332547423275177105879/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 6, 1), ((-14020169221671611659703094981508200852970268980953465902967769875/110427941548649020598956093796432407239217743554726184882600387580788736 : ℝ), 7, 1)] h y := by
  simp only [exact115, polynomial114, polynomial2, evaluate] <;> ring
theorem bound115 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact115 h y| ≤ (565967527633/1099511627776 : ℝ) := by
  rw [polynomial115]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error115 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded115 rnd h y - exact115 h y| ≤ (65624625493148411059643/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded115 exact115
  apply rounded_step rnd hrnd (propagation := (184712517275578882946795/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (565967527633/1099511627776 : ℝ))
  · convert FindOrb.add_error (error114 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound115 h y hh hy
  · norm_num
  · norm_num
def exact116 (h y : ℝ) : ℝ := exact115 h y + exact2 h y
def rounded116 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded115 rnd h y + rounded2 rnd h y)
theorem polynomial116 (h y : ℝ) : exact116 h y = evaluate [((1/1 : ℝ), 0, 1), ((67013562455272985/144115188075855872 : ℝ), 1, 1), ((280676097059173294264789550354375/2596148429267413814265248164610048 : ℝ), 2, 1), ((6269701719992390136845108765655874241537682326071/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((5830822599592922912261646054566409620696826975083/2993155353253689176481146537402947624255349848014848 : ℝ), 4, 1), ((297838693438769565934126034714499928916460648071441407135795596051/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 5, 1), ((614140308158404738916825263083387695153144929332547423275177105879/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 6, 1), ((-14020169221671611659703094981508200852970268980953465902967769875/110427941548649020598956093796432407239217743554726184882600387580788736 : ℝ), 7, 1)] h y := by
  simp only [exact116, polynomial115, polynomial2, evaluate] <;> ring
theorem bound116 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact116 h y| ≤ (565967527633/1099511627776 : ℝ) := by
  rw [polynomial116]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error116 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded116 rnd h y - exact116 h y| ≤ (340284486669608405530349/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded116 exact116
  apply rounded_step rnd hrnd (propagation := (65624625493148411059643/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (565967527633/1099511627776 : ℝ))
  · convert FindOrb.add_error (error115 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound116 h y hh hy
  · norm_num
  · norm_num
def exact117 (h y : ℝ) : ℝ := (2489436872650737/36028797018963968 : ℝ)
def rounded117 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (2489436872650737/36028797018963968 : ℝ)
theorem polynomial117 (h y : ℝ) : exact117 h y = evaluate [((2489436872650737/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact117, evaluate] <;> ring
theorem bound117 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact117 h y| ≤ (75971584249/1099511627776 : ℝ) := by
  rw [polynomial117]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error117 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded117 rnd h y - exact117 h y| ≤ (0/1 : ℝ) := by
  simp [rounded117, exact117]
def exact118 (h y : ℝ) : ℝ := exact117 h y * exact4 h y
def rounded118 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded117 rnd h y * rounded4 rnd h y)
theorem polynomial118 (h y : ℝ) : exact118 h y = evaluate [((2489436872650737/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact118, polynomial117, polynomial4, evaluate] <;> ring
theorem bound118 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact118 h y| ≤ (37985792125/1099511627776 : ℝ) := by
  rw [polynomial118]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error118 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded118 rnd h y - exact118 h y| ≤ (10441455032861158539265/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded118 exact118
  apply rounded_step rnd hrnd (propagation := (5740250609727761066192800334373113/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (37985792125/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound117 h y hh hy) (bound4 h y hh hy)
      (error117 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound118 h y hh hy
  · norm_num
  · norm_num
def exact119 (h y : ℝ) : ℝ := exact2 h y + exact118 h y
def rounded119 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded118 rnd h y)
theorem polynomial119 (h y : ℝ) : exact119 h y = evaluate [((2489436872650737/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact119, polynomial2, polynomial118, evaluate] <;> ring
theorem bound119 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact119 h y| ≤ (37985792125/1099511627776 : ℝ) := by
  rw [polynomial119]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error119 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded119 rnd h y - exact119 h y| ≤ (7831091274663048773633/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded119 exact119
  apply rounded_step rnd hrnd (propagation := (10441455032861158539265/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (37985792125/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error118 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound119 h y hh hy
  · norm_num
  · norm_num
def exact120 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded120 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial120 (h y : ℝ) : exact120 h y = evaluate [] h y := by
  simp only [exact120, evaluate] <;> ring
theorem bound120 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact120 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial120]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error120 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded120 rnd h y - exact120 h y| ≤ (0/1 : ℝ) := by
  simp [rounded120, exact120]
def exact121 (h y : ℝ) : ℝ := exact120 h y * exact11 h y
def rounded121 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded120 rnd h y * rounded11 rnd h y)
theorem polynomial121 (h y : ℝ) : exact121 h y = evaluate [] h y := by
  simp only [exact121, polynomial120, polynomial11, evaluate] <;> ring
theorem bound121 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact121 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial121]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error121 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded121 rnd h y - exact121 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded121 exact121
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound120 h y hh hy) (bound11 h y hh hy)
      (error120 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound121 h y hh hy
  · norm_num
  · norm_num
def exact122 (h y : ℝ) : ℝ := exact119 h y + exact121 h y
def rounded122 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded119 rnd h y + rounded121 rnd h y)
theorem polynomial122 (h y : ℝ) : exact122 h y = evaluate [((2489436872650737/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact122, polynomial119, polynomial121, evaluate] <;> ring
theorem bound122 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact122 h y| ≤ (37985792125/1099511627776 : ℝ) := by
  rw [polynomial122]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error122 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded122 rnd h y - exact122 h y| ≤ (5220727516447759138817/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded122 exact122
  apply rounded_step rnd hrnd (propagation := (15662182549326097547267/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (37985792125/1099511627776 : ℝ))
  · convert FindOrb.add_error (error119 rnd hrnd h y hh hy) (error121 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound122 h y hh hy
  · norm_num
  · norm_num
def exact123 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded123 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial123 (h y : ℝ) : exact123 h y = evaluate [] h y := by
  simp only [exact123, evaluate] <;> ring
theorem bound123 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact123 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial123]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error123 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded123 rnd h y - exact123 h y| ≤ (0/1 : ℝ) := by
  simp [rounded123, exact123]
def exact124 (h y : ℝ) : ℝ := exact123 h y * exact21 h y
def rounded124 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded123 rnd h y * rounded21 rnd h y)
theorem polynomial124 (h y : ℝ) : exact124 h y = evaluate [] h y := by
  simp only [exact124, polynomial123, polynomial21, evaluate] <;> ring
theorem bound124 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact124 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial124]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error124 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded124 rnd h y - exact124 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded124 exact124
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound123 h y hh hy) (bound21 h y hh hy)
      (error123 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound124 h y hh hy
  · norm_num
  · norm_num
def exact125 (h y : ℝ) : ℝ := exact122 h y + exact124 h y
def rounded125 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded122 rnd h y + rounded124 rnd h y)
theorem polynomial125 (h y : ℝ) : exact125 h y = evaluate [((2489436872650737/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact125, polynomial122, polynomial124, evaluate] <;> ring
theorem bound125 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact125 h y| ≤ (37985792125/1099511627776 : ℝ) := by
  rw [polynomial125]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error125 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded125 rnd h y - exact125 h y| ≤ (13051818791127987781635/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded125 exact125
  apply rounded_step rnd hrnd (propagation := (20882910065791036555269/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (37985792125/1099511627776 : ℝ))
  · convert FindOrb.add_error (error122 rnd hrnd h y hh hy) (error124 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound125 h y hh hy
  · norm_num
  · norm_num
def exact126 (h y : ℝ) : ℝ := (-5712797903313117/9007199254740992 : ℝ)
def rounded126 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-5712797903313117/9007199254740992 : ℝ)
theorem polynomial126 (h y : ℝ) : exact126 h y = evaluate [((-5712797903313117/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact126, evaluate] <;> ring
theorem bound126 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact126 h y| ≤ (697363025307/1099511627776 : ℝ) := by
  rw [polynomial126]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error126 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded126 rnd h y - exact126 h y| ≤ (0/1 : ℝ) := by
  simp [rounded126, exact126]
def exact127 (h y : ℝ) : ℝ := exact126 h y * exact34 h y
def rounded127 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded126 rnd h y * rounded34 rnd h y)
theorem polynomial127 (h y : ℝ) : exact127 h y = evaluate [((-5712797903313117/9007199254740992 : ℝ), 0, 1), ((-5712797903313117/72057594037927936 : ℝ), 1, 1), ((-411650472137662467205494186223395/83076749736557242056487941267521536 : ℝ), 2, 1), ((-34304206011471870838925039690337/166153499473114484112975882535043072 : ℝ), 3, 1)] h y := by
  simp only [exact127, polynomial126, polynomial34, evaluate] <;> ring
theorem bound127 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact127 h y| ≤ (175708127799/549755813888 : ℝ) := by
  rw [polynomial127]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error127 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded127 rnd h y - exact127 h y| ≤ (121830526338169643938389/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded127 exact127
  apply rounded_step rnd hrnd (propagation := (214803637550685970704439752349647879/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (175708127799/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound126 h y hh hy) (bound34 h y hh hy)
      (error126 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound127 h y hh hy
  · norm_num
  · norm_num
def exact128 (h y : ℝ) : ℝ := exact125 h y + exact127 h y
def rounded128 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded125 rnd h y + rounded127 rnd h y)
theorem polynomial128 (h y : ℝ) : exact128 h y = evaluate [((-20361754740601731/36028797018963968 : ℝ), 0, 1), ((-5712797903313117/72057594037927936 : ℝ), 1, 1), ((-411650472137662467205494186223395/83076749736557242056487941267521536 : ℝ), 2, 1), ((-34304206011471870838925039690337/166153499473114484112975882535043072 : ℝ), 3, 1)] h y := by
  simp only [exact128, polynomial125, polynomial127, evaluate] <;> ring
theorem bound128 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact128 h y| ≤ (313430463473/1099511627776 : ℝ) := by
  rw [polynomial128]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error128 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded128 rnd h y - exact128 h y| ≤ (312842245144568305968305/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded128 exact128
  apply rounded_step rnd hrnd (propagation := (16860293141162203965003/98079714615416886934934209737619787751599303819750539264 : ℝ)) (magnitude := (313430463473/1099511627776 : ℝ))
  · convert FindOrb.add_error (error125 rnd hrnd h y hh hy) (error127 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound128 h y hh hy
  · norm_num
  · norm_num
def exact129 (h y : ℝ) : ℝ := (-5807754717716435/36028797018963968 : ℝ)
def rounded129 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-5807754717716435/36028797018963968 : ℝ)
theorem polynomial129 (h y : ℝ) : exact129 h y = evaluate [((-5807754717716435/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact129, evaluate] <;> ring
theorem bound129 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact129 h y| ≤ (177238608329/1099511627776 : ℝ) := by
  rw [polynomial129]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error129 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded129 rnd h y - exact129 h y| ≤ (0/1 : ℝ) := by
  simp [rounded129, exact129]
def exact130 (h y : ℝ) : ℝ := exact129 h y * exact50 h y
def rounded130 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded129 rnd h y * rounded50 rnd h y)
theorem polynomial130 (h y : ℝ) : exact130 h y = evaluate [((-5807754717716435/36028797018963968 : ℝ), 0, 1), ((-29038773588582175/576460752303423488 : ℝ), 1, 1), ((-5231160396513395515126830603262875/664613997892457936451903530140172288 : ℝ), 2, 1), ((-17437201321711318238562234067965375/21267647932558653966460912964485513216 : ℝ), 3, 1), ((-2615580198256697539772613387265125/42535295865117307932921825928971026432 : ℝ), 4, 1)] h y := by
  simp only [exact130, polynomial129, polynomial50, evaluate] <;> ring
theorem bound130 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact130 h y| ≤ (22591790825/274877906944 : ℝ) := by
  rw [polynomial130]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error130 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded130 rnd h y - exact130 h y| ≤ (72995488445093327329521/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded130 exact130
  apply rounded_step rnd hrnd (propagation := (33301744350365535659932568604246187/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (22591790825/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound129 h y hh hy) (bound50 h y hh hy)
      (error129 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound130 h y hh hy
  · norm_num
  · norm_num
def exact131 (h y : ℝ) : ℝ := exact128 h y + exact130 h y
def rounded131 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded128 rnd h y + rounded130 rnd h y)
theorem polynomial131 (h y : ℝ) : exact131 h y = evaluate [((-13084754729159083/18014398509481984 : ℝ), 0, 1), ((-74741156815087111/576460752303423488 : ℝ), 1, 1), ((-8524364173614695252770784093050035/664613997892457936451903530140172288 : ℝ), 2, 1), ((-21828139691179717705944639148328511/21267647932558653966460912964485513216 : ℝ), 3, 1), ((-2615580198256697539772613387265125/42535295865117307932921825928971026432 : ℝ), 4, 1)] h y := by
  simp only [exact131, polynomial128, polynomial130, evaluate] <;> ring
theorem bound131 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact131 h y| ≤ (403797626773/1099511627776 : ℝ) := by
  rw [polynomial131]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error131 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded131 rnd h y - exact131 h y| ≤ (441335256827820001803683/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded131 exact131
  apply rounded_step rnd hrnd (propagation := (192918866794830816648913/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (403797626773/1099511627776 : ℝ))
  · convert FindOrb.add_error (error128 rnd hrnd h y hh hy) (error130 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound131 h y hh hy
  · norm_num
  · norm_num
def exact132 (h y : ℝ) : ℝ := (4995403856108555/36028797018963968 : ℝ)
def rounded132 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (4995403856108555/36028797018963968 : ℝ)
theorem polynomial132 (h y : ℝ) : exact132 h y = evaluate [((4995403856108555/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact132, evaluate] <;> ring
theorem bound132 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact132 h y| ≤ (152447627445/1099511627776 : ℝ) := by
  rw [polynomial132]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error132 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded132 rnd h y - exact132 h y| ≤ (0/1 : ℝ) := by
  simp [rounded132, exact132]
def exact133 (h y : ℝ) : ℝ := exact132 h y * exact69 h y
def rounded133 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded132 rnd h y * rounded69 rnd h y)
theorem polynomial133 (h y : ℝ) : exact133 h y = evaluate [((4995403856108555/36028797018963968 : ℝ), 0, 1), ((269967587339227520403577506210805/5192296858534827628530496329220096 : ℝ), 1, 1), ((202475690504420639053832165630965/20769187434139310514121985316880384 : ℝ), 2, 1), ((29179822217833365717786792054356243700039823406025/23945242826029513411849172299223580994042798784118784 : ℝ), 3, 1), ((87539466653500096245969318717331787382667189450965/766247770432944429179173513575154591809369561091801088 : ℝ), 4, 1), ((12158259257430568046073252060935094644856206904375/1532495540865888858358347027150309183618739122183602176 : ℝ), 5, 1)] h y := by
  simp only [exact133, polynomial132, polynomial69, evaluate] <;> ring
theorem bound133 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact133 h y| ≤ (39015704687/549755813888 : ℝ) := by
  rw [polynomial133]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error133 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded133 rnd h y - exact133 h y| ≤ (55355081099218504073673/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded133 exact133
  apply rounded_step rnd hrnd (propagation := (766746595834855902643835192009685/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ)) (magnitude := (39015704687/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound132 h y hh hy) (bound69 h y hh hy)
      (error132 rnd hrnd h y hh hy) (error69 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound133 h y hh hy
  · norm_num
  · norm_num
def exact134 (h y : ℝ) : ℝ := exact131 h y + exact133 h y
def rounded134 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded131 rnd h y + rounded133 rnd h y)
theorem polynomial134 (h y : ℝ) : exact134 h y = evaluate [((-21174105602209611/36028797018963968 : ℝ), 0, 1), ((-403240904624104721011362716343307/5192296858534827628530496329220096 : ℝ), 1, 1), ((-2045142077473234803048154792859155/664613997892457936451903530140172288 : ℝ), 2, 1), ((4603521772986338144416568743795357490298694153161/23945242826029513411849172299223580994042798784118784 : ℝ), 3, 1), ((40421362628594051879949027807739716704120970442965/766247770432944429179173513575154591809369561091801088 : ℝ), 4, 1), ((12158259257430568046073252060935094644856206904375/1532495540865888858358347027150309183618739122183602176 : ℝ), 5, 1)] h y := by
  simp only [exact134, polynomial131, polynomial133, evaluate] <;> ring
theorem bound134 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact134 h y| ≤ (81441567475/274877906944 : ℝ) := by
  rw [polynomial134]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error134 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded134 rnd h y - exact134 h y| ≤ (541463313138571599970157/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded134 exact134
  apply rounded_step rnd hrnd (propagation := (124172584481759626469339/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (81441567475/274877906944 : ℝ))
  · convert FindOrb.add_error (error131 rnd hrnd h y hh hy) (error133 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound134 h y hh hy
  · norm_num
  · norm_num
def exact135 (h y : ℝ) : ℝ := (4237565755553669/4503599627370496 : ℝ)
def rounded135 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (4237565755553669/4503599627370496 : ℝ)
theorem polynomial135 (h y : ℝ) : exact135 h y = evaluate [((4237565755553669/4503599627370496 : ℝ), 0, 0)] h y := by
  simp only [exact135, evaluate] <;> ring
theorem bound135 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact135 h y| ≤ (129320244005/137438953472 : ℝ) := by
  rw [polynomial135]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error135 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded135 rnd h y - exact135 h y| ≤ (0/1 : ℝ) := by
  simp [rounded135, exact135]
def exact136 (h y : ℝ) : ℝ := exact135 h y * exact91 h y
def rounded136 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded135 rnd h y * rounded91 rnd h y)
theorem polynomial136 (h y : ℝ) : exact136 h y = evaluate [((4237565755553669/4503599627370496 : ℝ), 0, 1), ((360311575648799730819355469501909/2596148429267413814265248164610048 : ℝ), 1, 1), ((3829569823676937029896174389173402466680503905419/374144419156711147060143317175368453031918731001856 : ℝ), 2, 1), ((3012594927959189557938806195098233425125600093903/5986310706507378352962293074805895248510699696029696 : ℝ), 3, 1), ((32019350492141574637510672448002781711220940199510486220323446455/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 4, 1), ((44461610790629608934212534298618479996652264090642497901552699307/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 5, 1), ((76380546293915784885177276045111980816843939277260879461125431625/110427941548649020598956093796432407239217743554726184882600387580788736 : ℝ), 6, 1)] h y := by
  simp only [exact136, polynomial135, polynomial91, evaluate] <;> ring
theorem bound136 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact136 h y| ≤ (130517927093/274877906944 : ℝ) := by
  rw [polynomial136]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error136 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded136 rnd h y - exact136 h y| ≤ (365320196161900333572637/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded136 exact136
  apply rounded_step rnd hrnd (propagation := (40347569693595617926207649897439605/215679573337205118357336120696157045389097155380324579848828881993728 : ℝ)) (magnitude := (130517927093/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound135 h y hh hy) (bound91 h y hh hy)
      (error135 rnd hrnd h y hh hy) (error91 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound136 h y hh hy
  · norm_num
  · norm_num
def exact137 (h y : ℝ) : ℝ := exact134 h y + exact136 h y
def rounded137 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded134 rnd h y + rounded136 rnd h y)
theorem polynomial137 (h y : ℝ) : exact137 h y = evaluate [((12726420442219741/36028797018963968 : ℝ), 0, 1), ((317382246673494740627348222660511/5192296858534827628530496329220096 : ℝ), 1, 1), ((2678257186423414239817847890454792231721712594059/374144419156711147060143317175368453031918731001856 : ℝ), 2, 1), ((16653901484823096376171793524188291190801094528773/23945242826029513411849172299223580994042798784118784 : ℝ), 3, 1), ((123040167328113507012211008577634187145431543164423087139969326775/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 4, 1), ((482509065680535126154489434579436312871470821760392257112499259307/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 5, 1), ((76380546293915784885177276045111980816843939277260879461125431625/110427941548649020598956093796432407239217743554726184882600387580788736 : ℝ), 6, 1)] h y := by
  simp only [exact137, polynomial134, polynomial136, evaluate] <;> ring
theorem bound137 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact137 h y| ≤ (49076372743/274877906944 : ℝ) := by
  rw [polynomial137]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error137 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded137 rnd h y - exact137 h y| ≤ (933763530540470757597579/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded137 exact137
  apply rounded_step rnd hrnd (propagation := (453391754650235966771397/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (49076372743/274877906944 : ℝ))
  · convert FindOrb.add_error (error134 rnd hrnd h y hh hy) (error136 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound137 h y hh hy
  · norm_num
  · norm_num
def exact138 (h y : ℝ) : ℝ := (1906250562164287/9007199254740992 : ℝ)
def rounded138 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1906250562164287/9007199254740992 : ℝ)
theorem polynomial138 (h y : ℝ) : exact138 h y = evaluate [((1906250562164287/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact138, evaluate] <;> ring
theorem bound138 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact138 h y| ≤ (232696601827/1099511627776 : ℝ) := by
  rw [polynomial138]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error138 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded138 rnd h y - exact138 h y| ≤ (0/1 : ℝ) := by
  simp [rounded138, exact138]
def exact139 (h y : ℝ) : ℝ := exact138 h y * exact116 h y
def rounded139 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded138 rnd h y * rounded116 rnd h y)
theorem polynomial139 (h y : ℝ) : exact139 h y = evaluate [((1906250562164287/9007199254740992 : ℝ), 0, 1), ((127744641102995684654757002886695/1298074214633706907132624082305024 : ℝ), 1, 1), ((535038967805127073405206860169634123767819205625/23384026197294446691258957323460528314494920687616 : ℝ), 2, 1), ((11951622428337890820556635289894508955315837289769812218205226377/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 3, 1), ((11115008858354238625140762009049030051142084990224148359901460821/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ), 4, 1), ((567755176801931223079398944331966762911104211258967968992394059743462181750430637/15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 : ℝ), 5, 1), ((1170705307674707487390081268350934118745747711881243531515214457258986275191543273/497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 : ℝ), 6, 1), ((-26725955460449943846675541626377029848810492407765638253454050844906285759454125/994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 : ℝ), 7, 1)] h y := by
  simp only [exact139, polynomial138, polynomial116, evaluate] <;> ring
theorem bound139 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact139 h y| ≤ (119779288457/1099511627776 : ℝ) := by
  rw [polynomial139]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error139 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded139 rnd h y - exact139 h y| ≤ (88478898770795179648745/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded139 exact139
  apply rounded_step rnd hrnd (propagation := (79183043702462956443707966017347623/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (119779288457/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound138 h y hh hy) (bound116 h y hh hy)
      (error138 rnd hrnd h y hh hy) (error116 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound139 h y hh hy
  · norm_num
  · norm_num
def exact140 (h y : ℝ) : ℝ := exact137 h y + exact139 h y
def rounded140 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded137 rnd h y + rounded139 rnd h y)
theorem polynomial140 (h y : ℝ) : exact140 h y = evaluate [((20351422690876889/36028797018963968 : ℝ), 0, 1), ((828360811085477479246376234207291/5192296858534827628530496329220096 : ℝ), 1, 1), ((11238880671305447414301157653168938212006819884059/374144419156711147060143317175368453031918731001856 : ℝ), 2, 1), ((14295450694628961035720177756095807345884489173644839277149078921/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 3, 1), ((834400734262784779021219777156772110418524982538768582173662819319/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 4, 1), ((703569404827040233961157200834912012790613844258662625622673937927458057004506029/15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 : ℝ), 5, 1), ((1514692707502341535448088509213395110791327040572243689964498958922379406981879273/497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 : ℝ), 6, 1), ((-26725955460449943846675541626377029848810492407765638253454050844906285759454125/994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 : ℝ), 7, 1)] h y := by
  simp only [exact140, polynomial137, polynomial139, evaluate] <;> ring
theorem bound140 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact140 h y| ≤ (79021194857/274877906944 : ℝ) := by
  rw [polynomial140]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error140 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded140 rnd h y - exact140 h y| ≤ (1065684790604278212020341/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded140 exact140
  apply rounded_step rnd hrnd (propagation := (255560607327816484311581/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (79021194857/274877906944 : ℝ))
  · convert FindOrb.add_error (error137 rnd hrnd h y hh hy) (error139 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound140 h y hh hy
  · norm_num
  · norm_num
def exact141 (h y : ℝ) : ℝ := exact140 h y * exact0 h y
def rounded141 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded140 rnd h y * rounded0 rnd h y)
theorem polynomial141 (h y : ℝ) : exact141 h y = evaluate [((20351422690876889/36028797018963968 : ℝ), 1, 1), ((828360811085477479246376234207291/5192296858534827628530496329220096 : ℝ), 2, 1), ((11238880671305447414301157653168938212006819884059/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((14295450694628961035720177756095807345884489173644839277149078921/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 4, 1), ((834400734262784779021219777156772110418524982538768582173662819319/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 5, 1), ((703569404827040233961157200834912012790613844258662625622673937927458057004506029/15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 : ℝ), 6, 1), ((1514692707502341535448088509213395110791327040572243689964498958922379406981879273/497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 : ℝ), 7, 1), ((-26725955460449943846675541626377029848810492407765638253454050844906285759454125/994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 : ℝ), 8, 1)] h y := by
  simp only [exact141, polynomial140, polynomial0, evaluate] <;> ring
theorem bound141 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact141 h y| ≤ (19755298715/1099511627776 : ℝ) := by
  rw [polynomial141]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error141 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded141 rnd h y - exact141 h y| ≤ (8665055874210466829969/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded141 exact141
  apply rounded_step rnd hrnd (propagation := (1065684790604278212020341/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (19755298715/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound140 h y hh hy) (bound0 h y hh hy)
      (error140 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound141 h y hh hy
  · norm_num
  · norm_num
def exact142 (h y : ℝ) : ℝ := exact141 h y + exact3 h y
def rounded142 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded141 rnd h y + rounded3 rnd h y)
theorem polynomial142 (h y : ℝ) : exact142 h y = evaluate [((1/1 : ℝ), 0, 1), ((20351422690876889/36028797018963968 : ℝ), 1, 1), ((828360811085477479246376234207291/5192296858534827628530496329220096 : ℝ), 2, 1), ((11238880671305447414301157653168938212006819884059/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((14295450694628961035720177756095807345884489173644839277149078921/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 4, 1), ((834400734262784779021219777156772110418524982538768582173662819319/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 5, 1), ((703569404827040233961157200834912012790613844258662625622673937927458057004506029/15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 : ℝ), 6, 1), ((1514692707502341535448088509213395110791327040572243689964498958922379406981879273/497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 : ℝ), 7, 1), ((-26725955460449943846675541626377029848810492407765638253454050844906285759454125/994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 : ℝ), 8, 1)] h y := by
  simp only [exact142, polynomial141, polynomial3, evaluate] <;> ring
theorem bound142 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact142 h y| ≤ (569511112603/1099511627776 : ℝ) := by
  rw [polynomial142]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error142 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded142 rnd h y - exact142 h y| ≤ (111575661013214363933253/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded142 exact142
  apply rounded_step rnd hrnd (propagation := (144878310719598058058889/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (569511112603/1099511627776 : ℝ))
  · convert FindOrb.add_error (error141 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound142 h y hh hy
  · norm_num
  · norm_num
def exact143 (h y : ℝ) : ℝ := exact142 h y + exact2 h y
def rounded143 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded142 rnd h y + rounded2 rnd h y)
theorem polynomial143 (h y : ℝ) : exact143 h y = evaluate [((1/1 : ℝ), 0, 1), ((20351422690876889/36028797018963968 : ℝ), 1, 1), ((828360811085477479246376234207291/5192296858534827628530496329220096 : ℝ), 2, 1), ((11238880671305447414301157653168938212006819884059/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((14295450694628961035720177756095807345884489173644839277149078921/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 4, 1), ((834400734262784779021219777156772110418524982538768582173662819319/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 5, 1), ((703569404827040233961157200834912012790613844258662625622673937927458057004506029/15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 : ℝ), 6, 1), ((1514692707502341535448088509213395110791327040572243689964498958922379406981879273/497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 : ℝ), 7, 1), ((-26725955460449943846675541626377029848810492407765638253454050844906285759454125/994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 : ℝ), 8, 1)] h y := by
  simp only [exact143, polynomial142, polynomial2, evaluate] <;> ring
theorem bound143 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact143 h y| ≤ (569511112603/1099511627776 : ℝ) := by
  rw [polynomial143]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error143 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded143 rnd h y - exact143 h y| ≤ (301424333333259397674123/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded143 exact143
  apply rounded_step rnd hrnd (propagation := (111575661013214363933253/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (569511112603/1099511627776 : ℝ))
  · convert FindOrb.add_error (error142 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound143 h y hh hy
  · norm_num
  · norm_num
def exact144 (h y : ℝ) : ℝ := exact143 h y + exact2 h y
def rounded144 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded143 rnd h y + rounded2 rnd h y)
theorem polynomial144 (h y : ℝ) : exact144 h y = evaluate [((1/1 : ℝ), 0, 1), ((20351422690876889/36028797018963968 : ℝ), 1, 1), ((828360811085477479246376234207291/5192296858534827628530496329220096 : ℝ), 2, 1), ((11238880671305447414301157653168938212006819884059/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((14295450694628961035720177756095807345884489173644839277149078921/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 4, 1), ((834400734262784779021219777156772110418524982538768582173662819319/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 5, 1), ((703569404827040233961157200834912012790613844258662625622673937927458057004506029/15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 : ℝ), 6, 1), ((1514692707502341535448088509213395110791327040572243689964498958922379406981879273/497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 : ℝ), 7, 1), ((-26725955460449943846675541626377029848810492407765638253454050844906285759454125/994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 : ℝ), 8, 1)] h y := by
  simp only [exact144, polynomial143, polynomial2, evaluate] <;> ring
theorem bound144 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact144 h y| ≤ (569511112603/1099511627776 : ℝ) := by
  rw [polynomial144]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error144 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded144 rnd h y - exact144 h y| ≤ (94924336160022516870435/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded144 exact144
  apply rounded_step rnd hrnd (propagation := (301424333333259397674123/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (569511112603/1099511627776 : ℝ))
  · convert FindOrb.add_error (error143 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound144 h y hh hy
  · norm_num
  · norm_num
def exact145 (h y : ℝ) : ℝ := (6613337780524577/36028797018963968 : ℝ)
def rounded145 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (6613337780524577/36028797018963968 : ℝ)
theorem polynomial145 (h y : ℝ) : exact145 h y = evaluate [((6613337780524577/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact145, evaluate] <;> ring
theorem bound145 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact145 h y| ≤ (201823052385/1099511627776 : ℝ) := by
  rw [polynomial145]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error145 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded145 rnd h y - exact145 h y| ≤ (0/1 : ℝ) := by
  simp [rounded145, exact145]
def exact146 (h y : ℝ) : ℝ := exact145 h y * exact4 h y
def rounded146 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded145 rnd h y * rounded4 rnd h y)
theorem polynomial146 (h y : ℝ) : exact146 h y = evaluate [((6613337780524577/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact146, polynomial145, polynomial4, evaluate] <;> ring
theorem bound146 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact146 h y| ≤ (100911526193/1099511627776 : ℝ) := by
  rw [polynomial146]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error146 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded146 rnd h y - exact146 h y| ≤ (27738349106387753107457/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded146 exact146
  apply rounded_step rnd hrnd (propagation := (15249318688853897777442319062491745/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (100911526193/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound145 h y hh hy) (bound4 h y hh hy)
      (error145 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound146 h y hh hy
  · norm_num
  · norm_num
def exact147 (h y : ℝ) : ℝ := exact2 h y + exact146 h y
def rounded147 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded146 rnd h y)
theorem polynomial147 (h y : ℝ) : exact147 h y = evaluate [((6613337780524577/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact147, polynomial2, polynomial146, evaluate] <;> ring
theorem bound147 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact147 h y| ≤ (100911526193/1099511627776 : ℝ) := by
  rw [polynomial147]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error147 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded147 rnd h y - exact147 h y| ≤ (20803761829807994699777/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded147 exact147
  apply rounded_step rnd hrnd (propagation := (27738349106387753107457/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (100911526193/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error146 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound147 h y hh hy
  · norm_num
  · norm_num
def exact148 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded148 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial148 (h y : ℝ) : exact148 h y = evaluate [] h y := by
  simp only [exact148, evaluate] <;> ring
theorem bound148 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact148 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial148]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error148 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded148 rnd h y - exact148 h y| ≤ (0/1 : ℝ) := by
  simp [rounded148, exact148]
def exact149 (h y : ℝ) : ℝ := exact148 h y * exact11 h y
def rounded149 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded148 rnd h y * rounded11 rnd h y)
theorem polynomial149 (h y : ℝ) : exact149 h y = evaluate [] h y := by
  simp only [exact149, polynomial148, polynomial11, evaluate] <;> ring
theorem bound149 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact149 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial149]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error149 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded149 rnd h y - exact149 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded149 exact149
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound148 h y hh hy) (bound11 h y hh hy)
      (error148 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound149 h y hh hy
  · norm_num
  · norm_num
def exact150 (h y : ℝ) : ℝ := exact147 h y + exact149 h y
def rounded150 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded147 rnd h y + rounded149 rnd h y)
theorem polynomial150 (h y : ℝ) : exact150 h y = evaluate [((6613337780524577/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact150, polynomial147, polynomial149, evaluate] <;> ring
theorem bound150 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact150 h y| ≤ (100911526193/1099511627776 : ℝ) := by
  rw [polynomial150]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error150 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded150 rnd h y - exact150 h y| ≤ (13869174553211056422913/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded150 exact150
  apply rounded_step rnd hrnd (propagation := (41607523659615989399555/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (100911526193/1099511627776 : ℝ))
  · convert FindOrb.add_error (error147 rnd hrnd h y hh hy) (error149 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound150 h y hh hy
  · norm_num
  · norm_num
def exact151 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded151 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial151 (h y : ℝ) : exact151 h y = evaluate [] h y := by
  simp only [exact151, evaluate] <;> ring
theorem bound151 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact151 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial151]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error151 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded151 rnd h y - exact151 h y| ≤ (0/1 : ℝ) := by
  simp [rounded151, exact151]
def exact152 (h y : ℝ) : ℝ := exact151 h y * exact21 h y
def rounded152 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded151 rnd h y * rounded21 rnd h y)
theorem polynomial152 (h y : ℝ) : exact152 h y = evaluate [] h y := by
  simp only [exact152, polynomial151, polynomial21, evaluate] <;> ring
theorem bound152 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact152 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial152]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error152 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded152 rnd h y - exact152 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded152 exact152
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound151 h y hh hy) (bound21 h y hh hy)
      (error151 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound152 h y hh hy
  · norm_num
  · norm_num
def exact153 (h y : ℝ) : ℝ := exact150 h y + exact152 h y
def rounded153 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded150 rnd h y + rounded152 rnd h y)
theorem polynomial153 (h y : ℝ) : exact153 h y = evaluate [((6613337780524577/36028797018963968 : ℝ), 0, 1)] h y := by
  simp only [exact153, polynomial150, polynomial152, evaluate] <;> ring
theorem bound153 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact153 h y| ≤ (100911526193/1099511627776 : ℝ) := by
  rw [polynomial153]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error153 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded153 rnd h y - exact153 h y| ≤ (34672936383036230991875/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded153 exact153
  apply rounded_step rnd hrnd (propagation := (55476698212844225691653/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (100911526193/1099511627776 : ℝ))
  · convert FindOrb.add_error (error150 rnd hrnd h y hh hy) (error152 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound153 h y hh hy
  · norm_num
  · norm_num
def exact154 (h y : ℝ) : ℝ := (-2779585756146969/1125899906842624 : ℝ)
def rounded154 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-2779585756146969/1125899906842624 : ℝ)
theorem polynomial154 (h y : ℝ) : exact154 h y = evaluate [((-2779585756146969/1125899906842624 : ℝ), 0, 0)] h y := by
  simp only [exact154, evaluate] <;> ring
theorem bound154 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact154 h y| ≤ (678609803747/274877906944 : ℝ) := by
  rw [polynomial154]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error154 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded154 rnd h y - exact154 h y| ≤ (0/1 : ℝ) := by
  simp [rounded154, exact154]
def exact155 (h y : ℝ) : ℝ := exact154 h y * exact34 h y
def rounded155 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded154 rnd h y * rounded34 rnd h y)
theorem polynomial155 (h y : ℝ) : exact155 h y = evaluate [((-2779585756146969/1125899906842624 : ℝ), 0, 1), ((-2779585756146969/9007199254740992 : ℝ), 1, 1), ((-200290262010045244418654090679015/10384593717069655257060992658440192 : ℝ), 2, 1), ((-16690855167503769673324735186509/20769187434139310514121985316880384 : ℝ), 3, 1)] h y := by
  simp only [exact155, polynomial154, polynomial34, evaluate] <;> ring
theorem bound155 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact155 h y| ≤ (1367864412595/1099511627776 : ℝ) := by
  rw [polynomial155]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error155 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded155 rnd h y - exact155 h y| ≤ (474217224420816802696683/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded155 exact155
  apply rounded_step rnd hrnd (propagation := (209027219729984063734754139161608559/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (1367864412595/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound154 h y hh hy) (bound34 h y hh hy)
      (error154 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound155 h y hh hy
  · norm_num
  · norm_num
def exact156 (h y : ℝ) : ℝ := exact153 h y + exact155 h y
def rounded156 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded153 rnd h y + rounded155 rnd h y)
theorem polynomial156 (h y : ℝ) : exact156 h y = evaluate [((-82333406416178431/36028797018963968 : ℝ), 0, 1), ((-2779585756146969/9007199254740992 : ℝ), 1, 1), ((-200290262010045244418654090679015/10384593717069655257060992658440192 : ℝ), 2, 1), ((-16690855167503769673324735186509/20769187434139310514121985316880384 : ℝ), 3, 1)] h y := by
  simp only [exact156, polynomial153, polynomial155, evaluate] <;> ring
theorem bound156 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact156 h y| ≤ (1266952886403/1099511627776 : ℝ) := by
  rw [polynomial156]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error156 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded156 rnd h y - exact156 h y| ≤ (1191909000413264085818333/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded156 exact156
  apply rounded_step rnd hrnd (propagation := (254445080401926516844279/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (1266952886403/1099511627776 : ℝ))
  · convert FindOrb.add_error (error153 rnd hrnd h y hh hy) (error155 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound156 h y hh hy
  · norm_num
  · norm_num
def exact157 (h y : ℝ) : ℝ := (-5247358077709609/18014398509481984 : ℝ)
def rounded157 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-5247358077709609/18014398509481984 : ℝ)
theorem polynomial157 (h y : ℝ) : exact157 h y = evaluate [((-5247358077709609/18014398509481984 : ℝ), 0, 0)] h y := by
  simp only [exact157, evaluate] <;> ring
theorem bound157 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact157 h y| ≤ (320273320173/1099511627776 : ℝ) := by
  rw [polynomial157]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error157 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded157 rnd h y - exact157 h y| ≤ (0/1 : ℝ) := by
  simp [rounded157, exact157]
def exact158 (h y : ℝ) : ℝ := exact157 h y * exact50 h y
def rounded158 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded157 rnd h y * rounded50 rnd h y)
theorem polynomial158 (h y : ℝ) : exact158 h y = evaluate [((-5247358077709609/18014398509481984 : ℝ), 0, 1), ((-26236790388548045/288230376151711744 : ℝ), 1, 1), ((-4726399976690511588198940401953025/332306998946228968225951765070086144 : ℝ), 2, 1), ((-15754666588968371829479182730436525/10633823966279326983230456482242756608 : ℝ), 3, 1), ((-2363199988345255597323542286866175/21267647932558653966460912964485513216 : ℝ), 4, 1)] h y := by
  simp only [exact158, polynomial157, polynomial50, evaluate] <;> ring
theorem bound158 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact158 h y| ≤ (163295072657/1099511627776 : ℝ) := by
  rw [polynomial158]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error158 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded158 rnd h y - exact158 h y| ≤ (65952073485489791180133/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded158 exact158
  apply rounded_step rnd hrnd (propagation := (60176844826302366040613193965144919/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (163295072657/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound157 h y hh hy) (bound50 h y hh hy)
      (error157 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound158 h y hh hy
  · norm_num
  · norm_num
def exact159 (h y : ℝ) : ℝ := exact156 h y + exact158 h y
def rounded159 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded156 rnd h y + rounded158 rnd h y)
theorem polynomial159 (h y : ℝ) : exact159 h y = evaluate [((-92828122571597649/36028797018963968 : ℝ), 0, 1), ((-115183534585251053/288230376151711744 : ℝ), 1, 1), ((-11135688361011959409595871303681505/332306998946228968225951765070086144 : ℝ), 2, 1), ((-24300384434730301902221447145929133/10633823966279326983230456482242756608 : ℝ), 3, 1), ((-2363199988345255597323542286866175/21267647932558653966460912964485513216 : ℝ), 4, 1)] h y := by
  simp only [exact159, polynomial156, polynomial158, evaluate] <;> ring
theorem bound159 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact159 h y| ≤ (357561989765/274877906944 : ℝ) := by
  rw [polynomial159]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error159 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded159 rnd h y - exact159 h y| ≤ (190048116260364246129365/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded159 exact159
  apply rounded_step rnd hrnd (propagation := (1323813147384243668178599/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (357561989765/274877906944 : ℝ))
  · convert FindOrb.add_error (error156 rnd hrnd h y hh hy) (error158 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound159 h y hh hy
  · norm_num
  · norm_num
def exact160 (h y : ℝ) : ℝ := (-7630328579663297/288230376151711744 : ℝ)
def rounded160 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-7630328579663297/288230376151711744 : ℝ)
theorem polynomial160 (h y : ℝ) : exact160 h y = evaluate [((-7630328579663297/288230376151711744 : ℝ), 0, 0)] h y := by
  simp only [exact160, evaluate] <;> ring
theorem bound160 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact160 h y| ≤ (29107393569/1099511627776 : ℝ) := by
  rw [polynomial160]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error160 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded160 rnd h y - exact160 h y| ≤ (0/1 : ℝ) := by
  simp [rounded160, exact160]
def exact161 (h y : ℝ) : ℝ := exact160 h y * exact69 h y
def rounded161 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded160 rnd h y * rounded69 rnd h y)
theorem polynomial161 (h y : ℝ) : exact161 h y = evaluate [((-7630328579663297/288230376151711744 : ℝ), 0, 1), ((-412367339377032836836565242960447/41538374868278621028243970633760768 : ℝ), 1, 1), ((-309275504532774625719841787304511/166153499473114484112975882535043072 : ℝ), 2, 1), ((-44571297502996031084733160334733141412029198943035/191561942608236107294793378393788647952342390272950272 : ℝ), 3, 1), ((-133713892508988091868187034764727944656789736332511/6129982163463555433433388108601236734474956488734408704 : ℝ), 4, 1), ((-18571373959581678086579604537301558874088250621125/12259964326927110866866776217202473468949912977468817408 : ℝ), 5, 1)] h y := by
  simp only [exact161, polynomial160, polynomial69, evaluate] <;> ring
theorem bound161 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact161 h y| ≤ (7449413879/549755813888 : ℝ) := by
  rw [polynomial161]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error161 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded161 rnd h y - exact161 h y| ≤ (10569151902240969104549/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded161 exact161
  apply rounded_step rnd hrnd (propagation := (146397784647111054858810227024577/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ)) (magnitude := (7449413879/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound160 h y hh hy) (bound69 h y hh hy)
      (error160 rnd hrnd h y hh hy) (error69 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound161 h y hh hy
  · norm_num
  · norm_num
def exact162 (h y : ℝ) : ℝ := exact159 h y + exact161 h y
def rounded162 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded159 rnd h y + rounded161 rnd h y)
theorem polynomial162 (h y : ℝ) : exact162 h y = evaluate [((-750255309152444489/288230376151711744 : ℝ), 0, 1), ((-17012064089372337823135906207193663/41538374868278621028243970633760768 : ℝ), 1, 1), ((-11754239370077508661035554878290527/332306998946228968225951765070086144 : ℝ), 2, 1), ((-482328106643840785980620111420221522328075403182907/191561942608236107294793378393788647952342390272950272 : ℝ), 3, 1), ((-814859914071461922153494622555781759186805440191711/6129982163463555433433388108601236734474956488734408704 : ℝ), 4, 1), ((-18571373959581678086579604537301558874088250621125/12259964326927110866866776217202473468949912977468817408 : ℝ), 5, 1)] h y := by
  simp only [exact162, polynomial159, polynomial161, evaluate] <;> ring
theorem bound162 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact162 h y| ≤ (1445146786817/1099511627776 : ℝ) := by
  rw [polynomial162]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error162 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded162 rnd h y - exact162 h y| ≤ (864786771989353452059047/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded162 exact162
  apply rounded_step rnd hrnd (propagation := (1530954081985154938139469/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (1445146786817/1099511627776 : ℝ))
  · convert FindOrb.add_error (error159 rnd hrnd h y hh hy) (error161 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound162 h y hh hy
  · norm_num
  · norm_num
def exact163 (h y : ℝ) : ℝ := (6412762798614975/2251799813685248 : ℝ)
def rounded163 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (6412762798614975/2251799813685248 : ℝ)
theorem polynomial163 (h y : ℝ) : exact163 h y = evaluate [((6412762798614975/2251799813685248 : ℝ), 0, 0)] h y := by
  simp only [exact163, evaluate] <;> ring
theorem bound163 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact163 h y| ≤ (1565615917631/549755813888 : ℝ) := by
  rw [polynomial163]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error163 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded163 rnd h y - exact163 h y| ≤ (0/1 : ℝ) := by
  simp [rounded163, exact163]
def exact164 (h y : ℝ) : ℝ := exact163 h y * exact91 h y
def rounded164 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded163 rnd h y * rounded91 rnd h y)
theorem polynomial164 (h y : ℝ) : exact164 h y = evaluate [((6412762798614975/2251799813685248 : ℝ), 0, 1), ((545264144916866873381041060140975/1298074214633706907132624082305024 : ℝ), 1, 1), ((5795337303683980816158242552361397199999012346225/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((4558998678898063538286011230443318761444866595325/2993155353253689176481146537402947624255349848014848 : ℝ), 3, 1), ((48455295213464218305193005832283786567646595333537029386356195125/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ), 4, 1), ((67284327864640876998517787814930229805112982378468752924285577425/27606985387162255149739023449108101809804435888681546220650096895197184 : ℝ), 5, 1), ((115587663783051960994204749767979051941083569631277704572615196875/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 6, 1)] h y := by
  simp only [exact164, polynomial163, polynomial91, evaluate] <;> ring
theorem bound164 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact164 h y| ≤ (790057835743/549755813888 : ℝ) := by
  rw [polynomial164]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error164 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded164 rnd h y - exact164 h y| ≤ (276421877401918398897109/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded164 exact164
  apply rounded_step rnd hrnd (propagation := (488467972172841624104234252121506351/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (790057835743/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound163 h y hh hy) (bound91 h y hh hy)
      (error163 rnd hrnd h y hh hy) (error91 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound164 h y hh hy
  · norm_num
  · norm_num
def exact165 (h y : ℝ) : ℝ := exact162 h y + exact164 h y
def rounded165 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded162 rnd h y + rounded164 rnd h y)
theorem polynomial165 (h y : ℝ) : exact165 h y = evaluate [((70578329070272311/288230376151711744 : ℝ), 0, 1), ((436388547967402125057407717317537/41538374868278621028243970633760768 : ℝ), 1, 1), ((-821711202204104388414911326699387391878557165199/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((-190552191194364719530315392671849121595603941082107/191561942608236107294793378393788647952342390272950272 : ℝ), 3, 1), ((-66226042454391728653525799642682015340026145992107818628052091083/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ), 4, 1), ((25465311442575787861876210762748127157855750468971118513035913425/27606985387162255149739023449108101809804435888681546220650096895197184 : ℝ), 5, 1), ((115587663783051960994204749767979051941083569631277704572615196875/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 6, 1)] h y := by
  simp only [exact165, polynomial162, polynomial164, evaluate] <;> ring
theorem bound165 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact165 h y| ≤ (67494009271/549755813888 : ℝ) := by
  rw [polynomial165]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error165 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded165 rnd h y - exact165 h y| ≤ (2853813665586051910984355/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded165 exact165
  apply rounded_step rnd hrnd (propagation := (1417630526793190249853265/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (67494009271/549755813888 : ℝ))
  · convert FindOrb.add_error (error162 rnd hrnd h y hh hy) (error164 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound165 h y hh hy
  · norm_num
  · norm_num
def exact166 (h y : ℝ) : ℝ := (5069023524617575/18014398509481984 : ℝ)
def rounded166 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (5069023524617575/18014398509481984 : ℝ)
theorem polynomial166 (h y : ℝ) : exact166 h y = evaluate [((5069023524617575/18014398509481984 : ℝ), 0, 0)] h y := by
  simp only [exact166, evaluate] <;> ring
theorem bound166 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact166 h y| ≤ (77347160715/274877906944 : ℝ) := by
  rw [polynomial166]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error166 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded166 rnd h y - exact166 h y| ≤ (0/1 : ℝ) := by
  simp [rounded166, exact166]
def exact167 (h y : ℝ) : ℝ := exact166 h y * exact116 h y
def rounded167 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded166 rnd h y * rounded116 rnd h y)
theorem polynomial167 (h y : ℝ) : exact167 h y = evaluate [((5069023524617575/18014398509481984 : ℝ), 0, 1), ((339693324554207859640014353711375/2596148429267413814265248164610048 : ℝ), 1, 1), ((1422753738790795189262111462861286817877603140625/46768052394588893382517914646921056628989841375232 : ℝ), 2, 1), ((31781265510976697744377735816210347865090096178010571656727297825/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 3, 1), ((29556576925208329333116471261098904049680983630355331771628883725/53919893334301279589334030174039261347274288845081144962207220498432 : ℝ), 4, 1), ((1509751343582485114435802019030408649462674149495004910091729765850009468955196325/31082702275611665134711390509176302506278509424834232340028998555822468563283335970816 : ℝ), 5, 1), ((3113091669470840440693392344603739362192155585202203987160005849896057198759223425/994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 : ℝ), 6, 1), ((-71068567603772676113101516887612554005828085878833740477387863615218859980553125/1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224 : ℝ), 7, 1)] h y := by
  simp only [exact167, polynomial166, polynomial116, evaluate] <;> ring
theorem bound167 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact167 h y| ≤ (39814023075/274877906944 : ℝ) := by
  rw [polynomial167]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error167 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded167 rnd h y - exact167 h y| ≤ (117639734304313581177979/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded167 exact167
  apply rounded_step rnd hrnd (propagation := (26320038879255476448670798913039535/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (39814023075/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound166 h y hh hy) (bound116 h y hh hy)
      (error166 rnd hrnd h y hh hy) (error116 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound167 h y hh hy
  · norm_num
  · norm_num
def exact168 (h y : ℝ) : ℝ := exact165 h y + exact167 h y
def rounded168 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded165 rnd h y + rounded167 rnd h y)
theorem polynomial168 (h y : ℝ) : exact168 h y = evaluate [((151682705464153511/288230376151711744 : ℝ), 0, 1), ((5871481740834727879297637376699537/41538374868278621028243970633760768 : ℝ), 1, 1), ((4869303752959076368633534524745759879631855397301/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((25076806313651912900569646997800957481171432380730947130717568801/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 3, 1), ((406679188348941540676337740534900449454869592093577489718010048517/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ), 4, 1), ((1538422735363399600976353366383148534349129864007839992225438080315769480519023525/31082702275611665134711390509176302506278509424834232340028998555822468563283335970816 : ℝ), 5, 1), ((5195333907638756390837731062832570073535014613183061971403029287872526021184823425/994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 : ℝ), 6, 1), ((-71068567603772676113101516887612554005828085878833740477387863615218859980553125/1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224 : ℝ), 7, 1)] h y := by
  simp only [exact168, polynomial165, polynomial167, evaluate] <;> ring
theorem bound168 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact168 h y| ≤ (294224976969/1099511627776 : ℝ) := by
  rw [polynomial168]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error168 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded168 rnd h y - exact168 h y| ≤ (3011891372810308154748703/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded168 exact168
  apply rounded_step rnd hrnd (propagation := (1485726699945182746081167/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (294224976969/1099511627776 : ℝ))
  · convert FindOrb.add_error (error165 rnd hrnd h y hh hy) (error167 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound168 h y hh hy
  · norm_num
  · norm_num
def exact169 (h y : ℝ) : ℝ := (2229189939653693/18014398509481984 : ℝ)
def rounded169 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (2229189939653693/18014398509481984 : ℝ)
theorem polynomial169 (h y : ℝ) : exact169 h y = evaluate [((2229189939653693/18014398509481984 : ℝ), 0, 0)] h y := by
  simp only [exact169, evaluate] <;> ring
theorem bound169 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact169 h y| ≤ (68029478139/549755813888 : ℝ) := by
  rw [polynomial169]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error169 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded169 rnd h y - exact169 h y| ≤ (0/1 : ℝ) := by
  simp [rounded169, exact169]
def exact170 (h y : ℝ) : ℝ := exact169 h y * exact144 h y
def rounded170 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded169 rnd h y * rounded144 rnd h y)
theorem polynomial170 (h y : ℝ) : exact170 h y = evaluate [((2229189939653693/18014398509481984 : ℝ), 0, 1), ((45367186720142650599487157201077/649037107316853453566312041152512 : ℝ), 1, 1), ((1846573586475119729428002233344602157312915675663/93536104789177786765035829293842113257979682750464 : ℝ), 2, 1), ((25053599725442446994521377193093815179291214611550843392871179887/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 3, 1), ((31867274871282277329774529299503399813443532913396769057280175255407588666105253/60708402882054033466233184588234965832575213720379360039119137804340758912662765568 : ℝ), 4, 1), ((1860037722458254330698883965298416634049714801471390452241539158391137800890095067/31082702275611665134711390509176302506278509424834232340028998555822468563283335970816 : ℝ), 5, 1), ((1568389839088574519644020160557358992948451833632658374328366300436562607024547157169088790615097/279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472 : ℝ), 6, 1), ((3376537745231033589808018906851676506861048457460805383457888040829705673939638592372439954605189/8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104 : ℝ), 7, 1), ((-59577231040067697238931981133860246792042320565985523478022845509074680471793434239003220333625/17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208 : ℝ), 8, 1)] h y := by
  simp only [exact170, polynomial169, polynomial144, evaluate] <;> ring
theorem bound170 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact170 h y| ≤ (70474095601/1099511627776 : ℝ) := by
  rw [polynomial170]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error170 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded170 rnd h y - exact170 h y| ≤ (56671495837248170862069/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded170 exact170
  apply rounded_step rnd hrnd (propagation := (6457653051657339017185016527920465/215679573337205118357336120696157045389097155380324579848828881993728 : ℝ)) (magnitude := (70474095601/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound169 h y hh hy) (bound144 h y hh hy)
      (error169 rnd hrnd h y hh hy) (error144 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound170 h y hh hy
  · norm_num
  · norm_num
def exact171 (h y : ℝ) : ℝ := exact168 h y + exact170 h y
def rounded171 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded168 rnd h y + rounded170 rnd h y)
theorem polynomial171 (h y : ℝ) : exact171 h y = evaluate [((187349744498612599/288230376151711744 : ℝ), 0, 1), ((8774981690923857517664815437568465/41538374868278621028243970633760768 : ℝ), 1, 1), ((8562450925909315827489538991434964194257686748627/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((3133150377443397493443189011930923291278915437017611907724296793/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 3, 1), ((60484778638588978595419676503463100941010744244764098685122807682188478573829541/60708402882054033466233184588234965832575213720379360039119137804340758912662765568 : ℝ), 4, 1), ((26550472326731671341212791653762227878115973949056487847398259677397713136008739/242833611528216133864932738352939863330300854881517440156476551217363035650651062272 : ℝ), 5, 1), ((3030746329745274904891845193049789752603381225216109371281768743917170141499258674396323466531897/279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472 : ℝ), 6, 1), ((3056473370652928061849335744174290748119090833261822500143144870805968850689870184621400569005189/8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104 : ℝ), 7, 1), ((-59577231040067697238931981133860246792042320565985523478022845509074680471793434239003220333625/17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208 : ℝ), 8, 1)] h y := by
  simp only [exact171, polynomial168, polynomial170, evaluate] <;> ring
theorem bound171 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact171 h y| ≤ (364699072569/1099511627776 : ℝ) := by
  rw [polynomial171]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error171 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded171 rnd h y - exact171 h y| ≤ (3118686727513648668120341/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded171 exact171
  apply rounded_step rnd hrnd (propagation := (767140717161889081402693/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (364699072569/1099511627776 : ℝ))
  · convert FindOrb.add_error (error168 rnd hrnd h y hh hy) (error170 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound171 h y hh hy
  · norm_num
  · norm_num
def exact172 (h y : ℝ) : ℝ := exact171 h y * exact0 h y
def rounded172 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded171 rnd h y * rounded0 rnd h y)
theorem polynomial172 (h y : ℝ) : exact172 h y = evaluate [((187349744498612599/288230376151711744 : ℝ), 1, 1), ((8774981690923857517664815437568465/41538374868278621028243970633760768 : ℝ), 2, 1), ((8562450925909315827489538991434964194257686748627/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((3133150377443397493443189011930923291278915437017611907724296793/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 4, 1), ((60484778638588978595419676503463100941010744244764098685122807682188478573829541/60708402882054033466233184588234965832575213720379360039119137804340758912662765568 : ℝ), 5, 1), ((26550472326731671341212791653762227878115973949056487847398259677397713136008739/242833611528216133864932738352939863330300854881517440156476551217363035650651062272 : ℝ), 6, 1), ((3030746329745274904891845193049789752603381225216109371281768743917170141499258674396323466531897/279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472 : ℝ), 7, 1), ((3056473370652928061849335744174290748119090833261822500143144870805968850689870184621400569005189/8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104 : ℝ), 8, 1), ((-59577231040067697238931981133860246792042320565985523478022845509074680471793434239003220333625/17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208 : ℝ), 9, 1)] h y := by
  simp only [exact172, polynomial171, polynomial0, evaluate] <;> ring
theorem bound172 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact172 h y| ≤ (5698423009/274877906944 : ℝ) := by
  rw [polynomial172]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error172 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded172 rnd h y - exact172 h y| ≤ (99025330824396971353257/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded172 exact172
  apply rounded_step rnd hrnd (propagation := (3118686727513648668120341/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (5698423009/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound171 h y hh hy) (bound0 h y hh hy)
      (error171 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound172 h y hh hy
  · norm_num
  · norm_num
def exact173 (h y : ℝ) : ℝ := exact172 h y + exact3 h y
def rounded173 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded172 rnd h y + rounded3 rnd h y)
theorem polynomial173 (h y : ℝ) : exact173 h y = evaluate [((1/1 : ℝ), 0, 1), ((187349744498612599/288230376151711744 : ℝ), 1, 1), ((8774981690923857517664815437568465/41538374868278621028243970633760768 : ℝ), 2, 1), ((8562450925909315827489538991434964194257686748627/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((3133150377443397493443189011930923291278915437017611907724296793/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 4, 1), ((60484778638588978595419676503463100941010744244764098685122807682188478573829541/60708402882054033466233184588234965832575213720379360039119137804340758912662765568 : ℝ), 5, 1), ((26550472326731671341212791653762227878115973949056487847398259677397713136008739/242833611528216133864932738352939863330300854881517440156476551217363035650651062272 : ℝ), 6, 1), ((3030746329745274904891845193049789752603381225216109371281768743917170141499258674396323466531897/279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472 : ℝ), 7, 1), ((3056473370652928061849335744174290748119090833261822500143144870805968850689870184621400569005189/8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104 : ℝ), 8, 1), ((-59577231040067697238931981133860246792042320565985523478022845509074680471793434239003220333625/17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208 : ℝ), 9, 1)] h y := by
  simp only [exact173, polynomial172, polynomial3, evaluate] <;> ring
theorem bound173 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact173 h y| ≤ (143137376481/274877906944 : ℝ) := by
  rw [polynomial173]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error173 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded173 rnd h y - exact173 h y| ≤ (88074782569953372623445/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded173 exact173
  apply rounded_step rnd hrnd (propagation := (273608525374708266125651/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (143137376481/274877906944 : ℝ))
  · convert FindOrb.add_error (error172 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound173 h y hh hy
  · norm_num
  · norm_num
def exact174 (h y : ℝ) : ℝ := exact173 h y + exact2 h y
def rounded174 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded173 rnd h y + rounded2 rnd h y)
theorem polynomial174 (h y : ℝ) : exact174 h y = evaluate [((1/1 : ℝ), 0, 1), ((187349744498612599/288230376151711744 : ℝ), 1, 1), ((8774981690923857517664815437568465/41538374868278621028243970633760768 : ℝ), 2, 1), ((8562450925909315827489538991434964194257686748627/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((3133150377443397493443189011930923291278915437017611907724296793/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 4, 1), ((60484778638588978595419676503463100941010744244764098685122807682188478573829541/60708402882054033466233184588234965832575213720379360039119137804340758912662765568 : ℝ), 5, 1), ((26550472326731671341212791653762227878115973949056487847398259677397713136008739/242833611528216133864932738352939863330300854881517440156476551217363035650651062272 : ℝ), 6, 1), ((3030746329745274904891845193049789752603381225216109371281768743917170141499258674396323466531897/279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472 : ℝ), 7, 1), ((3056473370652928061849335744174290748119090833261822500143144870805968850689870184621400569005189/8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104 : ℝ), 8, 1), ((-59577231040067697238931981133860246792042320565985523478022845509074680471793434239003220333625/17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208 : ℝ), 9, 1)] h y := by
  simp only [exact174, polynomial173, polynomial2, evaluate] <;> ring
theorem bound174 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact174 h y| ≤ (143137376481/274877906944 : ℝ) := by
  rw [polynomial174]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error174 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded174 rnd h y - exact174 h y| ≤ (430989735184918714861909/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded174 exact174
  apply rounded_step rnd hrnd (propagation := (88074782569953372623445/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (143137376481/274877906944 : ℝ))
  · convert FindOrb.add_error (error173 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound174 h y hh hy
  · norm_num
  · norm_num
def exact175 (h y : ℝ) : ℝ := exact174 h y + exact2 h y
def rounded175 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded174 rnd h y + rounded2 rnd h y)
theorem polynomial175 (h y : ℝ) : exact175 h y = evaluate [((1/1 : ℝ), 0, 1), ((187349744498612599/288230376151711744 : ℝ), 1, 1), ((8774981690923857517664815437568465/41538374868278621028243970633760768 : ℝ), 2, 1), ((8562450925909315827489538991434964194257686748627/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((3133150377443397493443189011930923291278915437017611907724296793/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 4, 1), ((60484778638588978595419676503463100941010744244764098685122807682188478573829541/60708402882054033466233184588234965832575213720379360039119137804340758912662765568 : ℝ), 5, 1), ((26550472326731671341212791653762227878115973949056487847398259677397713136008739/242833611528216133864932738352939863330300854881517440156476551217363035650651062272 : ℝ), 6, 1), ((3030746329745274904891845193049789752603381225216109371281768743917170141499258674396323466531897/279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472 : ℝ), 7, 1), ((3056473370652928061849335744174290748119090833261822500143144870805968850689870184621400569005189/8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104 : ℝ), 8, 1), ((-59577231040067697238931981133860246792042320565985523478022845509074680471793434239003220333625/17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208 : ℝ), 9, 1)] h y := by
  simp only [exact175, polynomial174, polynomial2, evaluate] <;> ring
theorem bound175 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact175 h y| ≤ (143137376481/274877906944 : ℝ) := by
  rw [polynomial175]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error175 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded175 rnd h y - exact175 h y| ≤ (254840170045011969615019/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded175 exact175
  apply rounded_step rnd hrnd (propagation := (430989735184918714861909/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (143137376481/274877906944 : ℝ))
  · convert FindOrb.add_error (error174 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound175 h y hh hy
  · norm_num
  · norm_num
def exact176 (h y : ℝ) : ℝ := (-5473786754720975/4503599627370496 : ℝ)
def rounded176 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-5473786754720975/4503599627370496 : ℝ)
theorem polynomial176 (h y : ℝ) : exact176 h y = evaluate [((-5473786754720975/4503599627370496 : ℝ), 0, 0)] h y := by
  simp only [exact176, evaluate] <;> ring
theorem bound176 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact176 h y| ≤ (1336373719415/1099511627776 : ℝ) := by
  rw [polynomial176]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error176 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded176 rnd h y - exact176 h y| ≤ (0/1 : ℝ) := by
  simp [rounded176, exact176]
def exact177 (h y : ℝ) : ℝ := exact176 h y * exact4 h y
def rounded177 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded176 rnd h y * rounded4 rnd h y)
theorem polynomial177 (h y : ℝ) : exact177 h y = evaluate [((-5473786754720975/4503599627370496 : ℝ), 0, 1)] h y := by
  simp only [exact177, polynomial176, polynomial4, evaluate] <;> ring
theorem bound177 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact177 h y| ≤ (167046714927/274877906944 : ℝ) := by
  rw [polynomial177]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error177 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded177 rnd h y - exact177 h y| ≤ (91834902721975243767809/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded177 exact177
  apply rounded_step rnd hrnd (propagation := (100973543378451834509255352679444855/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (167046714927/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound176 h y hh hy) (bound4 h y hh hy)
      (error176 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound177 h y hh hy
  · norm_num
  · norm_num
def exact178 (h y : ℝ) : ℝ := exact2 h y + exact177 h y
def rounded178 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded177 rnd h y)
theorem polynomial178 (h y : ℝ) : exact178 h y = evaluate [((-5473786754720975/4503599627370496 : ℝ), 0, 1)] h y := by
  simp only [exact178, polynomial2, polynomial177, evaluate] <;> ring
theorem bound178 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact178 h y| ≤ (167046714927/274877906944 : ℝ) := by
  rw [polynomial178]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error178 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded178 rnd h y - exact178 h y| ≤ (275504708165960091041795/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded178 exact178
  apply rounded_step rnd hrnd (propagation := (91834902721975243767809/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (167046714927/274877906944 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error177 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound178 h y hh hy
  · norm_num
  · norm_num
def exact179 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded179 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial179 (h y : ℝ) : exact179 h y = evaluate [] h y := by
  simp only [exact179, evaluate] <;> ring
theorem bound179 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact179 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial179]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error179 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded179 rnd h y - exact179 h y| ≤ (0/1 : ℝ) := by
  simp [rounded179, exact179]
def exact180 (h y : ℝ) : ℝ := exact179 h y * exact11 h y
def rounded180 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded179 rnd h y * rounded11 rnd h y)
theorem polynomial180 (h y : ℝ) : exact180 h y = evaluate [] h y := by
  simp only [exact180, polynomial179, polynomial11, evaluate] <;> ring
theorem bound180 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact180 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial180]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error180 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded180 rnd h y - exact180 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded180 exact180
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound179 h y hh hy) (bound11 h y hh hy)
      (error179 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound180 h y hh hy
  · norm_num
  · norm_num
def exact181 (h y : ℝ) : ℝ := exact178 h y + exact180 h y
def rounded181 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded178 rnd h y + rounded180 rnd h y)
theorem polynomial181 (h y : ℝ) : exact181 h y = evaluate [((-5473786754720975/4503599627370496 : ℝ), 0, 1)] h y := by
  simp only [exact181, polynomial178, polynomial180, evaluate] <;> ring
theorem bound181 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact181 h y| ≤ (167046714927/274877906944 : ℝ) := by
  rw [polynomial181]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error181 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded181 rnd h y - exact181 h y| ≤ (367339610887969694547973/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded181 exact181
  apply rounded_step rnd hrnd (propagation := (68876177041490022760449/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (167046714927/274877906944 : ℝ))
  · convert FindOrb.add_error (error178 rnd hrnd h y hh hy) (error180 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound181 h y hh hy
  · norm_num
  · norm_num
def exact182 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded182 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial182 (h y : ℝ) : exact182 h y = evaluate [] h y := by
  simp only [exact182, evaluate] <;> ring
theorem bound182 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact182 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial182]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error182 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded182 rnd h y - exact182 h y| ≤ (0/1 : ℝ) := by
  simp [rounded182, exact182]
def exact183 (h y : ℝ) : ℝ := exact182 h y * exact21 h y
def rounded183 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded182 rnd h y * rounded21 rnd h y)
theorem polynomial183 (h y : ℝ) : exact183 h y = evaluate [] h y := by
  simp only [exact183, polynomial182, polynomial21, evaluate] <;> ring
theorem bound183 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact183 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial183]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error183 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded183 rnd h y - exact183 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded183 exact183
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound182 h y hh hy) (bound21 h y hh hy)
      (error182 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound183 h y hh hy
  · norm_num
  · norm_num
def exact184 (h y : ℝ) : ℝ := exact181 h y + exact183 h y
def rounded184 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded181 rnd h y + rounded183 rnd h y)
theorem polynomial184 (h y : ℝ) : exact184 h y = evaluate [((-5473786754720975/4503599627370496 : ℝ), 0, 1)] h y := by
  simp only [exact184, polynomial181, polynomial183, evaluate] <;> ring
theorem bound184 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact184 h y| ≤ (167046714927/274877906944 : ℝ) := by
  rw [polynomial184]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error184 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded184 rnd h y - exact184 h y| ≤ (459174513609979298054151/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded184 exact184
  apply rounded_step rnd hrnd (propagation := (183669805443984847273987/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (167046714927/274877906944 : ℝ))
  · convert FindOrb.add_error (error181 rnd hrnd h y hh hy) (error183 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound184 h y hh hy
  · norm_num
  · norm_num
def exact185 (h y : ℝ) : ℝ := (586615266994121/35184372088832 : ℝ)
def rounded185 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (586615266994121/35184372088832 : ℝ)
theorem polynomial185 (h y : ℝ) : exact185 h y = evaluate [((586615266994121/35184372088832 : ℝ), 0, 0)] h y := by
  simp only [exact185, evaluate] <;> ring
theorem bound185 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact185 h y| ≤ (18331727093567/1099511627776 : ℝ) := by
  rw [polynomial185]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error185 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded185 rnd h y - exact185 h y| ≤ (0/1 : ℝ) := by
  simp [rounded185, exact185]
def exact186 (h y : ℝ) : ℝ := exact185 h y * exact34 h y
def rounded186 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded185 rnd h y * rounded34 rnd h y)
theorem polynomial186 (h y : ℝ) : exact186 h y = evaluate [((586615266994121/35184372088832 : ℝ), 0, 1), ((586615266994121/281474976710656 : ℝ), 1, 1), ((42270084765513077121434666670135/324518553658426726783156020576256 : ℝ), 2, 1), ((3522507063792756280132405473981/649037107316853453566312041152512 : ℝ), 3, 1)] h y := by
  simp only [exact186, polynomial185, polynomial34, evaluate] <;> ring
theorem bound186 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact186 h y| ≤ (9237752304137/1099511627776 : ℝ) := by
  rw [polynomial186]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error186 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded186 rnd h y - exact186 h y| ≤ (6405168841616336536795085/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded186 exact186
  apply rounded_step rnd hrnd (propagation := (5646587959766225530441035658691927099/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (9237752304137/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound185 h y hh hy) (bound34 h y hh hy)
      (error185 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound186 h y hh hy
  · norm_num
  · norm_num
def exact187 (h y : ℝ) : ℝ := exact184 h y + exact186 h y
def rounded187 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded184 rnd h y + rounded186 rnd h y)
theorem polynomial187 (h y : ℝ) : exact187 h y = evaluate [((69612967420526513/4503599627370496 : ℝ), 0, 1), ((586615266994121/281474976710656 : ℝ), 1, 1), ((42270084765513077121434666670135/324518553658426726783156020576256 : ℝ), 2, 1), ((3522507063792756280132405473981/649037107316853453566312041152512 : ℝ), 3, 1)] h y := by
  simp only [exact187, polynomial184, polynomial186, evaluate] <;> ring
theorem bound187 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact187 h y| ≤ (4284782722215/549755813888 : ℝ) := by
  rw [polynomial187]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error187 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded187 rnd h y - exact187 h y| ≤ (8042135461618589606410197/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded187 exact187
  apply rounded_step rnd hrnd (propagation := (1716085838806578958712309/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (4284782722215/549755813888 : ℝ))
  · convert FindOrb.add_error (error184 rnd hrnd h y hh hy) (error186 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound187 h y hh hy
  · norm_num
  · norm_num
def exact188 (h y : ℝ) : ℝ := (2062067278612779/2251799813685248 : ℝ)
def rounded188 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (2062067278612779/2251799813685248 : ℝ)
theorem polynomial188 (h y : ℝ) : exact188 h y = evaluate [((2062067278612779/2251799813685248 : ℝ), 0, 0)] h y := by
  simp only [exact188, evaluate] <;> ring
theorem bound188 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact188 h y| ≤ (503434394193/549755813888 : ℝ) := by
  rw [polynomial188]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error188 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded188 rnd h y - exact188 h y| ≤ (0/1 : ℝ) := by
  simp [rounded188, exact188]
def exact189 (h y : ℝ) : ℝ := exact188 h y * exact50 h y
def rounded189 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded188 rnd h y * rounded50 rnd h y)
theorem polynomial189 (h y : ℝ) : exact189 h y = evaluate [((2062067278612779/2251799813685248 : ℝ), 0, 1), ((10310336393063895/36028797018963968 : ℝ), 1, 1), ((1857345085514680903609752598996275/41538374868278621028243970633760768 : ℝ), 2, 1), ((6191150285048936293814160031334775/1329227995784915872903807060280344576 : ℝ), 3, 1), ((928672542757340374477353351518925/2658455991569831745807614120560689152 : ℝ), 4, 1)] h y := by
  simp only [exact189, polynomial188, polynomial50, evaluate] <;> ring
theorem bound189 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact189 h y| ≤ (128340936943/274877906944 : ℝ) := by
  rw [polynomial189]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error189 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded189 rnd h y - exact189 h y| ≤ (207338795145342200475413/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded189 exact189
  apply rounded_step rnd hrnd (propagation := (94591374027694190240721719893622979/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (128340936943/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound188 h y hh hy) (bound50 h y hh hy)
      (error188 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound189 h y hh hy
  · norm_num
  · norm_num
def exact190 (h y : ℝ) : ℝ := exact187 h y + exact189 h y
def rounded190 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded187 rnd h y + rounded189 rnd h y)
theorem polynomial190 (h y : ℝ) : exact190 h y = evaluate [((73737101977752071/4503599627370496 : ℝ), 0, 1), ((85397090568311383/36028797018963968 : ℝ), 1, 1), ((7267915935500354775153389932773555/41538374868278621028243970633760768 : ℝ), 2, 1), ((13405244751696501155525326442047863/1329227995784915872903807060280344576 : ℝ), 3, 1), ((928672542757340374477353351518925/2658455991569831745807614120560689152 : ℝ), 4, 1)] h y := by
  simp only [exact190, polynomial187, polynomial189, evaluate] <;> ring
theorem bound190 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact190 h y| ≤ (9082929192201/1099511627776 : ℝ) := by
  rw [polynomial190]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error190 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded190 rnd h y - exact190 h y| ≤ (18955393231534487874283/3064991081731777716716694054300618367237478244367204352 : ℝ) := by
  unfold rounded190 exact190
  apply rounded_step rnd hrnd (propagation := (8456813051909274007361023/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (9082929192201/1099511627776 : ℝ))
  · convert FindOrb.add_error (error187 rnd hrnd h y hh hy) (error189 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound190 h y hh hy
  · norm_num
  · norm_num
def exact191 (h y : ℝ) : ℝ := (-1704782977727143/281474976710656 : ℝ)
def rounded191 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-1704782977727143/281474976710656 : ℝ)
theorem polynomial191 (h y : ℝ) : exact191 h y = evaluate [((-1704782977727143/281474976710656 : ℝ), 0, 0)] h y := by
  simp only [exact191, evaluate] <;> ring
theorem bound191 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact191 h y| ≤ (6659308506747/1099511627776 : ℝ) := by
  rw [polynomial191]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error191 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded191 rnd h y - exact191 h y| ≤ (0/1 : ℝ) := by
  simp [rounded191, exact191]
def exact192 (h y : ℝ) : ℝ := exact191 h y * exact69 h y
def rounded192 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded191 rnd h y * rounded69 rnd h y)
theorem polynomial192 (h y : ℝ) : exact192 h y = evaluate [((-1704782977727143/281474976710656 : ℝ), 0, 1), ((-92131919798874307855516901147993/40564819207303340847894502572032 : ℝ), 1, 1), ((-69098939849155730465441931429209/162259276829213363391578010288128 : ℝ), 2, 1), ((-9958206712203330219713287530807608913445441215165/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((-29874620136609990349474243268428625289716100961209/5986310706507378352962293074805895248510699696029696 : ℝ), 4, 1), ((-4149252796751387249251528885074324020312003863875/11972621413014756705924586149611790497021399392059392 : ℝ), 5, 1)] h y := by
  simp only [exact192, polynomial191, polynomial69, evaluate] <;> ring
theorem bound192 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact192 h y| ≤ (3408614728499/1099511627776 : ℝ) := by
  rw [polynomial192]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error192 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded192 rnd h y - exact192 h y| ≤ (2418053784327616071405719/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded192 exact192
  apply rounded_step rnd hrnd (propagation := (33493483721184846878080824971721051/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ)) (magnitude := (3408614728499/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound191 h y hh hy) (bound69 h y hh hy)
      (error191 rnd hrnd h y hh hy) (error69 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound192 h y hh hy
  · norm_num
  · norm_num
def exact193 (h y : ℝ) : ℝ := exact190 h y + exact192 h y
def rounded193 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded190 rnd h y + rounded192 rnd h y)
theorem polynomial193 (h y : ℝ) : exact193 h y = evaluate [((46460574334117783/4503599627370496 : ℝ), 0, 1), ((4016656516618602885945907640999/40564819207303340847894502572032 : ℝ), 1, 1), ((-10421412665883512223999744513103949/41538374868278621028243970633760768 : ℝ), 2, 1), ((-8071586235061122101564741404383311905057314151101/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((-27783435477854405787269407041813529279333435642809/5986310706507378352962293074805895248510699696029696 : ℝ), 4, 1), ((-4149252796751387249251528885074324020312003863875/11972621413014756705924586149611790497021399392059392 : ℝ), 5, 1)] h y := by
  simp only [exact193, polynomial190, polynomial192, evaluate] <;> ring
theorem bound193 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact193 h y| ≤ (709425459113/137438953472 : ℝ) := by
  rw [polynomial193]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error193 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded193 rnd h y - exact193 h y| ≤ (1612904582526043078270163/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded193 exact193
  apply rounded_step rnd hrnd (propagation := (12123215118873273863038615/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (709425459113/137438953472 : ℝ))
  · convert FindOrb.add_error (error190 rnd hrnd h y hh hy) (error192 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound193 h y hh hy
  · norm_num
  · norm_num
def exact194 (h y : ℝ) : ℝ := (-1126151376175595/70368744177664 : ℝ)
def rounded194 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-1126151376175595/70368744177664 : ℝ)
theorem polynomial194 (h y : ℝ) : exact194 h y = evaluate [((-1126151376175595/70368744177664 : ℝ), 0, 0)] h y := by
  simp only [exact194, evaluate] <;> ring
theorem bound194 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact194 h y| ≤ (2199514406593/137438953472 : ℝ) := by
  rw [polynomial194]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error194 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded194 rnd h y - exact194 h y| ≤ (0/1 : ℝ) := by
  simp [rounded194, exact194]
def exact195 (h y : ℝ) : ℝ := exact194 h y * exact91 h y
def rounded195 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded194 rnd h y * rounded91 rnd h y)
theorem polynomial195 (h y : ℝ) : exact195 h y = evaluate [((-1126151376175595/70368744177664 : ℝ), 0, 1), ((-95754355253863571638582483376795/40564819207303340847894502572032 : ℝ), 1, 1), ((-1017724697591348812776305149617002541695698371845/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((-800610095438527492055697465592360758688830075265/93536104789177786765035829293842113257979682750464 : ℝ), 3, 1), ((-8509280492866977233088806281617277539871328430171172892436896025/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ), 4, 1), ((-11815864830706123282194052133619422138419514096306453207761293285/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ), 5, 1), ((-20298459607194549780098157907369211328663061795663380254063814375/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 6, 1)] h y := by
  simp only [exact195, polynomial194, polynomial91, evaluate] <;> ring
theorem bound195 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact195 h y| ≤ (1109942465575/137438953472 : ℝ) := by
  rw [polynomial195]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error195 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded195 rnd h y - exact195 h y| ≤ (6213466736470208681807499/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded195 exact195
  apply rounded_step rnd hrnd (propagation := (686242602578506296218983632956716753/215679573337205118357336120696157045389097155380324579848828881993728 : ℝ)) (magnitude := (1109942465575/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound194 h y hh hy) (bound91 h y hh hy)
      (error194 rnd hrnd h y hh hy) (error91 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound195 h y hh hy
  · norm_num
  · norm_num
def exact196 (h y : ℝ) : ℝ := exact193 h y + exact195 h y
def rounded196 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded193 rnd h y + rounded195 rnd h y)
theorem polynomial196 (h y : ℝ) : exact196 h y = evaluate [((-25613113741120297/4503599627370496 : ℝ), 0, 1), ((-22934424684311242188159143933949/10141204801825835211973625643008 : ℝ), 1, 1), ((-2484408141302197343542379136562416625188010362117/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((-9672806425938177085676136335568033422434974301631/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((-133634750158004297607745095110200027637194713343630211096598059289/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ), 4, 1), ((-310801038419754699148545147914405757673759958531498852538565005285/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ), 5, 1), ((-20298459607194549780098157907369211328663061795663380254063814375/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ), 6, 1)] h y := by
  simp only [exact196, polynomial193, polynomial195, evaluate] <;> ring
theorem bound196 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact196 h y| ≤ (1602612630449/549755813888 : ℝ) := by
  rw [polynomial196]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error196 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded196 rnd h y - exact196 h y| ≤ (4889306550544598147726665/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded196 exact196
  apply rounded_step rnd hrnd (propagation := (19116703396678553307968803/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (1602612630449/549755813888 : ℝ))
  · convert FindOrb.add_error (error193 rnd hrnd h y hh hy) (error195 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound196 h y hh hy
  · norm_num
  · norm_num
def exact197 (h y : ℝ) : ℝ := (4179707240385107/281474976710656 : ℝ)
def rounded197 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (4179707240385107/281474976710656 : ℝ)
theorem polynomial197 (h y : ℝ) : exact197 h y = evaluate [((4179707240385107/281474976710656 : ℝ), 0, 0)] h y := by
  simp only [exact197, evaluate] <;> ring
theorem bound197 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact197 h y| ≤ (16326981407755/1099511627776 : ℝ) := by
  rw [polynomial197]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error197 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded197 rnd h y - exact197 h y| ≤ (0/1 : ℝ) := by
  simp [rounded197, exact197]
def exact198 (h y : ℝ) : ℝ := exact197 h y * exact116 h y
def rounded198 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded197 rnd h y * rounded116 rnd h y)
theorem polynomial198 (h y : ℝ) : exact198 h y = evaluate [((4179707240385107/281474976710656 : ℝ), 0, 1), ((280097072198304063577374213434395/40564819207303340847894502572032 : ℝ), 1, 1), ((1173143915081259656163358410526956062543322293125/730750818665451459101842416358141509827966271488 : ℝ), 2, 1), ((26205517674107151820157201254829330217299996312634851681586224597/105312291668557186697918027683670432318895095400549111254310977536 : ℝ), 3, 1), ((24371131436919651548003318552561003079568087862579407646813288881/842498333348457493583344221469363458551160763204392890034487820288 : ℝ), 4, 1), ((1244878543432865417140648181596880160722412850044527097438121101952324943848412457/485667223056432267729865476705879726660601709763034880312953102434726071301302124544 : ℝ), 5, 1), ((2566926692622025085754923083714582099748766955017879017007071602259936493673744053/15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 : ℝ), 6, 1), ((-58600202807245265464979731696050773023577687470323444914175571626685603953251625/31082702275611665134711390509176302506278509424834232340028998555822468563283335970816 : ℝ), 7, 1)] h y := by
  simp only [exact198, polynomial197, polynomial116, evaluate] <;> ring
theorem bound198 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact198 h y| ≤ (4202111677409/549755813888 : ℝ) := by
  rw [polynomial198]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error198 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded198 rnd h y - exact198 h y| ≤ (6208055140753568107648333/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded198 exact198
  apply rounded_step rnd hrnd (propagation := (5555818487202150576500478443396456495/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (4202111677409/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound197 h y hh hy) (bound116 h y hh hy)
      (error197 rnd hrnd h y hh hy) (error116 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound198 h y hh hy
  · norm_num
  · norm_num
def exact199 (h y : ℝ) : ℝ := exact196 h y + exact198 h y
def rounded199 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded196 rnd h y + rounded198 rnd h y)
theorem polynomial199 (h y : ℝ) : exact199 h y = evaluate [((41262202105041415/4503599627370496 : ℝ), 0, 1), ((188359373461059094824737637698599/40564819207303340847894502572032 : ℝ), 1, 1), ((6900743179347879905764488147653231875158567982883/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((20760211747171887627945278067179329222026959086702548515274464725/105312291668557186697918027683670432318895095400549111254310977536 : ℝ), 3, 1), ((646241455823424551928361098571752070908984098258910833601427184903/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ), 4, 1), ((1069913113331169107884741858752415538058926173478890713733159156978961542736778537/485667223056432267729865476705879726660601709763034880312953102434726071301302124544 : ℝ), 5, 1), ((2384094422375712207761502787933897444142567349353775218461457483491822763482384053/15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 : ℝ), 6, 1), ((-58600202807245265464979731696050773023577687470323444914175571626685603953251625/31082702275611665134711390509176302506278509424834232340028998555822468563283335970816 : ℝ), 7, 1)] h y := by
  simp only [exact199, polynomial196, polynomial198, evaluate] <;> ring
theorem bound199 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact199 h y| ≤ (5198998093921/1099511627776 : ℝ) := by
  rw [polynomial199]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error199 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded199 rnd h y - exact199 h y| ≤ (13239913100031692851799353/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded199 exact199
  apply rounded_step rnd hrnd (propagation := (25765281342931960698554993/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (5198998093921/1099511627776 : ℝ))
  · convert FindOrb.add_error (error196 rnd hrnd h y hh hy) (error198 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound199 h y hh hy
  · norm_num
  · norm_num
def exact200 (h y : ℝ) : ℝ := (-3763763968675483/281474976710656 : ℝ)
def rounded200 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-3763763968675483/281474976710656 : ℝ)
theorem polynomial200 (h y : ℝ) : exact200 h y = evaluate [((-3763763968675483/281474976710656 : ℝ), 0, 0)] h y := by
  simp only [exact200, evaluate] <;> ring
theorem bound200 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact200 h y| ≤ (14702203002639/1099511627776 : ℝ) := by
  rw [polynomial200]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error200 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded200 rnd h y - exact200 h y| ≤ (0/1 : ℝ) := by
  simp [rounded200, exact200]
def exact201 (h y : ℝ) : ℝ := exact200 h y * exact144 h y
def rounded201 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded200 rnd h y * rounded144 rnd h y)
theorem polynomial201 (h y : ℝ) : exact201 h y = evaluate [((-3763763968675483/281474976710656 : ℝ), 0, 1), ((-76597951435207077195637145612387/10141204801825835211973625643008 : ℝ), 1, 1), ((-3117754573826318750217430248994710866501731546553/1461501637330902918203684832716283019655932542976 : ℝ), 2, 1), ((-42300494118902767332560882611439079534205127540148204501855825497/105312291668557186697918027683670432318895095400549111254310977536 : ℝ), 3, 1), ((-53804702240421388597079620456239864875530617675270633700966005976694609804793843/948568795032094272909893509191171341133987714380927500611236528192824358010355712 : ℝ), 4, 1), ((-3140487419054635905800937955559238955113749624449082863455914256126558779974056077/485667223056432267729865476705879726660601709763034880312953102434726071301302124544 : ℝ), 5, 1), ((-2648069175350468476950077002442965699683236386758560273548267937727515892397902956308537817987007/4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 : ℝ), 6, 1), ((-5700945836112825520891114432841293711412756451832542864550605265193853371093370445609776020963859/139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736 : ℝ), 7, 1), ((100590188190467276290031829579625918212223454238049930489947564738056137305014783647621350717375/279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472 : ℝ), 8, 1)] h y := by
  simp only [exact201, polynomial200, polynomial144, evaluate] <;> ring
theorem bound201 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact201 h y| ≤ (7615260974251/1099511627776 : ℝ) := by
  rw [polynomial201]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error201 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded201 rnd h y - exact201 h y| ≤ (1530946324765193050938835/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded201 exact201
  apply rounded_step rnd hrnd (propagation := (1395596860115396850726359490326077965/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (7615260974251/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound200 h y hh hy) (bound144 h y hh hy)
      (error200 rnd hrnd h y hh hy) (error144 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound201 h y hh hy
  · norm_num
  · norm_num
def exact202 (h y : ℝ) : ℝ := exact199 h y + exact201 h y
def rounded202 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded199 rnd h y + rounded201 rnd h y)
theorem polynomial202 (h y : ℝ) : exact202 h y = evaluate [((-18958021393766313/4503599627370496 : ℝ), 0, 1), ((-118032432279769213957810944750949/40564819207303340847894502572032 : ℝ), 1, 1), ((-5570275115957395095105232848325611590848358203329/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((-5385070592932719926153901136064937578044542113361413996645340193/26328072917139296674479506920917608079723773850137277813577744384 : ℝ), 3, 1), ((-31067102399501531844392396416862498212572663057057687200167725001672694199490547/948568795032094272909893509191171341133987714380927500611236528192824358010355712 : ℝ), 4, 1), ((-517643576430866699479049024201705854263705862742548037430688774786899309309319385/121416805764108066932466369176469931665150427440758720078238275608681517825325531136 : ℝ), 5, 1), ((-1977006253336260014459666856766380301744794079456242436200077953985689154462080430762242968418239/4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 : ℝ), 6, 1), ((-5964857687639370792075986275943901180849262614531557543532446371631228832888904698919183810019859/139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736 : ℝ), 7, 1), ((100590188190467276290031829579625918212223454238049930489947564738056137305014783647621350717375/279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472 : ℝ), 8, 1)] h y := by
  simp only [exact202, polynomial199, polynomial201, evaluate] <;> ring
theorem bound202 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact202 h y| ≤ (2416262880331/1099511627776 : ℝ) := by
  rw [polynomial202]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error202 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded202 rnd h y - exact202 h y| ≤ (32935700140710090920313279/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded202 exact202
  apply rounded_step rnd hrnd (propagation := (16301805749562078953677023/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (2416262880331/1099511627776 : ℝ))
  · convert FindOrb.add_error (error199 rnd hrnd h y hh hy) (error201 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound202 h y hh hy
  · norm_num
  · norm_num
def exact203 (h y : ℝ) : ℝ := (5780575765298471/1125899906842624 : ℝ)
def rounded203 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (5780575765298471/1125899906842624 : ℝ)
theorem polynomial203 (h y : ℝ) : exact203 h y = evaluate [((5780575765298471/1125899906842624 : ℝ), 0, 0)] h y := by
  simp only [exact203, evaluate] <;> ring
theorem bound203 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact203 h y| ≤ (176409172525/34359738368 : ℝ) := by
  rw [polynomial203]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error203 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded203 rnd h y - exact203 h y| ≤ (0/1 : ℝ) := by
  simp [rounded203, exact203]
def exact204 (h y : ℝ) : ℝ := exact203 h y * exact175 h y
def rounded204 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded203 rnd h y * rounded175 rnd h y)
theorem polynomial204 (h y : ℝ) : exact204 h y = evaluate [((5780575765298471/1125899906842624 : ℝ), 0, 1), ((1082989392683540531493308636036129/324518553658426726783156020576256 : ℝ), 1, 1), ((50724446503492248787198026188761074435717222317015/46768052394588893382517914646921056628989841375232 : ℝ), 2, 1), ((49495896313868844950424029289258126787281321382099169246204449317/210624583337114373395836055367340864637790190801098222508621955072 : ℝ), 3, 1), ((18111413140885060736165353099947673099220969036379700441368569986993400233103503/474284397516047136454946754595585670566993857190463750305618264096412179005177856 : ℝ), 4, 1), ((349636845567670095829825013030412246137020537986860994846768253435061830937811285334083341931811/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 5, 1), ((153477016889132807038791637818615328682334638786296431127236237178642744784606838329027999338069/273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728 : ℝ), 6, 1), ((17519458784492824626265882215213335008859214964789532516892256767577925686097937147984838671540817459055446829487/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 7, 1), ((17668175893676446844026841375670378123540380538468800204153661694505264148377095449052800073422739741876132766019/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 8, 1), ((-344390697913803150344487670288431030844003234838364663819547636044105142232306921003199891328257419774322387375/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 9, 1)] h y := by
  simp only [exact204, polynomial203, polynomial175, evaluate] <;> ring
theorem bound204 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact204 h y| ≤ (2939573738537/1099511627776 : ℝ) := by
  rw [polynomial204]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error204 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded204 rnd h y - exact204 h y| ≤ (755200974121781865512247/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded204 exact204
  apply rounded_step rnd hrnd (propagation := (44956143523770853563505944602152975/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ)) (magnitude := (2939573738537/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound203 h y hh hy) (bound175 h y hh hy)
      (error203 rnd hrnd h y hh hy) (error175 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound204 h y hh hy
  · norm_num
  · norm_num
def exact205 (h y : ℝ) : ℝ := exact202 h y + exact204 h y
def rounded205 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded202 rnd h y + rounded204 rnd h y)
theorem polynomial205 (h y : ℝ) : exact205 h y = evaluate [((4164281667427571/4503599627370496 : ℝ), 0, 1), ((138729934445386819830821078028537/324518553658426726783156020576256 : ℝ), 1, 1), ((6162245575833088026356163402156181708930356690383/46768052394588893382517914646921056628989841375232 : ℝ), 2, 1), ((6415331570407085541192820200738626162924984475207857273041727773/210624583337114373395836055367340864637790190801098222508621955072 : ℝ), 3, 1), ((5155723882268589627938309783032847985869275015701713682569414972314106266716459/948568795032094272909893509191171341133987714380927500611236528192824358010355712 : ℝ), 4, 1), ((58229418327072329135587929480448970474973376078568681631131368165150930663379353282616468198691/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 5, 1), ((478626016889864898160999348331464957172560141124500461835701840872594762091628982502205020990865/4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 : ℝ), 6, 1), ((4087793354807470264492010880723806487714359831824884649684633924915674283970937001904343098900498569120591489455/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 7, 1), ((21292319366090178786581310619744638001876661654797513620659936309310636833314025141147775847905262560872209310019/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 8, 1), ((-344390697913803150344487670288431030844003234838364663819547636044105142232306921003199891328257419774322387375/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 9, 1)] h y := by
  simp only [exact205, polynomial202, polynomial204, evaluate] <;> ring
theorem bound205 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact205 h y| ≤ (523310858207/1099511627776 : ℝ) := by
  rw [polynomial205]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error205 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded205 rnd h y - exact205 h y| ≤ (9007106833472430661176743/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded205 exact205
  apply rounded_step rnd hrnd (propagation := (35956504037197218382362267/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (523310858207/1099511627776 : ℝ))
  · convert FindOrb.add_error (error202 rnd hrnd h y hh hy) (error204 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound205 h y hh hy
  · norm_num
  · norm_num
def exact206 (h y : ℝ) : ℝ := exact205 h y * exact0 h y
def rounded206 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded205 rnd h y * rounded0 rnd h y)
theorem polynomial206 (h y : ℝ) : exact206 h y = evaluate [((4164281667427571/4503599627370496 : ℝ), 1, 1), ((138729934445386819830821078028537/324518553658426726783156020576256 : ℝ), 2, 1), ((6162245575833088026356163402156181708930356690383/46768052394588893382517914646921056628989841375232 : ℝ), 3, 1), ((6415331570407085541192820200738626162924984475207857273041727773/210624583337114373395836055367340864637790190801098222508621955072 : ℝ), 4, 1), ((5155723882268589627938309783032847985869275015701713682569414972314106266716459/948568795032094272909893509191171341133987714380927500611236528192824358010355712 : ℝ), 5, 1), ((58229418327072329135587929480448970474973376078568681631131368165150930663379353282616468198691/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 6, 1), ((478626016889864898160999348331464957172560141124500461835701840872594762091628982502205020990865/4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 : ℝ), 7, 1), ((4087793354807470264492010880723806487714359831824884649684633924915674283970937001904343098900498569120591489455/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 8, 1), ((21292319366090178786581310619744638001876661654797513620659936309310636833314025141147775847905262560872209310019/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 9, 1), ((-344390697913803150344487670288431030844003234838364663819547636044105142232306921003199891328257419774322387375/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 10, 1)] h y := by
  simp only [exact206, polynomial205, polynomial0, evaluate] <;> ring
theorem bound206 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact206 h y| ≤ (16353464319/549755813888 : ℝ) := by
  rw [polynomial206]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error206 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded206 rnd h y - exact206 h y| ≤ (1128135957205698885812661/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded206 exact206
  apply rounded_step rnd hrnd (propagation := (9007106833472430661176743/6277101735386680763835789423207666416102355444464034512896 : ℝ)) (magnitude := (16353464319/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound205 h y hh hy) (bound0 h y hh hy)
      (error205 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound206 h y hh hy
  · norm_num
  · norm_num
def exact207 (h y : ℝ) : ℝ := exact206 h y + exact3 h y
def rounded207 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded206 rnd h y + rounded3 rnd h y)
theorem polynomial207 (h y : ℝ) : exact207 h y = evaluate [((1/1 : ℝ), 0, 1), ((4164281667427571/4503599627370496 : ℝ), 1, 1), ((138729934445386819830821078028537/324518553658426726783156020576256 : ℝ), 2, 1), ((6162245575833088026356163402156181708930356690383/46768052394588893382517914646921056628989841375232 : ℝ), 3, 1), ((6415331570407085541192820200738626162924984475207857273041727773/210624583337114373395836055367340864637790190801098222508621955072 : ℝ), 4, 1), ((5155723882268589627938309783032847985869275015701713682569414972314106266716459/948568795032094272909893509191171341133987714380927500611236528192824358010355712 : ℝ), 5, 1), ((58229418327072329135587929480448970474973376078568681631131368165150930663379353282616468198691/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 6, 1), ((478626016889864898160999348331464957172560141124500461835701840872594762091628982502205020990865/4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 : ℝ), 7, 1), ((4087793354807470264492010880723806487714359831824884649684633924915674283970937001904343098900498569120591489455/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 8, 1), ((21292319366090178786581310619744638001876661654797513620659936309310636833314025141147775847905262560872209310019/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 9, 1), ((-344390697913803150344487670288431030844003234838364663819547636044105142232306921003199891328257419774322387375/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 10, 1)] h y := by
  simp only [exact207, polynomial206, polynomial3, evaluate] <;> ring
theorem bound207 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact207 h y| ≤ (291231371263/549755813888 : ℝ) := by
  rw [polynomial207]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error207 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded207 rnd h y - exact207 h y| ≤ (602970711976629131198683/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded207 exact207
  apply rounded_step rnd hrnd (propagation := (2331829778137312095044459/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (291231371263/549755813888 : ℝ))
  · convert FindOrb.add_error (error206 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound207 h y hh hy
  · norm_num
  · norm_num
def exact208 (h y : ℝ) : ℝ := exact207 h y + exact2 h y
def rounded208 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded207 rnd h y + rounded2 rnd h y)
theorem polynomial208 (h y : ℝ) : exact208 h y = evaluate [((1/1 : ℝ), 0, 1), ((4164281667427571/4503599627370496 : ℝ), 1, 1), ((138729934445386819830821078028537/324518553658426726783156020576256 : ℝ), 2, 1), ((6162245575833088026356163402156181708930356690383/46768052394588893382517914646921056628989841375232 : ℝ), 3, 1), ((6415331570407085541192820200738626162924984475207857273041727773/210624583337114373395836055367340864637790190801098222508621955072 : ℝ), 4, 1), ((5155723882268589627938309783032847985869275015701713682569414972314106266716459/948568795032094272909893509191171341133987714380927500611236528192824358010355712 : ℝ), 5, 1), ((58229418327072329135587929480448970474973376078568681631131368165150930663379353282616468198691/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 6, 1), ((478626016889864898160999348331464957172560141124500461835701840872594762091628982502205020990865/4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 : ℝ), 7, 1), ((4087793354807470264492010880723806487714359831824884649684633924915674283970937001904343098900498569120591489455/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 8, 1), ((21292319366090178786581310619744638001876661654797513620659936309310636833314025141147775847905262560872209310019/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 9, 1), ((-344390697913803150344487670288431030844003234838364663819547636044105142232306921003199891328257419774322387375/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 10, 1)] h y := by
  simp only [exact208, polynomial207, polynomial2, evaluate] <;> ring
theorem bound208 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact208 h y| ≤ (291231371263/549755813888 : ℝ) := by
  rw [polynomial208]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error208 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded208 rnd h y - exact208 h y| ≤ (2491935917675720954545005/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded208 exact208
  apply rounded_step rnd hrnd (propagation := (602970711976629131198683/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (291231371263/549755813888 : ℝ))
  · convert FindOrb.add_error (error207 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound208 h y hh hy
  · norm_num
  · norm_num
def exact209 (h y : ℝ) : ℝ := exact208 h y + exact2 h y
def rounded209 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded208 rnd h y + rounded2 rnd h y)
theorem polynomial209 (h y : ℝ) : exact209 h y = evaluate [((1/1 : ℝ), 0, 1), ((4164281667427571/4503599627370496 : ℝ), 1, 1), ((138729934445386819830821078028537/324518553658426726783156020576256 : ℝ), 2, 1), ((6162245575833088026356163402156181708930356690383/46768052394588893382517914646921056628989841375232 : ℝ), 3, 1), ((6415331570407085541192820200738626162924984475207857273041727773/210624583337114373395836055367340864637790190801098222508621955072 : ℝ), 4, 1), ((5155723882268589627938309783032847985869275015701713682569414972314106266716459/948568795032094272909893509191171341133987714380927500611236528192824358010355712 : ℝ), 5, 1), ((58229418327072329135587929480448970474973376078568681631131368165150930663379353282616468198691/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 6, 1), ((478626016889864898160999348331464957172560141124500461835701840872594762091628982502205020990865/4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 : ℝ), 7, 1), ((4087793354807470264492010880723806487714359831824884649684633924915674283970937001904343098900498569120591489455/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 8, 1), ((21292319366090178786581310619744638001876661654797513620659936309310636833314025141147775847905262560872209310019/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 9, 1), ((-344390697913803150344487670288431030844003234838364663819547636044105142232306921003199891328257419774322387375/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 10, 1)] h y := by
  simp only [exact209, polynomial208, polynomial2, evaluate] <;> ring
theorem bound209 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact209 h y| ≤ (291231371263/549755813888 : ℝ) := by
  rw [polynomial209]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error209 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded209 rnd h y - exact209 h y| ≤ (1285994493722462692147639/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded209 exact209
  apply rounded_step rnd hrnd (propagation := (2491935917675720954545005/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (291231371263/549755813888 : ℝ))
  · convert FindOrb.add_error (error208 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound209 h y hh hy
  · norm_num
  · norm_num
def exact210 (h y : ℝ) : ℝ := (4663223707248609/18014398509481984 : ℝ)
def rounded210 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (4663223707248609/18014398509481984 : ℝ)
theorem polynomial210 (h y : ℝ) : exact210 h y = evaluate [((4663223707248609/18014398509481984 : ℝ), 0, 0)] h y := by
  simp only [exact210, evaluate] <;> ring
theorem bound210 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact210 h y| ≤ (284620587601/1099511627776 : ℝ) := by
  rw [polynomial210]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error210 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded210 rnd h y - exact210 h y| ≤ (0/1 : ℝ) := by
  simp [rounded210, exact210]
def exact211 (h y : ℝ) : ℝ := exact210 h y * exact4 h y
def rounded211 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded210 rnd h y * rounded4 rnd h y)
theorem polynomial211 (h y : ℝ) : exact211 h y = evaluate [((4663223707248609/18014398509481984 : ℝ), 0, 1)] h y := by
  simp only [exact211, polynomial210, polynomial4, evaluate] <;> ring
theorem bound211 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact211 h y| ≤ (142310293801/1099511627776 : ℝ) := by
  rw [polynomial211]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error211 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded211 rnd h y - exact211 h y| ≤ (39117955696535858577409/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded211 exact211
  apply rounded_step rnd hrnd (propagation := (21505323571546017942537128348320337/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (142310293801/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound210 h y hh hy) (bound4 h y hh hy)
      (error210 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound211 h y hh hy
  · norm_num
  · norm_num
def exact212 (h y : ℝ) : ℝ := exact2 h y + exact211 h y
def rounded212 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded211 rnd h y)
theorem polynomial212 (h y : ℝ) : exact212 h y = evaluate [((4663223707248609/18014398509481984 : ℝ), 0, 1)] h y := by
  simp only [exact212, polynomial2, polynomial211, evaluate] <;> ring
theorem bound212 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact212 h y| ≤ (142310293801/1099511627776 : ℝ) := by
  rw [polynomial212]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error212 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded212 rnd h y - exact212 h y| ≤ (29338466772419073802241/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded212 exact212
  apply rounded_step rnd hrnd (propagation := (39117955696535858577409/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (142310293801/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error211 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound212 h y hh hy
  · norm_num
  · norm_num
def exact213 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded213 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial213 (h y : ℝ) : exact213 h y = evaluate [] h y := by
  simp only [exact213, evaluate] <;> ring
theorem bound213 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact213 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial213]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error213 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded213 rnd h y - exact213 h y| ≤ (0/1 : ℝ) := by
  simp [rounded213, exact213]
def exact214 (h y : ℝ) : ℝ := exact213 h y * exact11 h y
def rounded214 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded213 rnd h y * rounded11 rnd h y)
theorem polynomial214 (h y : ℝ) : exact214 h y = evaluate [] h y := by
  simp only [exact214, polynomial213, polynomial11, evaluate] <;> ring
theorem bound214 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact214 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial214]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error214 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded214 rnd h y - exact214 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded214 exact214
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound213 h y hh hy) (bound11 h y hh hy)
      (error213 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound214 h y hh hy
  · norm_num
  · norm_num
def exact215 (h y : ℝ) : ℝ := exact212 h y + exact214 h y
def rounded215 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded212 rnd h y + rounded214 rnd h y)
theorem polynomial215 (h y : ℝ) : exact215 h y = evaluate [((4663223707248609/18014398509481984 : ℝ), 0, 1)] h y := by
  simp only [exact215, polynomial212, polynomial214, evaluate] <;> ring
theorem bound215 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact215 h y| ≤ (142310293801/1099511627776 : ℝ) := by
  rw [polynomial215]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error215 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded215 rnd h y - exact215 h y| ≤ (19558977848285109157889/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded215 exact215
  apply rounded_step rnd hrnd (propagation := (58676933544838147604483/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (142310293801/1099511627776 : ℝ))
  · convert FindOrb.add_error (error212 rnd hrnd h y hh hy) (error214 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound215 h y hh hy
  · norm_num
  · norm_num
def exact216 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded216 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial216 (h y : ℝ) : exact216 h y = evaluate [] h y := by
  simp only [exact216, evaluate] <;> ring
theorem bound216 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact216 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial216]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error216 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded216 rnd h y - exact216 h y| ≤ (0/1 : ℝ) := by
  simp [rounded216, exact216]
def exact217 (h y : ℝ) : ℝ := exact216 h y * exact21 h y
def rounded217 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded216 rnd h y * rounded21 rnd h y)
theorem polynomial217 (h y : ℝ) : exact217 h y = evaluate [] h y := by
  simp only [exact217, polynomial216, polynomial21, evaluate] <;> ring
theorem bound217 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact217 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial217]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error217 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded217 rnd h y - exact217 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded217 exact217
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound216 h y hh hy) (bound21 h y hh hy)
      (error216 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound217 h y hh hy
  · norm_num
  · norm_num
def exact218 (h y : ℝ) : ℝ := exact215 h y + exact217 h y
def rounded218 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded215 rnd h y + rounded217 rnd h y)
theorem polynomial218 (h y : ℝ) : exact218 h y = evaluate [((4663223707248609/18014398509481984 : ℝ), 0, 1)] h y := by
  simp only [exact218, polynomial215, polynomial217, evaluate] <;> ring
theorem bound218 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact218 h y| ≤ (142310293801/1099511627776 : ℝ) := by
  rw [polynomial218]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error218 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded218 rnd h y - exact218 h y| ≤ (48897444620721362829315/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded218 exact218
  apply rounded_step rnd hrnd (propagation := (78235911393140436631557/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (142310293801/1099511627776 : ℝ))
  · convert FindOrb.add_error (error215 rnd hrnd h y hh hy) (error217 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound218 h y hh hy
  · norm_num
  · norm_num
def exact219 (h y : ℝ) : ℝ := (-5375593101103729/1125899906842624 : ℝ)
def rounded219 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-5375593101103729/1125899906842624 : ℝ)
theorem polynomial219 (h y : ℝ) : exact219 h y = evaluate [((-5375593101103729/1125899906842624 : ℝ), 0, 0)] h y := by
  simp only [exact219, evaluate] <;> ring
theorem bound219 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact219 h y| ≤ (5249602637797/1099511627776 : ℝ) := by
  rw [polynomial219]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error219 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded219 rnd h y - exact219 h y| ≤ (0/1 : ℝ) := by
  simp [rounded219, exact219]
def exact220 (h y : ℝ) : ℝ := exact219 h y * exact34 h y
def rounded220 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded219 rnd h y * rounded34 rnd h y)
theorem polynomial220 (h y : ℝ) : exact220 h y = evaluate [((-5375593101103729/1125899906842624 : ℝ), 0, 1), ((-5375593101103729/9007199254740992 : ℝ), 1, 1), ((-387352305392418601893136661769615/10384593717069655257060992658440192 : ℝ), 2, 1), ((-32279358782701548813863113204869/20769187434139310514121985316880384 : ℝ), 3, 1)] h y := by
  simp only [exact220, polynomial219, polynomial34, evaluate] <;> ring
theorem bound220 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact220 h y| ≤ (1322693945191/549755813888 : ℝ) := by
  rw [polynomial220]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error220 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded220 rnd h y - exact220 h y| ≤ (917114657960499511929241/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded220 exact220
  apply rounded_step rnd hrnd (propagation := (1616996745415422320755095579840876409/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (1322693945191/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound219 h y hh hy) (bound34 h y hh hy)
      (error219 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound220 h y hh hy
  · norm_num
  · norm_num
def exact221 (h y : ℝ) : ℝ := exact218 h y + exact220 h y
def rounded221 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded218 rnd h y + rounded220 rnd h y)
theorem polynomial221 (h y : ℝ) : exact221 h y = evaluate [((-81346265910411055/18014398509481984 : ℝ), 0, 1), ((-5375593101103729/9007199254740992 : ℝ), 1, 1), ((-387352305392418601893136661769615/10384593717069655257060992658440192 : ℝ), 2, 1), ((-32279358782701548813863113204869/20769187434139310514121985316880384 : ℝ), 3, 1)] h y := by
  simp only [exact221, polynomial218, polynomial220, evaluate] <;> ring
theorem bound221 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact221 h y| ≤ (1251538798291/549755813888 : ℝ) := by
  rw [polynomial221]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error221 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded221 rnd h y - exact221 h y| ≤ (2276044570495880833749817/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded221 exact221
  apply rounded_step rnd hrnd (propagation := (241503025645305218689639/196159429230833773869868419475239575503198607639501078528 : ℝ)) (magnitude := (1251538798291/549755813888 : ℝ))
  · convert FindOrb.add_error (error218 rnd hrnd h y hh hy) (error220 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound221 h y hh hy
  · norm_num
  · norm_num
def exact222 (h y : ℝ) : ℝ := (-7837938938870999/18014398509481984 : ℝ)
def rounded222 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-7837938938870999/18014398509481984 : ℝ)
theorem polynomial222 (h y : ℝ) : exact222 h y = evaluate [((-7837938938870999/18014398509481984 : ℝ), 0, 0)] h y := by
  simp only [exact222, evaluate] <;> ring
theorem bound222 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact222 h y| ≤ (119597456953/274877906944 : ℝ) := by
  rw [polynomial222]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error222 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded222 rnd h y - exact222 h y| ≤ (0/1 : ℝ) := by
  simp [rounded222, exact222]
def exact223 (h y : ℝ) : ℝ := exact222 h y * exact50 h y
def rounded223 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded222 rnd h y * rounded50 rnd h y)
theorem polynomial223 (h y : ℝ) : exact223 h y = evaluate [((-7837938938870999/18014398509481984 : ℝ), 0, 1), ((-39189694694354995/288230376151711744 : ℝ), 1, 1), ((-7059787776890426580471138000875775/332306998946228968225951765070086144 : ℝ), 2, 1), ((-23532625922968088405621986531144275/10633823966279326983230456482242756608 : ℝ), 3, 1), ((-3529893888445212996312858792775425/21267647932558653966460912964485513216 : ℝ), 4, 1)] h y := by
  simp only [exact223, polynomial222, polynomial50, evaluate] <;> ring
theorem bound223 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact223 h y| ≤ (121956305397/549755813888 : ℝ) := by
  rw [polynomial223]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error223 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded223 rnd h y - exact223 h y| ≤ (197024223319845001601507/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded223 exact223
  apply rounded_step rnd hrnd (propagation := (22471424109861856784380866602539259/215679573337205118357336120696157045389097155380324579848828881993728 : ℝ)) (magnitude := (121956305397/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound222 h y hh hy) (bound50 h y hh hy)
      (error222 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound223 h y hh hy
  · norm_num
  · norm_num
def exact224 (h y : ℝ) : ℝ := exact221 h y + exact223 h y
def rounded224 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded221 rnd h y + rounded223 rnd h y)
theorem polynomial224 (h y : ℝ) : exact224 h y = evaluate [((-44592102424641027/9007199254740992 : ℝ), 0, 1), ((-211208673929674323/288230376151711744 : ℝ), 1, 1), ((-19455061549447821841051511177503455/332306998946228968225951765070086144 : ℝ), 2, 1), ((-40059657619711281398319900492037203/10633823966279326983230456482242756608 : ℝ), 3, 1), ((-3529893888445212996312858792775425/21267647932558653966460912964485513216 : ℝ), 4, 1)] h y := by
  simp only [exact224, polynomial221, polynomial223, evaluate] <;> ring
theorem bound224 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact224 h y| ≤ (2746990207375/1099511627776 : ℝ) := by
  rw [polynomial224]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error224 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded224 rnd h y - exact224 h y| ≤ (2850612253115178091607325/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded224 exact224
  apply rounded_step rnd hrnd (propagation := (618267198453931458837831/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (2746990207375/1099511627776 : ℝ))
  · convert FindOrb.add_error (error221 rnd hrnd h y hh hy) (error223 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound224 h y hh hy
  · norm_num
  · norm_num
def exact225 (h y : ℝ) : ℝ := (-6866825998996543/2251799813685248 : ℝ)
def rounded225 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-6866825998996543/2251799813685248 : ℝ)
theorem polynomial225 (h y : ℝ) : exact225 h y = evaluate [((-6866825998996543/2251799813685248 : ℝ), 0, 0)] h y := by
  simp only [exact225, evaluate] <;> ring
theorem bound225 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact225 h y| ≤ (3352942382323/1099511627776 : ℝ) := by
  rw [polynomial225]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error225 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded225 rnd h y - exact225 h y| ≤ (0/1 : ℝ) := by
  simp [rounded225, exact225]
def exact226 (h y : ℝ) : ℝ := exact225 h y * exact69 h y
def rounded226 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded225 rnd h y * rounded69 rnd h y)
theorem polynomial226 (h y : ℝ) : exact226 h y = evaluate [((-6866825998996543/2251799813685248 : ℝ), 0, 1), ((-371105220123586373066138211347393/324518553658426726783156020576256 : ℝ), 1, 1), ((-278328915092689778082897158761409/1298074214633706907132624082305024 : ℝ), 2, 1), ((-40111423945531907938848212757209358003791124372165/1496577676626844588240573268701473812127674924007424 : ℝ), 3, 1), ((-120334271836595722569218759522907208792774773893409/47890485652059026823698344598447161988085597568237568 : ℝ), 4, 1), ((-16713093310638293595761111106346216807320374338875/95780971304118053647396689196894323976171195136475136 : ℝ), 5, 1)] h y := by
  simp only [exact226, polynomial225, polynomial69, evaluate] <;> ring
theorem bound226 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact226 h y| ≤ (429056889939/274877906944 : ℝ) := by
  rw [polynomial226]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error226 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded226 rnd h y - exact226 h y| ≤ (152185377205353034880107/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded226 exact226
  apply rounded_step rnd hrnd (propagation := (16863871224260837359547529709122259/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ)) (magnitude := (429056889939/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound225 h y hh hy) (bound69 h y hh hy)
      (error225 rnd hrnd h y hh hy) (error69 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound226 h y hh hy
  · norm_num
  · norm_num
def exact227 (h y : ℝ) : ℝ := exact224 h y + exact226 h y
def rounded227 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded224 rnd h y + rounded226 rnd h y)
theorem polynomial227 (h y : ℝ) : exact227 h y = evaluate [((-72059406420627199/9007199254740992 : ℝ), 0, 1), ((-608905046425360841603769746090945/324518553658426726783156020576256 : ℝ), 1, 1), ((-90707263813176405030273183820424159/332306998946228968225951765070086144 : ℝ), 2, 1), ((-45749319543304450990805653169570851558591783639749/1496577676626844588240573268701473812127674924007424 : ℝ), 3, 1), ((-128282886236925348782330529957271710420802073323809/47890485652059026823698344598447161988085597568237568 : ℝ), 4, 1), ((-16713093310638293595761111106346216807320374338875/95780971304118053647396689196894323976171195136475136 : ℝ), 5, 1)] h y := by
  simp only [exact227, polynomial224, polynomial226, evaluate] <;> ring
theorem bound227 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact227 h y| ≤ (4463217767131/1099511627776 : ℝ) := by
  rw [polynomial227]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error227 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded227 rnd h y - exact227 h y| ≤ (2340757624895061805288507/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded227 exact227
  apply rounded_step rnd hrnd (propagation := (4068095270758002370648181/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (4463217767131/1099511627776 : ℝ))
  · convert FindOrb.add_error (error224 rnd hrnd h y hh hy) (error226 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound227 h y hh hy
  · norm_num
  · norm_num
def exact228 (h y : ℝ) : ℝ := (1570044913334915/281474976710656 : ℝ)
def rounded228 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1570044913334915/281474976710656 : ℝ)
theorem polynomial228 (h y : ℝ) : exact228 h y = evaluate [((1570044913334915/281474976710656 : ℝ), 0, 0)] h y := by
  simp only [exact228, evaluate] <;> ring
theorem bound228 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact228 h y| ≤ (6132987942715/1099511627776 : ℝ) := by
  rw [polynomial228]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error228 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded228 rnd h y - exact228 h y| ≤ (0/1 : ℝ) := by
  simp [rounded228, exact228]
def exact229 (h y : ℝ) : ℝ := exact228 h y * exact91 h y
def rounded229 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded228 rnd h y * rounded91 rnd h y)
theorem polynomial229 (h y : ℝ) : exact229 h y = evaluate [((1570044913334915/281474976710656 : ℝ), 0, 1), ((133497717603953238356074300763315/162259276829213363391578010288128 : ℝ), 1, 1), ((1418879840164102075268625690349518917592173021165/23384026197294446691258957323460528314494920687616 : ℝ), 2, 1), ((1116185474262426630355046823975925249389413452105/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((11863371866876507092064556512058565179479974840360844613585643425/107839786668602559178668060348078522694548577690162289924414440996864 : ℝ), 4, 1), ((16473307999767905898928041512227146208643235715248818855115895245/3450873173395281893717377931138512726225554486085193277581262111899648 : ℝ), 5, 1), ((28299475478188993738191150376288005321064118098695881850995169375/6901746346790563787434755862277025452451108972170386555162524223799296 : ℝ), 6, 1)] h y := by
  simp only [exact229, polynomial228, polynomial91, evaluate] <;> ring
theorem bound229 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact229 h y| ≤ (386861739691/137438953472 : ℝ) := by
  rw [polynomial229]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error229 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded229 rnd h y - exact229 h y| ≤ (2165655090903721329524297/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded229 exact229
  apply rounded_step rnd hrnd (propagation := (1913475808467448396200475676842913515/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (386861739691/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound228 h y hh hy) (bound91 h y hh hy)
      (error228 rnd hrnd h y hh hy) (error91 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound229 h y hh hy
  · norm_num
  · norm_num
def exact230 (h y : ℝ) : ℝ := exact227 h y + exact229 h y
def rounded230 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded227 rnd h y + rounded229 rnd h y)
theorem polynomial230 (h y : ℝ) : exact230 h y = evaluate [((-21817969193909919/9007199254740992 : ℝ), 0, 1), ((-341909611217454364891621144564315/324518553658426726783156020576256 : ℝ), 1, 1), ((-4964076402161187515251153055273305628765960763411/23384026197294446691258957323460528314494920687616 : ℝ), 2, 1), ((-41284577646254744469385465873667150561034129831329/1496577676626844588240573268701473812127674924007424 : ℝ), 3, 1), ((-277004007460437858219027729952311201328432810202638329175124826207/107839786668602559178668060348078522694548577690162289924414440996864 : ℝ), 4, 1), ((-585679338448223681213107750357384757525484897759173509230330760755/3450873173395281893717377931138512726225554486085193277581262111899648 : ℝ), 5, 1), ((28299475478188993738191150376288005321064118098695881850995169375/6901746346790563787434755862277025452451108972170386555162524223799296 : ℝ), 6, 1)] h y := by
  simp only [exact230, polynomial227, polynomial229, evaluate] <;> ring
theorem bound230 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact230 h y| ≤ (342080962401/274877906944 : ℝ) := by
  rw [polynomial230]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error230 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded230 rnd h y - exact230 h y| ≤ (109925489665534328464475/24519928653854221733733552434404946937899825954937634816 : ℝ) := by
  unfold rounded230 exact230
  apply rounded_step rnd hrnd (propagation := (6847170340693844940101311/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (342080962401/274877906944 : ℝ))
  · convert FindOrb.add_error (error227 rnd hrnd h y hh hy) (error229 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound230 h y hh hy
  · norm_num
  · norm_num
def exact231 (h y : ℝ) : ℝ := (6930850213563427/1125899906842624 : ℝ)
def rounded231 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (6930850213563427/1125899906842624 : ℝ)
theorem polynomial231 (h y : ℝ) : exact231 h y = evaluate [((6930850213563427/1125899906842624 : ℝ), 0, 0)] h y := by
  simp only [exact231, evaluate] <;> ring
theorem bound231 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact231 h y| ≤ (1692102102921/274877906944 : ℝ) := by
  rw [polynomial231]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error231 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded231 rnd h y - exact231 h y| ≤ (0/1 : ℝ) := by
  simp [rounded231, exact231]
def exact232 (h y : ℝ) : ℝ := exact231 h y * exact116 h y
def rounded232 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded231 rnd h y * rounded116 rnd h y)
theorem polynomial232 (h y : ℝ) : exact232 h y = evaluate [((6930850213563427/1125899906842624 : ℝ), 0, 1), ((464460963654774821513882897119595/162259276829213363391578010288128 : ℝ), 1, 1), ((1945323987244720391496787165141521776219389443125/2923003274661805836407369665432566039311865085952 : ℝ), 2, 1), ((43454363504988242769322173634086412168169851253462377543054205317/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 3, 1), ((40412558059639066364562051646709052193838040922038507374769089441/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 4, 1), ((2064275372027548110040580591895404055880222693341682389425096644512835214159226777/1942668892225729070919461906823518906642406839052139521251812409738904285205208498176 : ℝ), 5, 1), ((4256514485957588353866653270758968751217037480001407244538411598947853913461087333/62165404551223330269422781018352605012557018849668464680057997111644937126566671941632 : ℝ), 6, 1), ((-97171692844218075771765250511936880639201991531295101837804073603590155052361625/124330809102446660538845562036705210025114037699336929360115994223289874253133343883264 : ℝ), 7, 1)] h y := by
  simp only [exact232, polynomial231, polynomial116, evaluate] <;> ring
theorem bound232 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact232 h y| ≤ (871000196359/274877906944 : ℝ) := by
  rw [polynomial232]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error232 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded232 rnd h y - exact232 h y| ≤ (2573571414426672173602993/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded232 exact232
  apply rounded_step rnd hrnd (propagation := (575796095485037374737481309187049429/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (871000196359/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound231 h y hh hy) (bound116 h y hh hy)
      (error231 rnd hrnd h y hh hy) (error116 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound232 h y hh hy
  · norm_num
  · norm_num
def exact233 (h y : ℝ) : ℝ := exact230 h y + exact232 h y
def rounded233 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded230 rnd h y + rounded232 rnd h y)
theorem polynomial233 (h y : ℝ) : exact233 h y = evaluate [((33628832514597497/9007199254740992 : ℝ), 0, 1), ((587012316092095278136144649674875/324518553658426726783156020576256 : ℝ), 1, 1), ((10598515495796575616723144265858868580989154781589/23384026197294446691258957323460528314494920687616 : ℝ), 2, 1), ((31833787973499419268138955206911534296097580474905892650537263493/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 3, 1), ((1016197850448012265446957922742378468874384499302593906817486035905/107839786668602559178668060348078522694548577690162289924414440996864 : ℝ), 4, 1), ((1734567215728295762327876585268521720909764086883368763840323967050504606169016217/1942668892225729070919461906823518906642406839052139521251812409738904285205208498176 : ℝ), 5, 1), ((4511413500394293236469833490585721628933700636665014632917756286584490172256607333/62165404551223330269422781018352605012557018849668464680057997111644937126566671941632 : ℝ), 6, 1), ((-97171692844218075771765250511936880639201991531295101837804073603590155052361625/124330809102446660538845562036705210025114037699336929360115994223289874253133343883264 : ℝ), 7, 1)] h y := by
  simp only [exact233, polynomial230, polynomial232, evaluate] <;> ring
theorem bound233 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact233 h y| ≤ (2115676935833/1099511627776 : ℝ) := by
  rw [polynomial233]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error233 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded233 rnd h y - exact233 h y| ≤ (4949789588483302205945785/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded233 exact233
  apply rounded_step rnd hrnd (propagation := (9608802753020869195329393/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (2115676935833/1099511627776 : ℝ))
  · convert FindOrb.add_error (error230 rnd hrnd h y hh hy) (error232 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound233 h y hh hy
  · norm_num
  · norm_num
def exact234 (h y : ℝ) : ℝ := (-5699423082634739/1125899906842624 : ℝ)
def rounded234 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-5699423082634739/1125899906842624 : ℝ)
theorem polynomial234 (h y : ℝ) : exact234 h y = evaluate [((-5699423082634739/1125899906842624 : ℝ), 0, 0)] h y := by
  simp only [exact234, evaluate] <;> ring
theorem bound234 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact234 h y| ≤ (695730356767/137438953472 : ℝ) := by
  rw [polynomial234]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error234 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded234 rnd h y - exact234 h y| ≤ (0/1 : ℝ) := by
  simp [rounded234, exact234]
def exact235 (h y : ℝ) : ℝ := exact234 h y * exact144 h y
def rounded235 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded234 rnd h y * rounded144 rnd h y)
theorem polynomial235 (h y : ℝ) : exact235 h y = evaluate [((-5699423082634739/1125899906842624 : ℝ), 0, 1), ((-115991368248840133674336403646971/40564819207303340847894502572032 : ℝ), 1, 1), ((-4721178727450604733075557563796637902615363682049/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((-64055135921015677943828983214098099398558277460373425296225725601/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 3, 1), ((-81475821665635114031120299695087400499285711960969877819953807195325383727236619/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 4, 1), ((-4755602805024690510817035113573353318865906338470048745988663035992232685429722741/1942668892225729070919461906823518906642406839052139521251812409738904285205208498176 : ℝ), 5, 1), ((-4009939706106818267631410332933278157638654993003276387815491720708700124364490239335744530341431/17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592 : ℝ), 6, 1), ((-8632874580237354450647485626058578010279637819676772309518302514571555143201426866681850453864747/559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944 : ℝ), 7, 1), ((152322527456756354308356987817520050571298420221809357848610937071219657963565710661783401848375/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888 : ℝ), 8, 1)] h y := by
  simp only [exact235, polynomial234, polynomial144, evaluate] <;> ring
theorem bound235 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact235 h y| ≤ (1441462407651/549755813888 : ℝ) := by
  rw [polynomial235]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error235 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded235 rnd h y - exact235 h y| ≤ (1159146919714089479234213/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded235 exact235
  apply rounded_step rnd hrnd (propagation := (66041742262483104465021018864483645/53919893334301279589334030174039261347274288845081144962207220498432 : ℝ)) (magnitude := (1441462407651/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound234 h y hh hy) (bound144 h y hh hy)
      (error234 rnd hrnd h y hh hy) (error144 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound235 h y hh hy
  · norm_num
  · norm_num
def exact236 (h y : ℝ) : ℝ := exact233 h y + exact235 h y
def rounded236 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded233 rnd h y + rounded235 rnd h y)
theorem polynomial236 (h y : ℝ) : exact236 h y = evaluate [((-11966552146480415/9007199254740992 : ℝ), 0, 1), ((-340918629898625791258546579500893/324518553658426726783156020576256 : ℝ), 1, 1), ((-8286199414005843315579085989327683029472299946607/23384026197294446691258957323460528314494920687616 : ℝ), 2, 1), ((-8055336986879064668922507001796641275615174246366883161422115527/105312291668557186697918027683670432318895095400549111254310977536 : ℝ), 3, 1), ((-45721538379600996372073960308788130092567982319424349395506020472827587525723659/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 4, 1), ((-755258897324098687122289632076207899489035562896669995537084767235432019815176631/485667223056432267729865476705879726660601709763034880312953102434726071301302124544 : ℝ), 5, 1), ((-2740089696151195515822894772189959947106174110775298714325504820997680619557338376582953981500983/17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592 : ℝ), 6, 1), ((-9070496979921535269311876765596834443227561996844071870036342665002263369409950584587244101480747/559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944 : ℝ), 7, 1), ((152322527456756354308356987817520050571298420221809357848610937071219657963565710661783401848375/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888 : ℝ), 8, 1)] h y := by
  simp only [exact236, polynomial233, polynomial235, evaluate] <;> ring
theorem bound236 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact236 h y| ≤ (767247879469/1099511627776 : ℝ) := by
  rw [polynomial236]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error236 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded236 rnd h y - exact236 h y| ≤ (12323322762002613925426365/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded236 exact236
  apply rounded_step rnd hrnd (propagation := (3054468254098695842589999/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (767247879469/1099511627776 : ℝ))
  · convert FindOrb.add_error (error233 rnd hrnd h y hh hy) (error235 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound236 h y hh hy
  · norm_num
  · norm_num
def exact237 (h y : ℝ) : ℝ := (2470141274003721/1125899906842624 : ℝ)
def rounded237 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (2470141274003721/1125899906842624 : ℝ)
theorem polynomial237 (h y : ℝ) : exact237 h y = evaluate [((2470141274003721/1125899906842624 : ℝ), 0, 0)] h y := by
  simp only [exact237, evaluate] <;> ring
theorem bound237 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact237 h y| ≤ (2412247337895/1099511627776 : ℝ) := by
  rw [polynomial237]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error237 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded237 rnd h y - exact237 h y| ≤ (0/1 : ℝ) := by
  simp [rounded237, exact237]
def exact238 (h y : ℝ) : ℝ := exact237 h y * exact175 h y
def rounded238 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded237 rnd h y * rounded175 rnd h y)
theorem polynomial238 (h y : ℝ) : exact238 h y = evaluate [((2470141274003721/1125899906842624 : ℝ), 0, 1), ((462780336560074544925590463480879/324518553658426726783156020576256 : ℝ), 1, 1), ((21675444453377983352550972383753466375567602258265/46768052394588893382517914646921056628989841375232 : ℝ), 2, 1), ((21150463438719977886478682630169926117535195331313248383189641067/210624583337114373395836055367340864637790190801098222508621955072 : ℝ), 3, 1), ((7739324064983273199896632434626954165029368232499799482524807454923776390366753/474284397516047136454946754595585670566993857190463750305618264096412179005177856 : ℝ), 4, 1), ((149405948164157229011362879872285766186688264835051259534865744225745377539866428793348453722061/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 5, 1), ((65583417538553509210460422429781449261671357860207673528402293936190185054726758719172574517819/273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728 : ℝ), 6, 1), ((7486371600139094856142753485291886160891199184032438509240316401043477865293854882125404370062625136835743188737/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 7, 1), ((7549921025743071071939068536486562004909376670468830943056020295062253945711660726828738616143778700588054308269/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 8, 1), ((-147164177382926853580721818178763580450648924763093071504386294739752632789878021602002178533806493521111418625/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 9, 1)] h y := by
  simp only [exact238, polynomial237, polynomial175, evaluate] <;> ring
theorem bound238 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact238 h y| ≤ (157016418311/137438953472 : ℝ) := by
  rw [polynomial238]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error238 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded238 rnd h y - exact238 h y| ≤ (645421207882080868951239/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded238 exact238
  apply rounded_step rnd hrnd (propagation := (614737521779789246027240210759845005/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (157016418311/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound237 h y hh hy) (bound175 h y hh hy)
      (error237 rnd hrnd h y hh hy) (error175 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound238 h y hh hy
  · norm_num
  · norm_num
def exact239 (h y : ℝ) : ℝ := exact236 h y + exact238 h y
def rounded239 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded236 rnd h y + rounded238 rnd h y)
theorem polynomial239 (h y : ℝ) : exact239 h y = evaluate [((7794578045549353/9007199254740992 : ℝ), 0, 1), ((60930853330724376833521941989993/162259276829213363391578010288128 : ℝ), 1, 1), ((5103045625366296721392800405098100316623002365051/46768052394588893382517914646921056628989841375232 : ℝ), 2, 1), ((5039789464961848548633668626576643566304846838579482060345410013/210624583337114373395836055367340864637790190801098222508621955072 : ℝ), 3, 1), ((16193054140265189227099099168227503227666963540574046464692439166562623597210365/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 4, 1), ((43112707896749024453296549947647111460470115660667892305057267067764714304080656733218443782093/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 5, 1), ((1457249026316229073646572263316052805640792792277992391492241990918491223945174181444090787639433/17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592 : ℝ), 6, 1), ((2380135747784115408991088250373030770260328476659391501660365581779807355713467978106847678040890395897795708673/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 7, 1), ((8921920381531831197990298087613873753662097892215018264597246732077342509273502151875272402656740428202735396269/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 8, 1), ((-147164177382926853580721818178763580450648924763093071504386294739752632789878021602002178533806493521111418625/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 9, 1)] h y := by
  simp only [exact239, polynomial236, polynomial238, evaluate] <;> ring
theorem bound239 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact239 h y| ≤ (488883467019/1099511627776 : ℝ) := by
  rw [polynomial239]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error239 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded239 rnd h y - exact239 h y| ≤ (3420339202460907512717203/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded239 exact239
  apply rounded_step rnd hrnd (propagation := (13614165177766775663328843/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (488883467019/1099511627776 : ℝ))
  · convert FindOrb.add_error (error236 rnd hrnd h y hh hy) (error238 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound239 h y hh hy
  · norm_num
  · norm_num
def exact240 (h y : ℝ) : ℝ := (1212621209191633/9007199254740992 : ℝ)
def rounded240 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1212621209191633/9007199254740992 : ℝ)
theorem polynomial240 (h y : ℝ) : exact240 h y = evaluate [((1212621209191633/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact240, evaluate] <;> ring
theorem bound240 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact240 h y| ≤ (148025049951/1099511627776 : ℝ) := by
  rw [polynomial240]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error240 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded240 rnd h y - exact240 h y| ≤ (0/1 : ℝ) := by
  simp [rounded240, exact240]
def exact241 (h y : ℝ) : ℝ := exact240 h y * exact209 h y
def rounded241 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded240 rnd h y * rounded209 rnd h y)
theorem polynomial241 (h y : ℝ) : exact241 h y = evaluate [((1212621209191633/9007199254740992 : ℝ), 0, 1), ((5049696270970570854727486713443/40564819207303340847894502572032 : ℝ), 1, 1), ((168226860858240943463488243546287609087075630921/2923003274661805836407369665432566039311865085952 : ℝ), 2, 1), ((7472469681502509991157056887078892931952210796120923176695165439/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 3, 1), ((7779367126272297925959477957454699264213270798112585962672810352348942975323309/1897137590064188545819787018382342682267975428761855001222473056385648716020711424 : ℝ), 4, 1), ((6251940128374717652086190022688521929989948943569792808213132708282057768289658098988606187547/8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304 : ℝ), 5, 1), ((70610227662299883309114411621628894130294397102236206687142963869268030684094611699019875958014374287738752403/615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544 : ℝ), 6, 1), ((580392059351562932149308386451199957226526724093451587076378522645412526246556457585168834523658149043327432545/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 : ℝ), 7, 1), ((4956944920832156658321671954219854539319975874588694217838220378826675626212412358172282401425464126661380961034319159993730015/2839213766779714416208296124562517712318911565184836172974571090549372219192960637992933791850638927971728600024477257552869537611776 : ℝ), 8, 1), ((25819518056202697240292341091928218503096545938938131919772431272927187968135309911593478176221451333088923728343919679677871027/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 9, 1), ((-417615464538586376572057244340715821055554396763337550125518747874626127034896978127371417283746333004867274658051558434833375/181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 : ℝ), 10, 1)] h y := by
  simp only [exact241, polynomial240, polynomial209, evaluate] <;> ring
theorem bound241 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact241 h y| ≤ (9801974165/137438953472 : ℝ) := by
  rw [polynomial241]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error241 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded241 rnd h y - exact241 h y| ≤ (357039114525124239024355/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded241 exact241
  apply rounded_step rnd hrnd (propagation := (190359399169978495935888198441715689/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (9801974165/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound240 h y hh hy) (bound209 h y hh hy)
      (error240 rnd hrnd h y hh hy) (error209 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound241 h y hh hy
  · norm_num
  · norm_num
def exact242 (h y : ℝ) : ℝ := exact239 h y + exact241 h y
def rounded242 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded239 rnd h y + rounded241 rnd h y)
theorem polynomial242 (h y : ℝ) : exact242 h y = evaluate [((4503599627370493/4503599627370496 : ℝ), 0, 1), ((81129638414606660252431888843765/162259276829213363391578010288128 : ℝ), 1, 1), ((7794675399098151816808612301838702062016212459787/46768052394588893382517914646921056628989841375232 : ℝ), 2, 1), ((17552048611426207088424394140232180064561904473279887297385985465/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 3, 1), ((31751788392809785079018055083136901756093505136799218390038059871260509547856983/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 4, 1), ((93128228923746765669986070129155286900389707209226234770762328734021176450397921525127293282469/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 5, 1), ((121882619630298222179234067729195156910495351911346723726214261312803688123388340109241976318134659676400864659/615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544 : ℝ), 6, 1), ((7023272222596618866185555341982630428072542269407004198271393762943107565685919638788198354230155588244415169033/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 7, 1), ((7468242252438155938669927388502808829150369857192058910395248072249845012785107072077593001199806059510404155578329550308672479/2839213766779714416208296124562517712318911565184836172974571090549372219192960637992933791850638927971728600024477257552869537611776 : ℝ), 8, 1), ((25156749521778662287274253829643333912109859757964471275549965896453236844374647892693084575031957602839007256175331130647983027/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 9, 1), ((-417615464538586376572057244340715821055554396763337550125518747874626127034896978127371417283746333004867274658051558434833375/181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 : ℝ), 10, 1)] h y := by
  simp only [exact242, polynomial239, polynomial241, evaluate] <;> ring
theorem bound242 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact242 h y| ≤ (567299260339/1099511627776 : ℝ) := by
  rw [polynomial242]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error242 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded242 rnd h y - exact242 h y| ≤ (882272808813449132865011/98079714615416886934934209737619787751599303819750539264 : ℝ) := by
  unfold rounded242 exact242
  apply rounded_step rnd hrnd (propagation := (14038395924368754289893167/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (567299260339/1099511627776 : ℝ))
  · convert FindOrb.add_error (error239 rnd hrnd h y hh hy) (error241 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound242 h y hh hy
  · norm_num
  · norm_num
def exact243 (h y : ℝ) : ℝ := exact242 h y * exact0 h y
def rounded243 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded242 rnd h y * rounded0 rnd h y)
theorem polynomial243 (h y : ℝ) : exact243 h y = evaluate [((4503599627370493/4503599627370496 : ℝ), 1, 1), ((81129638414606660252431888843765/162259276829213363391578010288128 : ℝ), 2, 1), ((7794675399098151816808612301838702062016212459787/46768052394588893382517914646921056628989841375232 : ℝ), 3, 1), ((17552048611426207088424394140232180064561904473279887297385985465/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 4, 1), ((31751788392809785079018055083136901756093505136799218390038059871260509547856983/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 5, 1), ((93128228923746765669986070129155286900389707209226234770762328734021176450397921525127293282469/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 6, 1), ((121882619630298222179234067729195156910495351911346723726214261312803688123388340109241976318134659676400864659/615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544 : ℝ), 7, 1), ((7023272222596618866185555341982630428072542269407004198271393762943107565685919638788198354230155588244415169033/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 8, 1), ((7468242252438155938669927388502808829150369857192058910395248072249845012785107072077593001199806059510404155578329550308672479/2839213766779714416208296124562517712318911565184836172974571090549372219192960637992933791850638927971728600024477257552869537611776 : ℝ), 9, 1), ((25156749521778662287274253829643333912109859757964471275549965896453236844374647892693084575031957602839007256175331130647983027/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 10, 1), ((-417615464538586376572057244340715821055554396763337550125518747874626127034896978127371417283746333004867274658051558434833375/181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 : ℝ), 11, 1)] h y := by
  simp only [exact243, polynomial242, polynomial0, evaluate] <;> ring
theorem bound243 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact243 h y| ≤ (8864050943/274877906944 : ℝ) := by
  rw [polynomial243]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error243 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded243 rnd h y - exact243 h y| ≤ (221786468088490697940349/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded243 exact243
  apply rounded_step rnd hrnd (propagation := (882272808813449132865011/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (8864050943/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound242 h y hh hy) (bound0 h y hh hy)
      (error242 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound243 h y hh hy
  · norm_num
  · norm_num
def exact244 (h y : ℝ) : ℝ := exact243 h y + exact3 h y
def rounded244 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded243 rnd h y + rounded3 rnd h y)
theorem polynomial244 (h y : ℝ) : exact244 h y = evaluate [((1/1 : ℝ), 0, 1), ((4503599627370493/4503599627370496 : ℝ), 1, 1), ((81129638414606660252431888843765/162259276829213363391578010288128 : ℝ), 2, 1), ((7794675399098151816808612301838702062016212459787/46768052394588893382517914646921056628989841375232 : ℝ), 3, 1), ((17552048611426207088424394140232180064561904473279887297385985465/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 4, 1), ((31751788392809785079018055083136901756093505136799218390038059871260509547856983/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 5, 1), ((93128228923746765669986070129155286900389707209226234770762328734021176450397921525127293282469/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 6, 1), ((121882619630298222179234067729195156910495351911346723726214261312803688123388340109241976318134659676400864659/615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544 : ℝ), 7, 1), ((7023272222596618866185555341982630428072542269407004198271393762943107565685919638788198354230155588244415169033/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 8, 1), ((7468242252438155938669927388502808829150369857192058910395248072249845012785107072077593001199806059510404155578329550308672479/2839213766779714416208296124562517712318911565184836172974571090549372219192960637992933791850638927971728600024477257552869537611776 : ℝ), 9, 1), ((25156749521778662287274253829643333912109859757964471275549965896453236844374647892693084575031957602839007256175331130647983027/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 10, 1), ((-417615464538586376572057244340715821055554396763337550125518747874626127034896978127371417283746333004867274658051558434833375/181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 : ℝ), 11, 1)] h y := by
  simp only [exact244, polynomial243, polynomial3, evaluate] <;> ring
theorem bound244 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact244 h y| ≤ (146303004415/274877906944 : ℝ) := by
  rw [polynomial244]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error244 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded244 rnd h y - exact244 h y| ≤ (521567331673152548748027/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded244 exact244
  apply rounded_step rnd hrnd (propagation := (962703736079877115180533/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (146303004415/274877906944 : ℝ))
  · convert FindOrb.add_error (error243 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound244 h y hh hy
  · norm_num
  · norm_num
def exact245 (h y : ℝ) : ℝ := exact244 h y + exact2 h y
def rounded245 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded244 rnd h y + rounded2 rnd h y)
theorem polynomial245 (h y : ℝ) : exact245 h y = evaluate [((1/1 : ℝ), 0, 1), ((4503599627370493/4503599627370496 : ℝ), 1, 1), ((81129638414606660252431888843765/162259276829213363391578010288128 : ℝ), 2, 1), ((7794675399098151816808612301838702062016212459787/46768052394588893382517914646921056628989841375232 : ℝ), 3, 1), ((17552048611426207088424394140232180064561904473279887297385985465/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 4, 1), ((31751788392809785079018055083136901756093505136799218390038059871260509547856983/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 5, 1), ((93128228923746765669986070129155286900389707209226234770762328734021176450397921525127293282469/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 6, 1), ((121882619630298222179234067729195156910495351911346723726214261312803688123388340109241976318134659676400864659/615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544 : ℝ), 7, 1), ((7023272222596618866185555341982630428072542269407004198271393762943107565685919638788198354230155588244415169033/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 8, 1), ((7468242252438155938669927388502808829150369857192058910395248072249845012785107072077593001199806059510404155578329550308672479/2839213766779714416208296124562517712318911565184836172974571090549372219192960637992933791850638927971728600024477257552869537611776 : ℝ), 9, 1), ((25156749521778662287274253829643333912109859757964471275549965896453236844374647892693084575031957602839007256175331130647983027/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 10, 1), ((-417615464538586376572057244340715821055554396763337550125518747874626127034896978127371417283746333004867274658051558434833375/181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 : ℝ), 11, 1)] h y := by
  simp only [exact245, polynomial244, polynomial2, evaluate] <;> ring
theorem bound245 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact245 h y| ≤ (146303004415/274877906944 : ℝ) := by
  rw [polynomial245]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error245 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded245 rnd h y - exact245 h y| ≤ (1123565590612733079811575/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded245 exact245
  apply rounded_step rnd hrnd (propagation := (521567331673152548748027/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (146303004415/274877906944 : ℝ))
  · convert FindOrb.add_error (error244 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound245 h y hh hy
  · norm_num
  · norm_num
def exact246 (h y : ℝ) : ℝ := exact245 h y + exact2 h y
def rounded246 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded245 rnd h y + rounded2 rnd h y)
theorem polynomial246 (h y : ℝ) : exact246 h y = evaluate [((1/1 : ℝ), 0, 1), ((4503599627370493/4503599627370496 : ℝ), 1, 1), ((81129638414606660252431888843765/162259276829213363391578010288128 : ℝ), 2, 1), ((7794675399098151816808612301838702062016212459787/46768052394588893382517914646921056628989841375232 : ℝ), 3, 1), ((17552048611426207088424394140232180064561904473279887297385985465/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 4, 1), ((31751788392809785079018055083136901756093505136799218390038059871260509547856983/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 5, 1), ((93128228923746765669986070129155286900389707209226234770762328734021176450397921525127293282469/68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432 : ℝ), 6, 1), ((121882619630298222179234067729195156910495351911346723726214261312803688123388340109241976318134659676400864659/615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544 : ℝ), 7, 1), ((7023272222596618866185555341982630428072542269407004198271393762943107565685919638788198354230155588244415169033/315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528 : ℝ), 8, 1), ((7468242252438155938669927388502808829150369857192058910395248072249845012785107072077593001199806059510404155578329550308672479/2839213766779714416208296124562517712318911565184836172974571090549372219192960637992933791850638927971728600024477257552869537611776 : ℝ), 9, 1), ((25156749521778662287274253829643333912109859757964471275549965896453236844374647892693084575031957602839007256175331130647983027/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 10, 1), ((-417615464538586376572057244340715821055554396763337550125518747874626127034896978127371417283746333004867274658051558434833375/181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 : ℝ), 11, 1)] h y := by
  simp only [exact246, polynomial245, polynomial2, evaluate] <;> ring
theorem bound246 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact246 h y| ≤ (146303004415/274877906944 : ℝ) := by
  rw [polynomial246]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error246 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded246 rnd h y - exact246 h y| ≤ (150499564734895132765887/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded246 exact246
  apply rounded_step rnd hrnd (propagation := (1123565590612733079811575/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (146303004415/274877906944 : ℝ))
  · convert FindOrb.add_error (error245 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound246 h y hh hy
  · norm_num
  · norm_num
def exact247 (h y : ℝ) : ℝ := (7407769262434301/9007199254740992 : ℝ)
def rounded247 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (7407769262434301/9007199254740992 : ℝ)
theorem polynomial247 (h y : ℝ) : exact247 h y = evaluate [((7407769262434301/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact247, evaluate] <;> ring
theorem bound247 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact247 h y| ≤ (452134354397/549755813888 : ℝ) := by
  rw [polynomial247]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error247 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded247 rnd h y - exact247 h y| ≤ (0/1 : ℝ) := by
  simp [rounded247, exact247]
def exact248 (h y : ℝ) : ℝ := exact247 h y * exact4 h y
def rounded248 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded247 rnd h y * rounded4 rnd h y)
theorem polynomial248 (h y : ℝ) : exact248 h y = evaluate [((7407769262434301/9007199254740992 : ℝ), 0, 1)] h y := by
  simp only [exact248, polynomial247, polynomial4, evaluate] <;> ring
theorem bound248 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact248 h y| ≤ (452134354397/1099511627776 : ℝ) := by
  rw [polynomial248]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error248 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded248 rnd h y - exact248 h y| ≤ (124281744994124083232769/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded248 exact248
  apply rounded_step rnd hrnd (propagation := (34162305935332777577646565129895389/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (452134354397/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound247 h y hh hy) (bound4 h y hh hy)
      (error247 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound248 h y hh hy
  · norm_num
  · norm_num
def exact249 (h y : ℝ) : ℝ := exact2 h y + exact248 h y
def rounded249 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded248 rnd h y)
theorem polynomial249 (h y : ℝ) : exact249 h y = evaluate [((7407769262434301/9007199254740992 : ℝ), 0, 1)] h y := by
  simp only [exact249, polynomial2, polynomial248, evaluate] <;> ring
theorem bound249 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact249 h y| ≤ (452134354397/1099511627776 : ℝ) := by
  rw [polynomial249]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error249 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded249 rnd h y - exact249 h y| ≤ (93211308745593062424577/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded249 exact249
  apply rounded_step rnd hrnd (propagation := (124281744994124083232769/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (452134354397/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error248 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound249 h y hh hy
  · norm_num
  · norm_num
def exact250 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded250 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial250 (h y : ℝ) : exact250 h y = evaluate [] h y := by
  simp only [exact250, evaluate] <;> ring
theorem bound250 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact250 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial250]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error250 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded250 rnd h y - exact250 h y| ≤ (0/1 : ℝ) := by
  simp [rounded250, exact250]
def exact251 (h y : ℝ) : ℝ := exact250 h y * exact11 h y
def rounded251 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded250 rnd h y * rounded11 rnd h y)
theorem polynomial251 (h y : ℝ) : exact251 h y = evaluate [] h y := by
  simp only [exact251, polynomial250, polynomial11, evaluate] <;> ring
theorem bound251 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact251 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial251]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error251 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded251 rnd h y - exact251 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded251 exact251
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound250 h y hh hy) (bound11 h y hh hy)
      (error250 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound251 h y hh hy
  · norm_num
  · norm_num
def exact252 (h y : ℝ) : ℝ := exact249 h y + exact251 h y
def rounded252 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded249 rnd h y + rounded251 rnd h y)
theorem polynomial252 (h y : ℝ) : exact252 h y = evaluate [((7407769262434301/9007199254740992 : ℝ), 0, 1)] h y := by
  simp only [exact252, polynomial249, polynomial251, evaluate] <;> ring
theorem bound252 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact252 h y| ≤ (452134354397/1099511627776 : ℝ) := by
  rw [polynomial252]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error252 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded252 rnd h y - exact252 h y| ≤ (62140872497062041616385/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded252 exact252
  apply rounded_step rnd hrnd (propagation := (186422617491186124849155/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (452134354397/1099511627776 : ℝ))
  · convert FindOrb.add_error (error249 rnd hrnd h y hh hy) (error251 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound252 h y hh hy
  · norm_num
  · norm_num
def exact253 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded253 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial253 (h y : ℝ) : exact253 h y = evaluate [] h y := by
  simp only [exact253, evaluate] <;> ring
theorem bound253 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact253 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial253]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error253 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded253 rnd h y - exact253 h y| ≤ (0/1 : ℝ) := by
  simp [rounded253, exact253]
def exact254 (h y : ℝ) : ℝ := exact253 h y * exact21 h y
def rounded254 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded253 rnd h y * rounded21 rnd h y)
theorem polynomial254 (h y : ℝ) : exact254 h y = evaluate [] h y := by
  simp only [exact254, polynomial253, polynomial21, evaluate] <;> ring
theorem bound254 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact254 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial254]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error254 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded254 rnd h y - exact254 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded254 exact254
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound253 h y hh hy) (bound21 h y hh hy)
      (error253 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound254 h y hh hy
  · norm_num
  · norm_num
def exact255 (h y : ℝ) : ℝ := exact252 h y + exact254 h y
def rounded255 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded252 rnd h y + rounded254 rnd h y)
theorem polynomial255 (h y : ℝ) : exact255 h y = evaluate [((7407769262434301/9007199254740992 : ℝ), 0, 1)] h y := by
  simp only [exact255, polynomial252, polynomial254, evaluate] <;> ring
theorem bound255 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact255 h y| ≤ (452134354397/1099511627776 : ℝ) := by
  rw [polynomial255]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error255 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded255 rnd h y - exact255 h y| ≤ (155352181242655104040963/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded255 exact255
  apply rounded_step rnd hrnd (propagation := (248563489988248166465541/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (452134354397/1099511627776 : ℝ))
  · convert FindOrb.add_error (error252 rnd hrnd h y hh hy) (error254 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound255 h y hh hy
  · norm_num
  · norm_num
def exact256 (h y : ℝ) : ℝ := (-6563249567138757/562949953421312 : ℝ)
def rounded256 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-6563249567138757/562949953421312 : ℝ)
theorem polynomial256 (h y : ℝ) : exact256 h y = evaluate [((-6563249567138757/562949953421312 : ℝ), 0, 0)] h y := by
  simp only [exact256, evaluate] <;> ring
theorem bound256 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact256 h y| ≤ (6409423405409/549755813888 : ℝ) := by
  rw [polynomial256]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error256 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded256 rnd h y - exact256 h y| ≤ (0/1 : ℝ) := by
  simp [rounded256, exact256]
def exact257 (h y : ℝ) : ℝ := exact256 h y * exact34 h y
def rounded257 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded256 rnd h y * rounded34 rnd h y)
theorem polynomial257 (h y : ℝ) : exact257 h y = evaluate [((-6563249567138757/562949953421312 : ℝ), 0, 1), ((-6563249567138757/4503599627370496 : ℝ), 1, 1), ((-472931972878490796541874911476795/5192296858534827628530496329220096 : ℝ), 2, 1), ((-39410997739874231404343850838377/10384593717069655257060992658440192 : ℝ), 3, 1)] h y := by
  simp only [exact257, polynomial256, polynomial34, evaluate] <;> ring
theorem bound257 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact257 h y| ≤ (6459693135219/1099511627776 : ℝ) := by
  rw [polynomial257]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error257 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded257 rnd h y - exact257 h y| ≤ (1119737351519361368482527/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded257 exact257
  apply rounded_step rnd hrnd (propagation := (1974247862479178801335650332379334373/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (6459693135219/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound256 h y hh hy) (bound34 h y hh hy)
      (error256 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound257 h y hh hy
  · norm_num
  · norm_num
def exact258 (h y : ℝ) : ℝ := exact255 h y + exact257 h y
def rounded258 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded255 rnd h y + rounded257 rnd h y)
theorem polynomial258 (h y : ℝ) : exact258 h y = evaluate [((-97604223811785811/9007199254740992 : ℝ), 0, 1), ((-6563249567138757/4503599627370496 : ℝ), 1, 1), ((-472931972878490796541874911476795/5192296858534827628530496329220096 : ℝ), 2, 1), ((-39410997739874231404343850838377/10384593717069655257060992658440192 : ℝ), 3, 1)] h y := by
  simp only [exact258, polynomial255, polynomial257, evaluate] <;> ring
theorem bound258 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact258 h y| ≤ (3003779390411/549755813888 : ℝ) := by
  rw [polynomial258]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error258 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded258 rnd h y - exact258 h y| ≤ (5615326360320455585926019/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded258 exact258
  apply rounded_step rnd hrnd (propagation := (2394826884281377841006017/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (3003779390411/549755813888 : ℝ))
  · convert FindOrb.add_error (error255 rnd hrnd h y hh hy) (error257 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound258 h y hh hy
  · norm_num
  · norm_num
def exact259 (h y : ℝ) : ℝ := (-6824053364833893/9007199254740992 : ℝ)
def rounded259 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-6824053364833893/9007199254740992 : ℝ)
theorem polynomial259 (h y : ℝ) : exact259 h y = evaluate [((-6824053364833893/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact259, evaluate] <;> ring
theorem bound259 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact259 h y| ≤ (416507163381/549755813888 : ℝ) := by
  rw [polynomial259]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error259 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded259 rnd h y - exact259 h y| ≤ (0/1 : ℝ) := by
  simp [rounded259, exact259]
def exact260 (h y : ℝ) : ℝ := exact259 h y * exact50 h y
def rounded260 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded259 rnd h y * rounded50 rnd h y)
theorem polynomial260 (h y : ℝ) : exact260 h y = evaluate [((-6824053364833893/9007199254740992 : ℝ), 0, 1), ((-34120266824169465/144115188075855872 : ℝ), 1, 1), ((-6146560838204460152044415925032925/166153499473114484112975882535043072 : ℝ), 2, 1), ((-20488536127348200336213385629262425/5316911983139663491615228241121378304 : ℝ), 3, 1), ((-3073280419102229820120206781245475/10633823966279326983230456482242756608 : ℝ), 4, 1)] h y := by
  simp only [exact260, polynomial259, polynomial50, evaluate] <;> ring
theorem bound260 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact260 h y| ≤ (424722030981/1099511627776 : ℝ) := by
  rw [polynomial260]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error260 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded260 rnd h y - exact260 h y| ≤ (85768964557203709969587/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded260 exact260
  apply rounded_step rnd hrnd (propagation := (78258429163825122533599737442856943/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (424722030981/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound259 h y hh hy) (bound50 h y hh hy)
      (error259 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound260 h y hh hy
  · norm_num
  · norm_num
def exact261 (h y : ℝ) : ℝ := exact258 h y + exact260 h y
def rounded261 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded258 rnd h y + rounded260 rnd h y)
theorem polynomial261 (h y : ℝ) : exact261 h y = evaluate [((-13053534647077463/1125899906842624 : ℝ), 0, 1), ((-244144252972609689/144115188075855872 : ℝ), 1, 1), ((-21280383970316165641384413092290365/166153499473114484112975882535043072 : ℝ), 2, 1), ((-40666966970163806815237437258511449/5316911983139663491615228241121378304 : ℝ), 3, 1), ((-3073280419102229820120206781245475/10633823966279326983230456482242756608 : ℝ), 4, 1)] h y := by
  simp only [exact261, polynomial258, polynomial260, evaluate] <;> ring
theorem bound261 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact261 h y| ≤ (6432280811803/1099511627776 : ℝ) := by
  rw [polynomial261]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error261 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded261 rnd h y - exact261 h y| ≤ (427653010110093833202149/98079714615416886934934209737619787751599303819750539264 : ℝ) := by
  unfold rounded261 exact261
  apply rounded_step rnd hrnd (propagation := (5958402218549270425804367/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (6432280811803/1099511627776 : ℝ))
  · convert FindOrb.add_error (error258 rnd hrnd h y hh hy) (error260 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound261 h y hh hy
  · norm_num
  · norm_num
def exact262 (h y : ℝ) : ℝ := (6430902371175735/9007199254740992 : ℝ)
def rounded262 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (6430902371175735/9007199254740992 : ℝ)
theorem polynomial262 (h y : ℝ) : exact262 h y = evaluate [((6430902371175735/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact262, evaluate] <;> ring
theorem bound262 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact262 h y| ≤ (785022262107/1099511627776 : ℝ) := by
  rw [polynomial262]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error262 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded262 rnd h y - exact262 h y| ≤ (0/1 : ℝ) := by
  simp [rounded262, exact262]
def exact263 (h y : ℝ) : ℝ := exact262 h y * exact69 h y
def rounded263 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded262 rnd h y * rounded69 rnd h y)
theorem polynomial263 (h y : ℝ) : exact263 h y = evaluate [((6430902371175735/9007199254740992 : ℝ), 0, 1), ((347546514269796945197441270198985/1298074214633706907132624082305024 : ℝ), 1, 1), ((260659885702347707290355359855305/5192296858534827628530496329220096 : ℝ), 2, 1), ((37565048451824935353172431983244070474403530898925/5986310706507378352962293074805895248510699696029696 : ℝ), 3, 1), ((112695145355474804891374845209581367664285701995305/191561942608236107294793378393788647952342390272950272 : ℝ), 4, 1), ((15652103521593721772590005448981122686255432761875/383123885216472214589586756787577295904684780545900544 : ℝ), 5, 1)] h y := by
  simp only [exact263, polynomial262, polynomial69, evaluate] <;> ring
theorem bound263 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact263 h y| ≤ (100454816071/274877906944 : ℝ) := by
  rw [polynomial263]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error263 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded263 rnd h y - exact263 h y| ≤ (17815532665164752584723/98079714615416886934934209737619787751599303819750539264 : ℝ) := by
  unfold rounded263 exact263
  apply rounded_step rnd hrnd (propagation := (3948327417179898406990553373839931/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ)) (magnitude := (100454816071/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound262 h y hh hy) (bound69 h y hh hy)
      (error262 rnd hrnd h y hh hy) (error69 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound263 h y hh hy
  · norm_num
  · norm_num
def exact264 (h y : ℝ) : ℝ := exact261 h y + exact263 h y
def rounded264 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded261 rnd h y + rounded263 rnd h y)
theorem polynomial264 (h y : ℝ) : exact264 h y = evaluate [((-97997374805443969/9007199254740992 : ℝ), 0, 1), ((-1851509419154389266295210734472503/1298074214633706907132624082305024 : ℝ), 1, 1), ((-12939267627841039008093041576920605/166153499473114484112975882535043072 : ℝ), 2, 1), ((-8221885871454561920972865547677497987136214303251/5986310706507378352962293074805895248510699696029696 : ℝ), 3, 1), ((57331847154379428911705484831120375916037107972905/191561942608236107294793378393788647952342390272950272 : ℝ), 4, 1), ((15652103521593721772590005448981122686255432761875/383123885216472214589586756787577295904684780545900544 : ℝ), 5, 1)] h y := by
  simp only [exact264, polynomial261, polynomial263, evaluate] <;> ring
theorem bound264 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact264 h y| ≤ (753807694073/137438953472 : ℝ) := by
  rw [polynomial264]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error264 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded264 rnd h y - exact264 h y| ≤ (7956317009144414629961601/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded264 exact264
  apply rounded_step rnd hrnd (propagation := (55683567846907323223359/12259964326927110866866776217202473468949912977468817408 : ℝ)) (magnitude := (753807694073/137438953472 : ℝ))
  · convert FindOrb.add_error (error261 rnd hrnd h y hh hy) (error263 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound264 h y hh hy
  · norm_num
  · norm_num
def exact265 (h y : ℝ) : ℝ := (3399028483198001/281474976710656 : ℝ)
def rounded265 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (3399028483198001/281474976710656 : ℝ)
theorem polynomial265 (h y : ℝ) : exact265 h y = evaluate [((3399028483198001/281474976710656 : ℝ), 0, 0)] h y := by
  simp only [exact265, evaluate] <;> ring
theorem bound265 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact265 h y| ≤ (13277455012493/1099511627776 : ℝ) := by
  rw [polynomial265]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error265 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded265 rnd h y - exact265 h y| ≤ (0/1 : ℝ) := by
  simp [rounded265, exact265]
def exact266 (h y : ℝ) : ℝ := exact265 h y * exact91 h y
def rounded266 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded265 rnd h y * rounded91 rnd h y)
theorem polynomial266 (h y : ℝ) : exact266 h y = evaluate [((3399028483198001/281474976710656 : ℝ), 0, 1), ((289012461187449892853536610032961/162259276829213363391578010288128 : ℝ), 1, 1), ((3071767533521780820355649118503531597401131598751/23384026197294446691258957323460528314494920687616 : ℝ), 2, 1), ((2416457126370466852297993074604741899231455122387/374144419156711147060143317175368453031918731001856 : ℝ), 3, 1), ((25683302776753984484911219495936820493763078317074514137365959195/107839786668602559178668060348078522694548577690162289924414440996864 : ℝ), 4, 1), ((35663465820713353912594705803631655715713280479794190896251824703/3450873173395281893717377931138512726225554486085193277581262111899648 : ℝ), 5, 1), ((61266223910505916868882702356523500040455741161507708705202417125/6901746346790563787434755862277025452451108972170386555162524223799296 : ℝ), 6, 1)] h y := by
  simp only [exact266, polynomial265, polynomial91, evaluate] <;> ring
theorem bound266 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact266 h y| ≤ (6700211241605/1099511627776 : ℝ) := by
  rw [polynomial266]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error266 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded266 rnd h y - exact266 h y| ≤ (4688479467207317168318963/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded266 exact266
  apply rounded_step rnd hrnd (propagation := (4142530394927410911936327558749730653/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (6700211241605/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound265 h y hh hy) (bound91 h y hh hy)
      (error265 rnd hrnd h y hh hy) (error91 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound266 h y hh hy
  · norm_num
  · norm_num
def exact267 (h y : ℝ) : ℝ := exact264 h y + exact266 h y
def rounded267 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded264 rnd h y + rounded266 rnd h y)
theorem polynomial267 (h y : ℝ) : exact267 h y = evaluate [((10771536656892063/9007199254740992 : ℝ), 0, 1), ((460590270345209876533082145791185/1298074214633706907132624082305024 : ℝ), 1, 1), ((1250727506422030039381122068020482596816846865311/23384026197294446691258957323460528314494920687616 : ℝ), 2, 1), ((30441428150472907715795023645998372400567067654941/5986310706507378352962293074805895248510699696029696 : ℝ), 3, 1), ((57958263461869662923228569285106710278207488014614735195111510555/107839786668602559178668060348078522694548577690162289924414440996864 : ℝ), 4, 1), ((176645080995541181046423735615265372353087110567535636170589104703/3450873173395281893717377931138512726225554486085193277581262111899648 : ℝ), 5, 1), ((61266223910505916868882702356523500040455741161507708705202417125/6901746346790563787434755862277025452451108972170386555162524223799296 : ℝ), 6, 1)] h y := by
  simp only [exact267, polynomial264, polynomial266, evaluate] <;> ring
theorem bound267 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact267 h y| ≤ (334874847043/549755813888 : ℝ) := by
  rw [polynomial267]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error267 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded267 rnd h y - exact267 h y| ≤ (12736846173395103785847157/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded267 exact267
  apply rounded_step rnd hrnd (propagation := (3161199119087932949570141/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (334874847043/549755813888 : ℝ))
  · convert FindOrb.add_error (error264 rnd hrnd h y hh hy) (error266 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound267 h y hh hy
  · norm_num
  · norm_num
def exact268 (h y : ℝ) : ℝ := (-4791062396311683/2251799813685248 : ℝ)
def rounded268 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-4791062396311683/2251799813685248 : ℝ)
theorem polynomial268 (h y : ℝ) : exact268 h y = evaluate [((-4791062396311683/2251799813685248 : ℝ), 0, 0)] h y := by
  simp only [exact268, evaluate] <;> ring
theorem bound268 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact268 h y| ≤ (584846483925/274877906944 : ℝ) := by
  rw [polynomial268]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error268 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded268 rnd h y - exact268 h y| ≤ (0/1 : ℝ) := by
  simp [rounded268, exact268]
def exact269 (h y : ℝ) : ℝ := exact268 h y * exact116 h y
def rounded269 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded268 rnd h y * rounded116 rnd h y)
theorem polynomial269 (h y : ℝ) : exact269 h y = evaluate [((-4791062396311683/2251799813685248 : ℝ), 0, 1), ((-321066159122342818534918909783755/324518553658426726783156020576256 : ℝ), 1, 1), ((-1344736694163733324959169991432926938005602663125/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((-30038532146746221231992282818686129390542130860657767966552787493/842498333348457493583344221469363458551160763204392890034487820288 : ℝ), 3, 1), ((-27935834896473986152972500717157335845678613286646239400942794689/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 4, 1), ((-1426963764301092053343309872664277410254247117733342051418487417882658376959963833/3885337784451458141838923813647037813284813678104279042503624819477808570410416996352 : ℝ), 5, 1), ((-2942384536477002049640335353901438647010963659051663009549552570745664451975684357/124330809102446660538845562036705210025114037699336929360115994223289874253133343883264 : ℝ), 6, 1), ((67171505547877295287036919827651496225402401187107723060367586161128823917949625/248661618204893321077691124073410420050228075398673858720231988446579748506266687766528 : ℝ), 7, 1)] h y := by
  simp only [exact269, polynomial268, polynomial116, evaluate] <;> ring
theorem bound269 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact269 h y| ≤ (1204185968351/1099511627776 : ℝ) := by
  rw [polynomial269]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error269 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded269 rnd h y - exact269 h y| ≤ (889511448664436201691267/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded269 exact269
  apply rounded_step rnd hrnd (propagation := (199014185562944009131050137528139825/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (1204185968351/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound268 h y hh hy) (bound116 h y hh hy)
      (error268 rnd hrnd h y hh hy) (error116 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound269 h y hh hy
  · norm_num
  · norm_num
def exact270 (h y : ℝ) : ℝ := exact267 h y + exact269 h y
def rounded270 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded267 rnd h y + rounded269 rnd h y)
theorem polynomial270 (h y : ℝ) : exact270 h y = evaluate [((-8392712928354669/9007199254740992 : ℝ), 0, 1), ((-823674366144161397606593493343835/1298074214633706907132624082305024 : ℝ), 1, 1), ((-4128219270232903260455557897711225155205563787189/23384026197294446691258957323460528314494920687616 : ℝ), 2, 1), ((-25754282006899486406164235915009703044712482315026625822649911845/842498333348457493583344221469363458551160763204392890034487820288 : ℝ), 3, 1), ((-389015094881714115524331442189410663252650324571725095219973204469/107839786668602559178668060348078522694548577690162289924414440996864 : ℝ), 4, 1), ((-1228079084064004466455225514960819521557773972021894398547511797040320045280703161/3885337784451458141838923813647037813284813678104279042503624819477808570410416996352 : ℝ), 5, 1), ((-1838710363781994771696575568238059361046109693147809593710559695673300103535108357/124330809102446660538845562036705210025114037699336929360115994223289874253133343883264 : ℝ), 6, 1), ((67171505547877295287036919827651496225402401187107723060367586161128823917949625/248661618204893321077691124073410420050228075398673858720231988446579748506266687766528 : ℝ), 7, 1)] h y := by
  simp only [exact270, polynomial267, polynomial269, evaluate] <;> ring
theorem bound270 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact270 h y| ≤ (534436274265/1099511627776 : ℝ) := by
  rw [polynomial270]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error270 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded270 rnd h y - exact270 h y| ≤ (13699809984291996353536505/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded270 exact270
  apply rounded_step rnd hrnd (propagation := (1703294702757442498442303/196159429230833773869868419475239575503198607639501078528 : ℝ)) (magnitude := (534436274265/1099511627776 : ℝ))
  · convert FindOrb.add_error (error267 rnd hrnd h y hh hy) (error269 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound270 h y hh hy
  · norm_num
  · norm_num
def exact271 (h y : ℝ) : ℝ := (8962911788471029/4503599627370496 : ℝ)
def rounded271 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (8962911788471029/4503599627370496 : ℝ)
theorem polynomial271 (h y : ℝ) : exact271 h y = evaluate [((8962911788471029/4503599627370496 : ℝ), 0, 0)] h y := by
  simp only [exact271, evaluate] <;> ring
theorem bound271 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact271 h y| ≤ (1094105442929/549755813888 : ℝ) := by
  rw [polynomial271]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error271 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded271 rnd h y - exact271 h y| ≤ (0/1 : ℝ) := by
  simp [rounded271, exact271]
def exact272 (h y : ℝ) : ℝ := exact271 h y * exact144 h y
def rounded272 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded271 rnd h y * rounded144 rnd h y)
theorem polynomial272 (h y : ℝ) : exact272 h y = evaluate [((8962911788471029/4503599627370496 : ℝ), 0, 1), ((182408006348217258753528582148781/162259276829213363391578010288128 : ℝ), 1, 1), ((7424524878785449138830652277431518690668734072439/23384026197294446691258957323460528314494920687616 : ℝ), 2, 1), ((100733096058062786701978299301745151844054080872288564750660426711/1684996666696914987166688442938726917102321526408785780068975640576 : ℝ), 3, 1), ((128128863552396274998489455167260740126081133339144333933497633494249474243079709/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 4, 1), ((7478660177432796129055331094494752002914212389967550496168622772904257456493009251/7770675568902916283677847627294075626569627356208558085007249638955617140820833992704 : ℝ), 5, 1), ((6306030512531824607307009743846806236535867370934713416755808676214816590309295697573945322333841/69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368 : ℝ), 6, 1), ((13576057123983837176991812792396663328419427425749045218985128393479410143968584688055837736081917/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776 : ℝ), 7, 1), ((-239542381254618469561886553254495106261062166172302499271564484855048116504133272282715417044625/4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986543214231552 : ℝ), 8, 1)] h y := by
  simp only [exact272, polynomial271, polynomial144, evaluate] <;> ring
theorem bound272 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact272 h y| ≤ (141677721355/137438953472 : ℝ) := by
  rw [polynomial272]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error272 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded272 rnd h y - exact272 h y| ≤ (911437126235840187692521/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded272 exact272
  apply rounded_step rnd hrnd (propagation := (103857232859102726843140660579904115/215679573337205118357336120696157045389097155380324579848828881993728 : ℝ)) (magnitude := (141677721355/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound271 h y hh hy) (bound144 h y hh hy)
      (error271 rnd hrnd h y hh hy) (error144 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound272 h y hh hy
  · norm_num
  · norm_num
def exact273 (h y : ℝ) : ℝ := exact270 h y + exact272 h y
def rounded273 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded270 rnd h y + rounded272 rnd h y)
theorem polynomial273 (h y : ℝ) : exact273 h y = evaluate [((9533110648587389/9007199254740992 : ℝ), 0, 1), ((635589684641576672421635163846413/1298074214633706907132624082305024 : ℝ), 1, 1), ((1648152804276272939187547189860146767731585142625/11692013098647223345629478661730264157247460343808 : ℝ), 2, 1), ((49224532044263813889649827471725745754629116242235313105360603021/1684996666696914987166688442938726917102321526408785780068975640576 : ℝ), 3, 1), ((73379856166434217611323531873076220489210305164297333676255862635649401573518877/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 4, 1), ((5022502009304787196144880064573112959798664445923761699073599178823617365931602929/7770675568902916283677847627294075626569627356208558085007249638955617140820833992704 : ℝ), 5, 1), ((5270928598885467007548457016193214780618236622823251016884010044386454667165801900930304529229457/69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368 : ℝ), 6, 1), ((14181084258694507960623682145328075755089786887062423992612547238441658308964945077058026814609917/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776 : ℝ), 7, 1), ((-239542381254618469561886553254495106261062166172302499271564484855048116504133272282715417044625/4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986543214231552 : ℝ), 8, 1)] h y := by
  simp only [exact273, polynomial270, polynomial272, evaluate] <;> ring
theorem bound273 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact273 h y| ≤ (292473387/536870912 : ℝ) := by
  rw [polynomial273]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error273 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded273 rnd h y - exact273 h y| ≤ (14693571050322148220540899/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded273 exact273
  apply rounded_step rnd hrnd (propagation := (7305623555263918270614513/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (292473387/536870912 : ℝ))
  · convert FindOrb.add_error (error270 rnd hrnd h y hh hy) (error272 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound273 h y hh hy
  · norm_num
  · norm_num
def exact274 (h y : ℝ) : ℝ := (-8441059727549505/36028797018963968 : ℝ)
def rounded274 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-8441059727549505/36028797018963968 : ℝ)
theorem polynomial274 (h y : ℝ) : exact274 h y = evaluate [((-8441059727549505/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact274, evaluate] <;> ring
theorem bound274 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact274 h y| ≤ (128800349847/549755813888 : ℝ) := by
  rw [polynomial274]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error274 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded274 rnd h y - exact274 h y| ≤ (0/1 : ℝ) := by
  simp [rounded274, exact274]
def exact275 (h y : ℝ) : ℝ := exact274 h y * exact175 h y
def rounded275 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded274 rnd h y * rounded175 rnd h y)
theorem polynomial275 (h y : ℝ) : exact275 h y = evaluate [((-8441059727549505/36028797018963968 : ℝ), 0, 1), ((-1581430383253928238144410589213495/10384593717069655257060992658440192 : ℝ), 1, 1), ((-74070144561241631429917779000191457123730114359825/1496577676626844588240573268701473812127674924007424 : ℝ), 2, 1), ((-72276159679812096281587425688182513323324034273582512401633279635/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 3, 1), ((-26447109471393993602113083470693538677941845422822189291225564710141595220237465/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 4, 1), ((-510555629095940003613659894679826646720737087201365373042662882023255790148355914616707508927205/2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824 : ℝ), 5, 1), ((-224114122704592313789612058026167204853462025366925987481614656847354429198290670649756735124195/8749002899132047697490008908470485461412677723572849745703082425639811996797503692894052708092215296 : ℝ), 6, 1), ((-25582710788431312430152987036383713979324519382203938685716206693672789438842488375406762188081579854088729060985/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 7, 1), ((-25799874277345922157045230326477699740839252270046422960912289677028040519006973295564096201164968041594599381445/322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672 : ℝ), 8, 1), ((502894965611227748859850242412630843535551251122625463657963485891384042087312999510525826862972956009803605625/645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344 : ℝ), 9, 1)] h y := by
  simp only [exact275, polynomial274, polynomial175, evaluate] <;> ring
theorem bound275 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact275 h y| ≤ (16767575441/137438953472 : ℝ) := by
  rw [polynomial275]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error275 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded275 rnd h y - exact275 h y| ≤ (68923676331190607892947/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded275 exact275
  apply rounded_step rnd hrnd (propagation := (32823503056866511423716981105552093/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (16767575441/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound274 h y hh hy) (bound175 h y hh hy)
      (error274 rnd hrnd h y hh hy) (error175 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound275 h y hh hy
  · norm_num
  · norm_num
def exact276 (h y : ℝ) : ℝ := exact273 h y + exact275 h y
def rounded276 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded273 rnd h y + rounded275 rnd h y)
theorem polynomial276 (h y : ℝ) : exact276 h y = evaluate [((29691382866800051/36028797018963968 : ℝ), 0, 1), ((3503287093878685141228670721557809/10384593717069655257060992658440192 : ℝ), 1, 1), ((136893414386121304786088261301907329145912783896175/1496577676626844588240573268701473812127674924007424 : ℝ), 2, 1), ((124621968497243159277011884198720469695192430695358740019809132449/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 3, 1), ((11733186673760056002302612100595670452817114935368786096257574481376951588320353/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 4, 1), ((903153007002347937030830363682304661053151116105758429516194463086589314186501860268586406184219/2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824 : ℝ), 5, 1), ((3478015617248728497231560551983877141790540419887843117031092789607619233579476535732250648235897/69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368 : ℝ), 6, 1), ((38283214994734880121769638982061599524041058948837630815638591644459921284327169666545529922821331200317945747847/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 7, 1), ((-43060721940669778567149778472910668013882809951433495629212433236544190949981742191292767426716640417726445525445/322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672 : ℝ), 8, 1), ((502894965611227748859850242412630843535551251122625463657963485891384042087312999510525826862972956009803605625/645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344 : ℝ), 9, 1)] h y := by
  simp only [exact276, polynomial273, polynomial275, evaluate] <;> ring
theorem bound276 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact276 h y| ≤ (464844893049/1099511627776 : ℝ) := by
  rw [polynomial276]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error276 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded276 rnd h y - exact276 h y| ≤ (7447653099305993881771461/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded276 exact276
  apply rounded_step rnd hrnd (propagation := (14831418402984529436326793/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (464844893049/1099511627776 : ℝ))
  · convert FindOrb.add_error (error273 rnd hrnd h y hh hy) (error275 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound276 h y hh hy
  · norm_num
  · norm_num
def exact277 (h y : ℝ) : ℝ := (792176769020489/4503599627370496 : ℝ)
def rounded277 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (792176769020489/4503599627370496 : ℝ)
theorem polynomial277 (h y : ℝ) : exact277 h y = evaluate [((792176769020489/4503599627370496 : ℝ), 0, 0)] h y := by
  simp only [exact277, evaluate] <;> ring
theorem bound277 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact277 h y| ≤ (48350632875/274877906944 : ℝ) := by
  rw [polynomial277]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error277 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded277 rnd h y - exact277 h y| ≤ (0/1 : ℝ) := by
  simp [rounded277, exact277]
def exact278 (h y : ℝ) : ℝ := exact277 h y * exact209 h y
def rounded278 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded277 rnd h y * rounded209 rnd h y)
theorem polynomial278 (h y : ℝ) : exact278 h y = evaluate [((792176769020489/4503599627370496 : ℝ), 0, 1), ((3298847196594027703382022502219/20282409603651670423947251286016 : ℝ), 1, 1), ((109898631235370775515616498761257023524679694593/1461501637330902918203684832716283019655932542976 : ℝ), 2, 1), ((4881587790174258405614656507728143091504126416039412390756257287/210624583337114373395836055367340864637790190801098222508621955072 : ℝ), 3, 1), ((5082076635640224767274815488272555980337715502397490984883880497060057397340997/948568795032094272909893509191171341133987714380927500611236528192824358010355712 : ℝ), 4, 1), ((4084244687017303348270883508130880567458639960693483388617643182630177898857840453039724528451/4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152 : ℝ), 5, 1), ((46127992472282605476037993842880975187365723379004157861613090765558973252594660123094637213237815226301979899/307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272 : ℝ), 6, 1), ((379156411628959172331750947470746166457645453561699387327513983112355954297708923385849695126608292890266832985/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408 : ℝ), 7, 1), ((3238254932234807209235506864053806215753949837605200014179130233174875916220082614475409891386462494728445652668071269922443495/1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888 : ℝ), 8, 1), ((16867280760381704325278144875692959410689217654224138609893026249829186338988561636776985083846803092916143517712281445163979291/45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416 : ℝ), 9, 1), ((-272818310354067841151473392356834799969881488990766738906943698960005864584782014355850865078004643770524084268849982769926375/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 10, 1)] h y := by
  simp only [exact278, polynomial277, polynomial209, evaluate] <;> ring
theorem bound278 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact278 h y| ≤ (102454367979/1099511627776 : ℝ) := by
  rw [polynomial278]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error278 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded278 rnd h y - exact278 h y| ≤ (14577825808991468941569/49039857307708443467467104868809893875799651909875269632 : ℝ) := by
  unfold rounded278 exact278
  apply rounded_step rnd hrnd (propagation := (62178647645246285768914638587032125/215679573337205118357336120696157045389097155380324579848828881993728 : ℝ)) (magnitude := (102454367979/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound277 h y hh hy) (bound209 h y hh hy)
      (error277 rnd hrnd h y hh hy) (error209 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound278 h y hh hy
  · norm_num
  · norm_num
def exact279 (h y : ℝ) : ℝ := exact276 h y + exact278 h y
def rounded279 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded276 rnd h y + rounded278 rnd h y)
theorem polynomial279 (h y : ℝ) : exact279 h y = evaluate [((36028797018963963/36028797018963968 : ℝ), 0, 1), ((5192296858534827325360266242693937/10384593717069655257060992658440192 : ℝ), 1, 1), ((249429612771140978914079556033434521235184791159407/1496577676626844588240573268701473812127674924007424 : ℝ), 2, 1), ((280832777782819428256680892446021048623324476008619936524009365633/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 3, 1), ((32061493216320955071401874053685894374167976944958750035793096469617181177684341/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 4, 1), ((2994286286755207251345522719845315511591974775980821924488427772593240398401716172224925364751131/2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824 : ℝ), 5, 1), ((61424466923288600886667399651330982476476585188242577497455388771581253731974563342570494566605344399523880187/307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272 : ℝ), 6, 1), ((232411297748761976355626124087083636750355531172427717127325750997986169884754138440100573827644777160134564236167/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 7, 1), ((3048871874338025025523281544655614967319630536261978037043589657955634206458597041858495139837962478341243745769012775615402215/1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888 : ℝ), 8, 1), ((16902668847565035945433713136053068206352472561299166531232504916304553179209295845340813777807750020440303876383309777953739291/45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416 : ℝ), 9, 1), ((-272818310354067841151473392356834799969881488990766738906943698960005864584782014355850865078004643770524084268849982769926375/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 10, 1)] h y := by
  simp only [exact279, polynomial276, polynomial278, evaluate] <;> ring
theorem bound279 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact279 h y| ≤ (567299261027/1099511627776 : ℝ) := by
  rw [polynomial279]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error279 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded279 rnd h y - exact279 h y| ≤ (15439765641240704605608875/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded279 exact279
  apply rounded_step rnd hrnd (propagation := (7680898312249857384836565/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (567299261027/1099511627776 : ℝ))
  · convert FindOrb.add_error (error276 rnd hrnd h y hh hy) (error278 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound279 h y hh hy
  · norm_num
  · norm_num
def exact280 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded280 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial280 (h y : ℝ) : exact280 h y = evaluate [] h y := by
  simp only [exact280, evaluate] <;> ring
theorem bound280 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact280 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial280]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error280 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded280 rnd h y - exact280 h y| ≤ (0/1 : ℝ) := by
  simp [rounded280, exact280]
def exact281 (h y : ℝ) : ℝ := exact280 h y * exact246 h y
def rounded281 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded280 rnd h y * rounded246 rnd h y)
theorem polynomial281 (h y : ℝ) : exact281 h y = evaluate [] h y := by
  simp only [exact281, polynomial280, polynomial246, evaluate] <;> ring
theorem bound281 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact281 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial281]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error281 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded281 rnd h y - exact281 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded281 exact281
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound280 h y hh hy) (bound246 h y hh hy)
      (error280 rnd hrnd h y hh hy) (error246 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound281 h y hh hy
  · norm_num
  · norm_num
def exact282 (h y : ℝ) : ℝ := exact279 h y + exact281 h y
def rounded282 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded279 rnd h y + rounded281 rnd h y)
theorem polynomial282 (h y : ℝ) : exact282 h y = evaluate [((36028797018963963/36028797018963968 : ℝ), 0, 1), ((5192296858534827325360266242693937/10384593717069655257060992658440192 : ℝ), 1, 1), ((249429612771140978914079556033434521235184791159407/1496577676626844588240573268701473812127674924007424 : ℝ), 2, 1), ((280832777782819428256680892446021048623324476008619936524009365633/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 3, 1), ((32061493216320955071401874053685894374167976944958750035793096469617181177684341/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 4, 1), ((2994286286755207251345522719845315511591974775980821924488427772593240398401716172224925364751131/2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824 : ℝ), 5, 1), ((61424466923288600886667399651330982476476585188242577497455388771581253731974563342570494566605344399523880187/307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272 : ℝ), 6, 1), ((232411297748761976355626124087083636750355531172427717127325750997986169884754138440100573827644777160134564236167/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 7, 1), ((3048871874338025025523281544655614967319630536261978037043589657955634206458597041858495139837962478341243745769012775615402215/1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888 : ℝ), 8, 1), ((16902668847565035945433713136053068206352472561299166531232504916304553179209295845340813777807750020440303876383309777953739291/45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416 : ℝ), 9, 1), ((-272818310354067841151473392356834799969881488990766738906943698960005864584782014355850865078004643770524084268849982769926375/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 10, 1)] h y := by
  simp only [exact282, polynomial279, polynomial281, evaluate] <;> ring
theorem bound282 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact282 h y| ≤ (567299261027/1099511627776 : ℝ) := by
  rw [polynomial282]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error282 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded282 rnd h y - exact282 h y| ≤ (15517734657981694441544621/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded282 exact282
  apply rounded_step rnd hrnd (propagation := (3859941410310176151402219/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (567299261027/1099511627776 : ℝ))
  · convert FindOrb.add_error (error279 rnd hrnd h y hh hy) (error281 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound282 h y hh hy
  · norm_num
  · norm_num
def exact283 (h y : ℝ) : ℝ := exact282 h y * exact0 h y
def rounded283 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded282 rnd h y * rounded0 rnd h y)
theorem polynomial283 (h y : ℝ) : exact283 h y = evaluate [((36028797018963963/36028797018963968 : ℝ), 1, 1), ((5192296858534827325360266242693937/10384593717069655257060992658440192 : ℝ), 2, 1), ((249429612771140978914079556033434521235184791159407/1496577676626844588240573268701473812127674924007424 : ℝ), 3, 1), ((280832777782819428256680892446021048623324476008619936524009365633/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 4, 1), ((32061493216320955071401874053685894374167976944958750035793096469617181177684341/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 5, 1), ((2994286286755207251345522719845315511591974775980821924488427772593240398401716172224925364751131/2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824 : ℝ), 6, 1), ((61424466923288600886667399651330982476476585188242577497455388771581253731974563342570494566605344399523880187/307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272 : ℝ), 7, 1), ((232411297748761976355626124087083636750355531172427717127325750997986169884754138440100573827644777160134564236167/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 8, 1), ((3048871874338025025523281544655614967319630536261978037043589657955634206458597041858495139837962478341243745769012775615402215/1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888 : ℝ), 9, 1), ((16902668847565035945433713136053068206352472561299166531232504916304553179209295845340813777807750020440303876383309777953739291/45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416 : ℝ), 10, 1), ((-272818310354067841151473392356834799969881488990766738906943698960005864584782014355850865078004643770524084268849982769926375/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 11, 1)] h y := by
  simp only [exact283, polynomial282, polynomial0, evaluate] <;> ring
theorem bound283 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact283 h y| ≤ (35456203815/1099511627776 : ℝ) := by
  rw [polynomial283]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error283 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded283 rnd h y - exact283 h y| ≤ (974731479670279436492219/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded283 exact283
  apply rounded_step rnd hrnd (propagation := (15517734657981694441544621/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (35456203815/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound282 h y hh hy) (bound0 h y hh hy)
      (error282 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound283 h y hh hy
  · norm_num
  · norm_num
def exact284 (h y : ℝ) : ℝ := exact283 h y + exact3 h y
def rounded284 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded283 rnd h y + rounded3 rnd h y)
theorem polynomial284 (h y : ℝ) : exact284 h y = evaluate [((1/1 : ℝ), 0, 1), ((36028797018963963/36028797018963968 : ℝ), 1, 1), ((5192296858534827325360266242693937/10384593717069655257060992658440192 : ℝ), 2, 1), ((249429612771140978914079556033434521235184791159407/1496577676626844588240573268701473812127674924007424 : ℝ), 3, 1), ((280832777782819428256680892446021048623324476008619936524009365633/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 4, 1), ((32061493216320955071401874053685894374167976944958750035793096469617181177684341/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 5, 1), ((2994286286755207251345522719845315511591974775980821924488427772593240398401716172224925364751131/2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824 : ℝ), 6, 1), ((61424466923288600886667399651330982476476585188242577497455388771581253731974563342570494566605344399523880187/307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272 : ℝ), 7, 1), ((232411297748761976355626124087083636750355531172427717127325750997986169884754138440100573827644777160134564236167/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 8, 1), ((3048871874338025025523281544655614967319630536261978037043589657955634206458597041858495139837962478341243745769012775615402215/1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888 : ℝ), 9, 1), ((16902668847565035945433713136053068206352472561299166531232504916304553179209295845340813777807750020440303876383309777953739291/45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416 : ℝ), 10, 1), ((-272818310354067841151473392356834799969881488990766738906943698960005864584782014355850865078004643770524084268849982769926375/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 11, 1)] h y := by
  simp only [exact284, polynomial283, polynomial3, evaluate] <;> ring
theorem bound284 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact284 h y| ≤ (585212017703/1099511627776 : ℝ) := by
  rw [polynomial284]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error284 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded284 rnd h y - exact284 h y| ≤ (1130720270668531617226173/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded284 exact284
  apply rounded_step rnd hrnd (propagation := (262572335849048439977839/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (585212017703/1099511627776 : ℝ))
  · convert FindOrb.add_error (error283 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound284 h y hh hy
  · norm_num
  · norm_num
def exact285 (h y : ℝ) : ℝ := exact284 h y + exact2 h y
def rounded285 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded284 rnd h y + rounded2 rnd h y)
theorem polynomial285 (h y : ℝ) : exact285 h y = evaluate [((1/1 : ℝ), 0, 1), ((36028797018963963/36028797018963968 : ℝ), 1, 1), ((5192296858534827325360266242693937/10384593717069655257060992658440192 : ℝ), 2, 1), ((249429612771140978914079556033434521235184791159407/1496577676626844588240573268701473812127674924007424 : ℝ), 3, 1), ((280832777782819428256680892446021048623324476008619936524009365633/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 4, 1), ((32061493216320955071401874053685894374167976944958750035793096469617181177684341/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 5, 1), ((2994286286755207251345522719845315511591974775980821924488427772593240398401716172224925364751131/2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824 : ℝ), 6, 1), ((61424466923288600886667399651330982476476585188242577497455388771581253731974563342570494566605344399523880187/307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272 : ℝ), 7, 1), ((232411297748761976355626124087083636750355531172427717127325750997986169884754138440100573827644777160134564236167/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 8, 1), ((3048871874338025025523281544655614967319630536261978037043589657955634206458597041858495139837962478341243745769012775615402215/1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888 : ℝ), 9, 1), ((16902668847565035945433713136053068206352472561299166531232504916304553179209295845340813777807750020440303876383309777953739291/45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416 : ℝ), 10, 1), ((-272818310354067841151473392356834799969881488990766738906943698960005864584782014355850865078004643770524084268849982769926375/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 11, 1)] h y := by
  simp only [exact285, polynomial284, polynomial2, evaluate] <;> ring
theorem bound285 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact285 h y| ≤ (585212017703/1099511627776 : ℝ) := by
  rw [polynomial285]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error285 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded285 rnd h y - exact285 h y| ≤ (605575598970434737270495/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded285 exact285
  apply rounded_step rnd hrnd (propagation := (1130720270668531617226173/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (585212017703/1099511627776 : ℝ))
  · convert FindOrb.add_error (error284 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound285 h y hh hy
  · norm_num
  · norm_num
def exact286 (h y : ℝ) : ℝ := exact285 h y + exact2 h y
def rounded286 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded285 rnd h y + rounded2 rnd h y)
theorem polynomial286 (h y : ℝ) : exact286 h y = evaluate [((1/1 : ℝ), 0, 1), ((36028797018963963/36028797018963968 : ℝ), 1, 1), ((5192296858534827325360266242693937/10384593717069655257060992658440192 : ℝ), 2, 1), ((249429612771140978914079556033434521235184791159407/1496577676626844588240573268701473812127674924007424 : ℝ), 3, 1), ((280832777782819428256680892446021048623324476008619936524009365633/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 4, 1), ((32061493216320955071401874053685894374167976944958750035793096469617181177684341/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 5, 1), ((2994286286755207251345522719845315511591974775980821924488427772593240398401716172224925364751131/2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824 : ℝ), 6, 1), ((61424466923288600886667399651330982476476585188242577497455388771581253731974563342570494566605344399523880187/307828173409331868845930000782371982852185463050511302093346042220669701339821957901673955116288403443801781174272 : ℝ), 7, 1), ((232411297748761976355626124087083636750355531172427717127325750997986169884754138440100573827644777160134564236167/10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896 : ℝ), 8, 1), ((3048871874338025025523281544655614967319630536261978037043589657955634206458597041858495139837962478341243745769012775615402215/1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888 : ℝ), 9, 1), ((16902668847565035945433713136053068206352472561299166531232504916304553179209295845340813777807750020440303876383309777953739291/45427420268475430659332737993000283397102585042957378767593137448789955507087370207886940669610222847547657600391636120845912601788416 : ℝ), 10, 1), ((-272818310354067841151473392356834799969881488990766738906943698960005864584782014355850865078004643770524084268849982769926375/90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832 : ℝ), 11, 1)] h y := by
  simp only [exact286, polynomial285, polynomial2, evaluate] <;> ring
theorem bound286 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact286 h y| ≤ (585212017703/1099511627776 : ℝ) := by
  rw [polynomial286]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error286 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded286 rnd h y - exact286 h y| ≤ (1291582125213207331855807/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded286 exact286
  apply rounded_step rnd hrnd (propagation := (605575598970434737270495/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (585212017703/1099511627776 : ℝ))
  · convert FindOrb.add_error (error285 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound286 h y hh hy
  · norm_num
  · norm_num
def exact287 (h y : ℝ) : ℝ := (3008223768778379/72057594037927936 : ℝ)
def rounded287 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (3008223768778379/72057594037927936 : ℝ)
theorem polynomial287 (h y : ℝ) : exact287 h y = evaluate [((3008223768778379/72057594037927936 : ℝ), 0, 0)] h y := by
  simp only [exact287, evaluate] <;> ring
theorem bound287 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact287 h y| ≤ (45901851941/1099511627776 : ℝ) := by
  rw [polynomial287]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error287 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded287 rnd h y - exact287 h y| ≤ (0/1 : ℝ) := by
  simp [rounded287, exact287]
def exact288 (h y : ℝ) : ℝ := exact287 h y * exact4 h y
def rounded288 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded287 rnd h y * rounded4 rnd h y)
theorem polynomial288 (h y : ℝ) : exact288 h y = evaluate [((3008223768778379/72057594037927936 : ℝ), 0, 1)] h y := by
  simp only [exact288, polynomial287, polynomial4, evaluate] <;> ring
theorem bound288 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact288 h y| ≤ (22950925971/1099511627776 : ℝ) := by
  rw [polynomial288]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error288 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded288 rnd h y - exact288 h y| ≤ (6308702493266451365889/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded288 exact288
  apply rounded_step rnd hrnd (propagation := (3468245873725173878436415459994917/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (22950925971/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound287 h y hh hy) (bound4 h y hh hy)
      (error287 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound288 h y hh hy
  · norm_num
  · norm_num
def exact289 (h y : ℝ) : ℝ := exact2 h y + exact288 h y
def rounded289 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded288 rnd h y)
theorem polynomial289 (h y : ℝ) : exact289 h y = evaluate [((3008223768778379/72057594037927936 : ℝ), 0, 1)] h y := by
  simp only [exact289, polynomial2, polynomial288, evaluate] <;> ring
theorem bound289 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact289 h y| ≤ (22950925971/1099511627776 : ℝ) := by
  rw [polynomial289]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error289 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded289 rnd h y - exact289 h y| ≤ (4731526869967018393601/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded289 exact289
  apply rounded_step rnd hrnd (propagation := (6308702493266451365889/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (22950925971/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error288 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound289 h y hh hy
  · norm_num
  · norm_num
def exact290 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded290 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial290 (h y : ℝ) : exact290 h y = evaluate [] h y := by
  simp only [exact290, evaluate] <;> ring
theorem bound290 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact290 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial290]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error290 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded290 rnd h y - exact290 h y| ≤ (0/1 : ℝ) := by
  simp [rounded290, exact290]
def exact291 (h y : ℝ) : ℝ := exact290 h y * exact11 h y
def rounded291 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded290 rnd h y * rounded11 rnd h y)
theorem polynomial291 (h y : ℝ) : exact291 h y = evaluate [] h y := by
  simp only [exact291, polynomial290, polynomial11, evaluate] <;> ring
theorem bound291 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact291 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial291]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error291 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded291 rnd h y - exact291 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded291 exact291
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound290 h y hh hy) (bound11 h y hh hy)
      (error290 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound291 h y hh hy
  · norm_num
  · norm_num
def exact292 (h y : ℝ) : ℝ := exact289 h y + exact291 h y
def rounded292 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded289 rnd h y + rounded291 rnd h y)
theorem polynomial292 (h y : ℝ) : exact292 h y = evaluate [((3008223768778379/72057594037927936 : ℝ), 0, 1)] h y := by
  simp only [exact292, polynomial289, polynomial291, evaluate] <;> ring
theorem bound292 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact292 h y| ≤ (22950925971/1099511627776 : ℝ) := by
  rw [polynomial292]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error292 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded292 rnd h y - exact292 h y| ≤ (3154351246650405552129/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded292 exact292
  apply rounded_step rnd hrnd (propagation := (9463053739934036787203/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (22950925971/1099511627776 : ℝ))
  · convert FindOrb.add_error (error289 rnd hrnd h y hh hy) (error291 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound292 h y hh hy
  · norm_num
  · norm_num
def exact293 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded293 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial293 (h y : ℝ) : exact293 h y = evaluate [] h y := by
  simp only [exact293, evaluate] <;> ring
theorem bound293 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact293 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial293]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error293 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded293 rnd h y - exact293 h y| ≤ (0/1 : ℝ) := by
  simp [rounded293, exact293]
def exact294 (h y : ℝ) : ℝ := exact293 h y * exact21 h y
def rounded294 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded293 rnd h y * rounded21 rnd h y)
theorem polynomial294 (h y : ℝ) : exact294 h y = evaluate [] h y := by
  simp only [exact294, polynomial293, polynomial21, evaluate] <;> ring
theorem bound294 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact294 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial294]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error294 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded294 rnd h y - exact294 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded294 exact294
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound293 h y hh hy) (bound21 h y hh hy)
      (error293 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound294 h y hh hy
  · norm_num
  · norm_num
def exact295 (h y : ℝ) : ℝ := exact292 h y + exact294 h y
def rounded295 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded292 rnd h y + rounded294 rnd h y)
theorem polynomial295 (h y : ℝ) : exact295 h y = evaluate [((3008223768778379/72057594037927936 : ℝ), 0, 1)] h y := by
  simp only [exact295, polynomial292, polynomial294, evaluate] <;> ring
theorem bound295 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact295 h y| ≤ (22950925971/1099511627776 : ℝ) := by
  rw [polynomial295]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error295 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded295 rnd h y - exact295 h y| ≤ (7885878116634603814915/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded295 exact295
  apply rounded_step rnd hrnd (propagation := (12617404986601622208517/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (22950925971/1099511627776 : ℝ))
  · convert FindOrb.add_error (error292 rnd hrnd h y hh hy) (error294 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound295 h y hh hy
  · norm_num
  · norm_num
def exact296 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded296 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial296 (h y : ℝ) : exact296 h y = evaluate [] h y := by
  simp only [exact296, evaluate] <;> ring
theorem bound296 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact296 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial296]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error296 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded296 rnd h y - exact296 h y| ≤ (0/1 : ℝ) := by
  simp [rounded296, exact296]
def exact297 (h y : ℝ) : ℝ := exact296 h y * exact34 h y
def rounded297 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded296 rnd h y * rounded34 rnd h y)
theorem polynomial297 (h y : ℝ) : exact297 h y = evaluate [] h y := by
  simp only [exact297, polynomial296, polynomial34, evaluate] <;> ring
theorem bound297 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact297 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial297]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error297 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded297 rnd h y - exact297 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded297 exact297
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound296 h y hh hy) (bound34 h y hh hy)
      (error296 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound297 h y hh hy
  · norm_num
  · norm_num
def exact298 (h y : ℝ) : ℝ := exact295 h y + exact297 h y
def rounded298 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded295 rnd h y + rounded297 rnd h y)
theorem polynomial298 (h y : ℝ) : exact298 h y = evaluate [((3008223768778379/72057594037927936 : ℝ), 0, 1)] h y := by
  simp only [exact298, polynomial295, polynomial297, evaluate] <;> ring
theorem bound298 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact298 h y| ≤ (22950925971/1099511627776 : ℝ) := by
  rw [polynomial298]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error298 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded298 rnd h y - exact298 h y| ≤ (2365763434992099131393/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded298 exact298
  apply rounded_step rnd hrnd (propagation := (15771756233269207629831/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (22950925971/1099511627776 : ℝ))
  · convert FindOrb.add_error (error295 rnd hrnd h y hh hy) (error297 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound298 h y hh hy
  · norm_num
  · norm_num
def exact299 (h y : ℝ) : ℝ := (0/1 : ℝ)
def rounded299 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (0/1 : ℝ)
theorem polynomial299 (h y : ℝ) : exact299 h y = evaluate [] h y := by
  simp only [exact299, evaluate] <;> ring
theorem bound299 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact299 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial299]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error299 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded299 rnd h y - exact299 h y| ≤ (0/1 : ℝ) := by
  simp [rounded299, exact299]
def exact300 (h y : ℝ) : ℝ := exact299 h y * exact50 h y
def rounded300 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded299 rnd h y * rounded50 rnd h y)
theorem polynomial300 (h y : ℝ) : exact300 h y = evaluate [] h y := by
  simp only [exact300, polynomial299, polynomial50, evaluate] <;> ring
theorem bound300 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact300 h y| ≤ (0/1 : ℝ) := by
  rw [polynomial300]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error300 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded300 rnd h y - exact300 h y| ≤ (1/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded300 exact300
  apply rounded_step rnd hrnd (propagation := (0/1 : ℝ)) (magnitude := (0/1 : ℝ))
  · convert FindOrb.mul_error (bound299 h y hh hy) (bound50 h y hh hy)
      (error299 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound300 h y hh hy
  · norm_num
  · norm_num
def exact301 (h y : ℝ) : ℝ := exact298 h y + exact300 h y
def rounded301 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded298 rnd h y + rounded300 rnd h y)
theorem polynomial301 (h y : ℝ) : exact301 h y = evaluate [((3008223768778379/72057594037927936 : ℝ), 0, 1)] h y := by
  simp only [exact301, polynomial298, polynomial300, evaluate] <;> ring
theorem bound301 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact301 h y| ≤ (22950925971/1099511627776 : ℝ) := by
  rw [polynomial301]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error301 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded301 rnd h y - exact301 h y| ≤ (11040229363302189236229/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded301 exact301
  apply rounded_step rnd hrnd (propagation := (18926107479936793051145/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (22950925971/1099511627776 : ℝ))
  · convert FindOrb.add_error (error298 rnd hrnd h y hh hy) (error300 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound301 h y hh hy
  · norm_num
  · norm_num
def exact302 (h y : ℝ) : ℝ := (-7991522767052917/144115188075855872 : ℝ)
def rounded302 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-7991522767052917/144115188075855872 : ℝ)
theorem polynomial302 (h y : ℝ) : exact302 h y = evaluate [((-7991522767052917/144115188075855872 : ℝ), 0, 0)] h y := by
  simp only [exact302, evaluate] <;> ring
theorem bound302 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact302 h y| ≤ (1905327503/34359738368 : ℝ) := by
  rw [polynomial302]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error302 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded302 rnd h y - exact302 h y| ≤ (0/1 : ℝ) := by
  simp [rounded302, exact302]
def exact303 (h y : ℝ) : ℝ := exact302 h y * exact69 h y
def rounded303 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded302 rnd h y * rounded69 rnd h y)
theorem polynomial303 (h y : ℝ) : exact303 h y = evaluate [((-7991522767052917/144115188075855872 : ℝ), 0, 1), ((-431887427469868217323245191389067/20769187434139310514121985316880384 : ℝ), 1, 1), ((-323915570602401160994553201778571/83076749736557242056487941267521536 : ℝ), 2, 1), ((-46681153378063215314392767171999564531755553054135/95780971304118053647396689196894323976171195136475136 : ℝ), 3, 1), ((-140043460134189644491556670297830518481261355686571/3064991081731777716716694054300618367237478244367204352 : ℝ), 4, 1), ((-19450480574193004776415224541253343610122901463625/6129982163463555433433388108601236734474956488734408704 : ℝ), 5, 1)] h y := by
  simp only [exact303, polynomial302, polynomial69, evaluate] <;> ring
theorem bound303 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact303 h y| ≤ (15604088341/549755813888 : ℝ) := by
  rw [polynomial303]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error303 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded303 rnd h y - exact303 h y| ≤ (2767365034578695200081/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded303 exact303
  apply rounded_step rnd hrnd (propagation := (9582985326569548550767146409199/842498333348457493583344221469363458551160763204392890034487820288 : ℝ)) (magnitude := (15604088341/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound302 h y hh hy) (bound69 h y hh hy)
      (error302 rnd hrnd h y hh hy) (error69 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound303 h y hh hy
  · norm_num
  · norm_num
def exact304 (h y : ℝ) : ℝ := exact301 h y + exact303 h y
def rounded304 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded301 rnd h y + rounded303 rnd h y)
theorem polynomial304 (h y : ℝ) : exact304 h y = evaluate [((-1975075229496159/144115188075855872 : ℝ), 0, 1), ((-431887427469868217323245191389067/20769187434139310514121985316880384 : ℝ), 1, 1), ((-323915570602401160994553201778571/83076749736557242056487941267521536 : ℝ), 2, 1), ((-46681153378063215314392767171999564531755553054135/95780971304118053647396689196894323976171195136475136 : ℝ), 3, 1), ((-140043460134189644491556670297830518481261355686571/3064991081731777716716694054300618367237478244367204352 : ℝ), 4, 1), ((-19450480574193004776415224541253343610122901463625/6129982163463555433433388108601236734474956488734408704 : ℝ), 5, 1)] h y := by
  simp only [exact304, polynomial301, polynomial303, evaluate] <;> ring
theorem bound304 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact304 h y| ≤ (1032156339/137438953472 : ℝ) := by
  rw [polynomial304]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error304 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded304 rnd h y - exact304 h y| ≤ (45354246899647146945171/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded304 exact304
  apply rounded_step rnd hrnd (propagation := (22109689501616970036553/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (1032156339/137438953472 : ℝ))
  · convert FindOrb.add_error (error301 rnd hrnd h y hh hy) (error303 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound304 h y hh hy
  · norm_num
  · norm_num
def exact305 (h y : ℝ) : ℝ := (538884534668111/2251799813685248 : ℝ)
def rounded305 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (538884534668111/2251799813685248 : ℝ)
theorem polynomial305 (h y : ℝ) : exact305 h y = evaluate [((538884534668111/2251799813685248 : ℝ), 0, 0)] h y := by
  simp only [exact305, evaluate] <;> ring
theorem bound305 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact305 h y| ≤ (131563607097/549755813888 : ℝ) := by
  rw [polynomial305]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error305 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded305 rnd h y - exact305 h y| ≤ (0/1 : ℝ) := by
  simp [rounded305, exact305]
def exact306 (h y : ℝ) : ℝ := exact305 h y * exact91 h y
def rounded306 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded305 rnd h y * rounded91 rnd h y)
theorem polynomial306 (h y : ℝ) : exact306 h y = evaluate [((538884534668111/2251799813685248 : ℝ), 0, 1), ((45820253178270283610796575748671/1298074214633706907132624082305024 : ℝ), 1, 1), ((487000337329644366214819765900154994954274651361/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((383106932032653452927876624082439477509938614957/2993155353253689176481146537402947624255349848014848 : ℝ), 3, 1), ((4071850157774933732494085494155179973507974764528089804871020645/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ), 4, 1), ((5654112720280984215271119635435783674850957745693577357134612033/27606985387162255149739023449108101809804435888681546220650096895197184 : ℝ), 5, 1), ((9713193262747382178964037932842736010320290918901722573159550875/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 6, 1)] h y := by
  simp only [exact306, polynomial305, polynomial91, evaluate] <;> ring
theorem bound306 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact306 h y| ≤ (132782066809/1099511627776 : ℝ) := by
  rw [polynomial306]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error306 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded306 rnd h y - exact306 h y| ≤ (92914383054002520810181/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded306 exact306
  apply rounded_step rnd hrnd (propagation := (41047492968554877527154517298209737/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (132782066809/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound305 h y hh hy) (bound91 h y hh hy)
      (error305 rnd hrnd h y hh hy) (error91 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound306 h y hh hy
  · norm_num
  · norm_num
def exact307 (h y : ℝ) : ℝ := exact304 h y + exact306 h y
def rounded307 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded304 rnd h y + rounded306 rnd h y)
theorem polynomial307 (h y : ℝ) : exact307 h y = evaluate [((32513534989262945/144115188075855872 : ℝ), 0, 1), ((301236623382456320449500020589669/20769187434139310514121985316880384 : ℝ), 1, 1), ((-242392684202593362387852218652578042665310569247/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((-34421731553018304820700715201361501251437517375511/95780971304118053647396689196894323976171195136475136 : ℝ), 3, 1), ((-35346879521975778435338036476358275155247666718896215929220779931/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ), 4, 1), ((-81943064345831703172617915503316755751837573504221821211407595967/27606985387162255149739023449108101809804435888681546220650096895197184 : ℝ), 5, 1), ((9713193262747382178964037932842736010320290918901722573159550875/55213970774324510299478046898216203619608871777363092441300193790394368 : ℝ), 6, 1)] h y := by
  simp only [exact307, polynomial304, polynomial306, evaluate] <;> ring
theorem bound307 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact307 h y| ≤ (124530478321/1099511627776 : ℝ) := by
  rw [polynomial307]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error307 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded307 rnd h y - exact307 h y| ≤ (155383968569455491435865/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded307 exact307
  apply rounded_step rnd hrnd (propagation := (17283578744206208469419/196159429230833773869868419475239575503198607639501078528 : ℝ)) (magnitude := (124530478321/1099511627776 : ℝ))
  · convert FindOrb.add_error (error304 rnd hrnd h y hh hy) (error306 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound307 h y hh hy
  · norm_num
  · norm_num
def exact308 (h y : ℝ) : ℝ := (1584165194288257/2251799813685248 : ℝ)
def rounded308 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1584165194288257/2251799813685248 : ℝ)
theorem polynomial308 (h y : ℝ) : exact308 h y = evaluate [((1584165194288257/2251799813685248 : ℝ), 0, 0)] h y := by
  simp only [exact308, evaluate] <;> ring
theorem bound308 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact308 h y| ≤ (386759080637/549755813888 : ℝ) := by
  rw [polynomial308]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error308 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded308 rnd h y - exact308 h y| ≤ (0/1 : ℝ) := by
  simp [rounded308, exact308]
def exact309 (h y : ℝ) : ℝ := exact308 h y * exact116 h y
def rounded309 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded308 rnd h y * rounded116 rnd h y)
theorem polynomial309 (h y : ℝ) : exact309 h y = evaluate [((1584165194288257/2251799813685248 : ℝ), 0, 1), ((106160553186905773078153714837145/324518553658426726783156020576256 : ℝ), 1, 1), ((444637303829814940898585541691196682040251074375/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((9932243243381163808358764679372899072546810721633564667040248247/842498333348457493583344221469363458551160763204392890034487820288 : ℝ), 3, 1), ((9236986216344482476420872680711336189405804858199999114458500331/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 4, 1), ((471825691657989004793909959771419882893628698355132899626040100459221080024873107/3885337784451458141838923813647037813284813678104279042503624819477808570410416996352 : ℝ), 5, 1), ((972899700594009268765509117582543206130122783527971377201533177910197302535362903/124330809102446660538845562036705210025114037699336929360115994223289874253133343883264 : ℝ), 6, 1), ((-22210264099003649608517609205972400466921221089718980442790025560568511190857875/248661618204893321077691124073410420050228075398673858720231988446579748506266687766528 : ℝ), 7, 1)] h y := by
  simp only [exact309, polynomial308, polynomial116, evaluate] <;> ring
theorem bound309 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact309 h y| ≤ (199082097113/549755813888 : ℝ) := by
  rw [polynomial309]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error309 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded309 rnd h y - exact309 h y| ≤ (294117037169122012694093/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded309 exact309
  apply rounded_step rnd hrnd (propagation := (131608115219371228891725245641752313/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (199082097113/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound308 h y hh hy) (bound116 h y hh hy)
      (error308 rnd hrnd h y hh hy) (error116 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound309 h y hh hy
  · norm_num
  · norm_num
def exact310 (h y : ℝ) : ℝ := exact307 h y + exact309 h y
def rounded310 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded307 rnd h y + rounded309 rnd h y)
theorem polynomial310 (h y : ℝ) : exact310 h y = evaluate [((133900107423711393/144115188075855872 : ℝ), 0, 1), ((7095512027344425797451337770166949/20769187434139310514121985316880384 : ℝ), 1, 1), ((13986001038351484746366885115465715782622723810753/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((9629466490655342554124102349837088097727713715317529602641899959/842498333348457493583344221469363458551160763204392890034487820288 : ℝ), 3, 1), ((1146987356170117978546533666654692757088695355130703670721467262437/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ), 4, 1), ((460293230593817622450758396534766848340842990688344421795853347171299530869110931/3885337784451458141838923813647037813284813678104279042503624819477808570410416996352 : ℝ), 5, 1), ((994771867373352630079250988876814134701974999854859832968747300979498724828354903/124330809102446660538845562036705210025114037699336929360115994223289874253133343883264 : ℝ), 6, 1), ((-22210264099003649608517609205972400466921221089718980442790025560568511190857875/248661618204893321077691124073410420050228075398673858720231988446579748506266687766528 : ℝ), 7, 1)] h y := by
  simp only [exact310, polynomial307, polynomial309, evaluate] <;> ring
theorem bound310 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact310 h y| ≤ (522689010323/1099511627776 : ℝ) := by
  rw [polynomial310]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error310 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded310 rnd h y - exact310 h y| ≤ (521338836308686028821415/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded310 exact310
  apply rounded_step rnd hrnd (propagation := (224750502869288752064979/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (522689010323/1099511627776 : ℝ))
  · convert FindOrb.add_error (error307 rnd hrnd h y hh hy) (error309 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound310 h y hh hy
  · norm_num
  · norm_num
def exact311 (h y : ℝ) : ℝ := (-1710826556832979/2251799813685248 : ℝ)
def rounded311 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-1710826556832979/2251799813685248 : ℝ)
theorem polynomial311 (h y : ℝ) : exact311 h y = evaluate [((-1710826556832979/2251799813685248 : ℝ), 0, 0)] h y := by
  simp only [exact311, evaluate] <;> ring
theorem bound311 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact311 h y| ≤ (104420566213/137438953472 : ℝ) := by
  rw [polynomial311]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error311 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded311 rnd h y - exact311 h y| ≤ (0/1 : ℝ) := by
  simp [rounded311, exact311]
def exact312 (h y : ℝ) : ℝ := exact311 h y * exact144 h y
def rounded312 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded311 rnd h y * rounded144 rnd h y)
theorem polynomial312 (h y : ℝ) : exact312 h y = evaluate [((-1710826556832979/2251799813685248 : ℝ), 0, 1), ((-34817754408885468349488224122331/81129638414606681695789005144064 : ℝ), 1, 1), ((-1417181674244741217491809273434276280813551049889/11692013098647223345629478661730264157247460343808 : ℝ), 2, 1), ((-19227775521546218206551294976301221048203434493656207091007581761/842498333348457493583344221469363458551160763204392890034487820288 : ℝ), 3, 1), ((-24457036690267683330760682024742356034693990893933602255071992765226988686535659/7588550360256754183279148073529370729071901715047420004889892225542594864082845696 : ℝ), 4, 1), ((-1427514935217709571687574684716524530500447690241074111351331469891210516937521301/3885337784451458141838923813647037813284813678104279042503624819477808570410416996352 : ℝ), 5, 1), ((-1203685222353273558404623958723723607399858005801280882336693143963940159640346810940862551530391/34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184 : ℝ), 6, 1), ((-2591376509436253547828998130856740344778429121483732748223522492781698210476335547082732602944267/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888 : ℝ), 7, 1), ((45723474358473131295091442705549198722147567369074149703626862497963812827337938119367837588375/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776 : ℝ), 8, 1)] h y := by
  simp only [exact312, polynomial311, polynomial144, evaluate] <;> ring
theorem bound312 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact312 h y| ≤ (216345771487/549755813888 : ℝ) := by
  rw [polynomial312]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error312 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded312 rnd h y - exact312 h y| ≤ (347947380772799652572205/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded312 exact312
  apply rounded_step rnd hrnd (propagation := (9912052929222701386440167459612655/53919893334301279589334030174039261347274288845081144962207220498432 : ℝ)) (magnitude := (216345771487/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound311 h y hh hy) (bound144 h y hh hy)
      (error311 rnd hrnd h y hh hy) (error144 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound312 h y hh hy
  · norm_num
  · norm_num
def exact313 (h y : ℝ) : ℝ := exact310 h y + exact312 h y
def rounded313 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded310 rnd h y + rounded312 rnd h y)
theorem polynomial313 (h y : ℝ) : exact313 h y = evaluate [((24407207786400737/144115188075855872 : ℝ), 0, 1), ((-1817833101330254100017647605149787/20769187434139310514121985316880384 : ℝ), 1, 1), ((-8688905749564374733502063259482704710394092987471/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((-4799154515445437826213596313232066475237860389169338744182840901/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 3, 1), ((-14368029210098906564667386997655259987848000552110159165221922508993385081334763/7588550360256754183279148073529370729071901715047420004889892225542594864082845696 : ℝ), 4, 1), ((-483610852311945974618408144090878841079802349776364844777739061359955493034205185/1942668892225729070919461906823518906642406839052139521251812409738904285205208498176 : ℝ), 5, 1), ((-923681834151943347633452621850045891126917599853767461871595719212432897652368364707835841584023/34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184 : ℝ), 6, 1), ((-2691402646556326689285181187865046753833926109105168126809348470113726956693516789864913307200267/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888 : ℝ), 7, 1), ((45723474358473131295091442705549198722147567369074149703626862497963812827337938119367837588375/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776 : ℝ), 8, 1)] h y := by
  simp only [exact313, polynomial310, polynomial312, evaluate] <;> ring
theorem bound313 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact313 h y| ≤ (96214750261/1099511627776 : ℝ) := by
  rw [polynomial313]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error313 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded313 rnd h y - exact313 h y| ≤ (882509871665927360249813/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded313 exact313
  apply rounded_step rnd hrnd (propagation := (217321554270371420348405/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (96214750261/1099511627776 : ℝ))
  · convert FindOrb.add_error (error310 rnd hrnd h y hh hy) (error312 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound313 h y hh hy
  · norm_num
  · norm_num
def exact314 (h y : ℝ) : ℝ := (1487455709958167/2251799813685248 : ℝ)
def rounded314 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1487455709958167/2251799813685248 : ℝ)
theorem polynomial314 (h y : ℝ) : exact314 h y = evaluate [((1487455709958167/2251799813685248 : ℝ), 0, 0)] h y := by
  simp only [exact314, evaluate] <;> ring
theorem bound314 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact314 h y| ≤ (726296733379/1099511627776 : ℝ) := by
  rw [polynomial314]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error314 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded314 rnd h y - exact314 h y| ≤ (0/1 : ℝ) := by
  simp [rounded314, exact314]
def exact315 (h y : ℝ) : ℝ := exact314 h y * exact175 h y
def rounded315 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded314 rnd h y * rounded175 rnd h y)
theorem polynomial315 (h y : ℝ) : exact315 h y = evaluate [((1487455709958167/2251799813685248 : ℝ), 0, 1), ((278674447213664995598879829146033/649037107316853453566312041152512 : ℝ), 1, 1), ((13052396620943063230800537857170889555985348403655/93536104789177786765035829293842113257979682750464 : ℝ), 2, 1), ((12736266520980405760209125329066208699765446508498184000414686709/421249166674228746791672110734681729275580381602196445017243910144 : ℝ), 3, 1), ((4660422419085767723682169409062701049248709655354921333231740611546707522258431/948568795032094272909893509191171341133987714380927500611236528192824358010355712 : ℝ), 4, 1), ((89968429351524942810036684919846832941843432796558693728198195797808375337086416702950098811347/136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864 : ℝ), 5, 1), ((39492651664483324265486159263212014126372954213910096422947269945087774948013626901831036421413/546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456 : ℝ), 6, 1), ((4508100933614366791588847979741621521848534914033840621503111433710292262150293297468503655173842690206441152799/630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056 : ℝ), 7, 1), ((4546368767512782823302503672767804746303870315077889876016554834789062489660358750342947125130750347675995928563/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 8, 1), ((-88618492494045640738501457660576456866059756583474092278487268659264860588013516591138310059118389532533465375/40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584 : ℝ), 9, 1)] h y := by
  simp only [exact315, polynomial314, polynomial175, evaluate] <;> ring
theorem bound315 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact315 h y| ≤ (189102518493/549755813888 : ℝ) := by
  rw [polynomial315]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error315 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded315 rnd h y - exact315 h y| ≤ (194328047366510559531657/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded315 exact315
  apply rounded_step rnd hrnd (propagation := (185089583037441080924343103917019201/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (189102518493/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound314 h y hh hy) (bound175 h y hh hy)
      (error314 rnd hrnd h y hh hy) (error175 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound315 h y hh hy
  · norm_num
  · norm_num
def exact316 (h y : ℝ) : ℝ := exact313 h y + exact315 h y
def rounded316 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded313 rnd h y + rounded315 rnd h y)
theorem polynomial316 (h y : ℝ) : exact316 h y = evaluate [((119604373223723425/144115188075855872 : ℝ), 0, 1), ((7099749209507025759146506927523269/20769187434139310514121985316880384 : ℝ), 1, 1), ((17415887492321751728099012454859074401576603819839/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((496069500345935495874720563489633889032974132458052828514490363/26328072917139296674479506920917608079723773850137277813577744384 : ℝ), 3, 1), ((22915350142587235224789968274846348406141676690729211500632002383380275096732685/7588550360256754183279148073529370729071901715047420004889892225542594864082845696 : ℝ), 4, 1), ((55937341003643569915133854906195802527120239252945214044765655107577142798913516081783428823507/136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864 : ℝ), 5, 1), ((1603847872374989405357661570995523012960951469836478709197029557273184699020503757009350489386409/34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184 : ℝ), 6, 1), ((2992975939097486838177170516320391024813125063156334275579374078656847544584290453630880886764811465685831262495/630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056 : ℝ), 7, 1), ((4958209211678590868794529091871623629007565949022050870137692024112272597173843858972170068251301419458531096563/20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792 : ℝ), 8, 1), ((-88618492494045640738501457660576456866059756583474092278487268659264860588013516591138310059118389532533465375/40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584 : ℝ), 9, 1)] h y := by
  simp only [exact316, polynomial313, polynomial315, evaluate] <;> ring
theorem bound316 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact316 h y| ≤ (468202504335/1099511627776 : ℝ) := by
  rw [polynomial316]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error316 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded316 rnd h y - exact316 h y| ≤ (166939403575965052826781/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded316 exact316
  apply rounded_step rnd hrnd (propagation := (1271165966398948479313127/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (468202504335/1099511627776 : ℝ))
  · convert FindOrb.add_error (error313 rnd hrnd h y hh hy) (error315 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound316 h y hh hy
  · norm_num
  · norm_num
def exact317 (h y : ℝ) : ℝ := (2849652349149073/18014398509481984 : ℝ)
def rounded317 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (2849652349149073/18014398509481984 : ℝ)
theorem polynomial317 (h y : ℝ) : exact317 h y = evaluate [((2849652349149073/18014398509481984 : ℝ), 0, 0)] h y := by
  simp only [exact317, evaluate] <;> ring
theorem bound317 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact317 h y| ≤ (173928976389/1099511627776 : ℝ) := by
  rw [polynomial317]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error317 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded317 rnd h y - exact317 h y| ≤ (0/1 : ℝ) := by
  simp [rounded317, exact317]
def exact318 (h y : ℝ) : ℝ := exact317 h y * exact209 h y
def rounded318 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded317 rnd h y * rounded209 rnd h y)
theorem polynomial318 (h y : ℝ) : exact318 h y = evaluate [((2849652349149073/18014398509481984 : ℝ), 0, 1), ((11866755036103396448522709291683/81129638414606681695789005144064 : ℝ), 1, 1), ((395332083589593450862116216995372741648361096201/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((17560257581206241360955780880935187218573853696053156722572464959/842498333348457493583344221469363458551160763204392890034487820288 : ℝ), 3, 1), ((18281464680180762921899351809851714865996747938550318952052754830612138261304429/3794275180128377091639574036764685364535950857523710002444946112771297432041422848 : ℝ), 4, 1), ((14692020672670665108472865961914883261378354103218890713275075295212333286951958669810413692507/17087896287367280659160173649356416916821636178853222159576332862577757806245124400183696695492608 : ℝ), 5, 1), ((165933598725325747092400936061237257700078496230369358260147123896203815950918647046690829800383091638942463443/1231312693637327475383720003129487931408741852202045208373384168882678805359287831606695820465153613775207124697088 : ℝ), 6, 1), ((1363917753394067397552960403123783001671786880059789300439545260253447454043907002193173843054763963886056218145/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 : ℝ), 7, 1), ((11648789936363077700738524112726771515958805140334070261837490202723478283325627987742128276768631203548026425389363414902525215/5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223552 : ℝ), 8, 1), ((60675707900411178849872562709305989180219687713725721391338712181990085508177097762769437670975020575026027954852215443103462387/181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 : ℝ), 9, 1), ((-981393761335157901412873825870268805042012549781752593799028768700052710913275406993722696474823503736554159404474255128153375/363419362147803445274661903944002267176820680343659030140745099590319644056698961663095525356881782780381260803133088966767300814307328 : ℝ), 10, 1)] h y := by
  simp only [exact318, polynomial317, polynomial209, evaluate] <;> ring
theorem bound318 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact318 h y| ≤ (92138314897/1099511627776 : ℝ) := by
  rw [polynomial318]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error318 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded318 rnd h y - exact318 h y| ≤ (419519856542976649383337/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded318 exact318
  apply rounded_step rnd hrnd (propagation := (223671705935038222301480079333095571/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (92138314897/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound317 h y hh hy) (bound209 h y hh hy)
      (error317 rnd hrnd h y hh hy) (error209 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound318 h y hh hy
  · norm_num
  · norm_num
def exact319 (h y : ℝ) : ℝ := exact316 h y + exact318 h y
def rounded319 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded316 rnd h y + rounded318 rnd h y)
theorem polynomial319 (h y : ℝ) : exact319 h y = evaluate [((142401592016916009/144115188075855872 : ℝ), 0, 1), ((10137638498749495249968320506194117/20769187434139310514121985316880384 : ℝ), 1, 1), ((30066514167188742155686731398711002134324158898271/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((33434481592276177228946838912603471667629025934710847235036156575/842498333348457493583344221469363458551160763204392890034487820288 : ℝ), 3, 1), ((59478279502948761068588671894549778138135172567829849404737512044604551619341543/7588550360256754183279148073529370729071901715047420004889892225542594864082845696 : ℝ), 4, 1), ((173473506385008890782916782601514868618147072078696339750966257469275809094529185440266738363563/136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864 : ℝ), 5, 1), ((222363979040848912025378752681979942397331734506390045303129309829689381657655630044094814639991180312263947731/1231312693637327475383720003129487931408741852202045208373384168882678805359287831606695820465153613775207124697088 : ℝ), 6, 1), ((13904317966250026018600853741310655038187420103634648679095736160684427176935546471176271631202923176774281007655/630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056 : ℝ), 7, 1), ((13044401758746869110780944010246683438327863231349470041048490765074443297008124550591242412839311124582079260336409397349600543/5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223552 : ℝ), 8, 1), ((60276605690636859805526597606335808920415306470053628999414002521439161072849530094990212210444414268654806408976102509190886387/181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 : ℝ), 9, 1), ((-981393761335157901412873825870268805042012549781752593799028768700052710913275406993722696474823503736554159404474255128153375/363419362147803445274661903944002267176820680343659030140745099590319644056698961663095525356881782780381260803133088966767300814307328 : ℝ), 10, 1)] h y := by
  simp only [exact319, polynomial316, polynomial318, evaluate] <;> ring
theorem bound319 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact319 h y| ≤ (560340819231/1099511627776 : ℝ) := by
  rw [polynomial319]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error319 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded319 rnd h y - exact319 h y| ≤ (916023870466724421908809/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded319 exact319
  apply rounded_step rnd hrnd (propagation := (1755035085150697071997585/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (560340819231/1099511627776 : ℝ))
  · convert FindOrb.add_error (error316 rnd hrnd h y hh hy) (error318 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound319 h y hh hy
  · norm_num
  · norm_num
def exact320 (h y : ℝ) : ℝ := (-8578800240006029/36028797018963968 : ℝ)
def rounded320 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-8578800240006029/36028797018963968 : ℝ)
theorem polynomial320 (h y : ℝ) : exact320 h y = evaluate [((-8578800240006029/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact320, evaluate] <;> ring
theorem bound320 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact320 h y| ≤ (16362762909/68719476736 : ℝ) := by
  rw [polynomial320]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error320 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded320 rnd h y - exact320 h y| ≤ (0/1 : ℝ) := by
  simp [rounded320, exact320]
def exact321 (h y : ℝ) : ℝ := exact320 h y * exact246 h y
def rounded321 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded320 rnd h y * rounded246 rnd h y)
theorem polynomial321 (h y : ℝ) : exact321 h y = evaluate [((-8578800240006029/36028797018963968 : ℝ), 0, 1), ((-38635481564177048119471736702297/162259276829213363391578010288128 : ℝ), 1, 1), ((-695994961502829967069162812151206416361439059185/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((-66868963184552314687575322006384348814480963868643601693800055823/1684996666696914987166688442938726917102321526408785780068975640576 : ℝ), 3, 1), ((-150575518840300633413543182274614530665858341403839814456057247920294451706368485/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 4, 1), ((-272392249884857230042448760105789472592127615710701855298740684120377567874641606858139949750507/136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864 : ℝ), 5, 1), ((-798928472642375165121081528470878552275140753524762202610476635695812690777693450948082638711070437443760005601/2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176 : ℝ), 6, 1), ((-1045606646536965930016537611232914269304934501096959108702334108639048340527263935178062600958606554659448093936025738973029111/22181357552966518876627313473144669627491496603006532601363836644916970462445004984319795248833116624779129687691228574631793262592 : ℝ), 7, 1), ((-60251249428839550660651205067478104705336841637049801631153895226982212523848967157370429759939517823546183638801466546974099957/11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104 : ℝ), 8, 1), ((-64068558427639618784358948003424710616414595361398948286461903580247280686271273933947033547852772319485543083105159111641113285785405946375891/102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168 : ℝ), 9, 1), ((-215814728835206343299814121254495128555947123458148058434641921361805134133687788556685662950769502497807967803026188560429869218930203169669783/3273390607896141870013189696827599152216642046043064789483291368096133796404674554883270092325904157150886684127560071009217256545885393053328527589376 : ℝ), 10, 1), ((3582639647413854100232798202308224460569317287971519335675898426481048861048180805254262059044073111956079003646324972232035974655813610417875/6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106657055178752 : ℝ), 11, 1)] h y := by
  simp only [exact321, polynomial320, polynomial246, evaluate] <;> ring
theorem bound321 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact321 h y| ≤ (69672281799/549755813888 : ℝ) := by
  rw [polynomial321]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error321 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded321 rnd h y - exact321 h y| ≤ (305834426526109421414111/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded321 exact321
  apply rounded_step rnd hrnd (propagation := (2462588695664786496426286384085283/13479973333575319897333507543509815336818572211270286240551805124608 : ℝ)) (magnitude := (69672281799/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound320 h y hh hy) (bound246 h y hh hy)
      (error320 rnd hrnd h y hh hy) (error246 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound321 h y hh hy
  · norm_num
  · norm_num
def exact322 (h y : ℝ) : ℝ := exact319 h y + exact321 h y
def rounded322 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded319 rnd h y + rounded321 rnd h y)
theorem polynomial322 (h y : ℝ) : exact322 h y = evaluate [((108086391056891893/144115188075855872 : ℝ), 0, 1), ((5192296858534833090675938208300101/20769187434139310514121985316880384 : ℝ), 1, 1), ((7794675399098183209473521409872396810758109004351/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((39770318355818822594520777088000778092776272257327/1684996666696914987166688442938726917102321526408785780068975640576 : ℝ), 3, 1), ((-31618959834403111276365838485514974389587996268180115646582223831085348467685399/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 4, 1), ((-1545605367185130300930187148504290687093445994250086180433975416423464980939256584654268927921/2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 : ℝ), 5, 1), ((-354200514560677341070324023106918667480477284511982112004218016036433927462382190859893009431088076819232110139/2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176 : ℝ), 6, 1), ((-556391949570993195990483942396697375329565998098134174841647992486243245501134813131370918185785536577381959290944440841020151/22181357552966518876627313473144669627491496603006532601363836644916970462445004984319795248833116624779129687691228574631793262592 : ℝ), 7, 1), ((-34162445911345812439089317046984737828681115174350861549056913696833325929832718056187944934260895574382025118128647752274898871/11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104 : ℝ), 8, 1), ((-30135846061700808720036564062302032591729265515723648334251119292260111237638625560975826825142546911027033377592469628190382025843185409896147/102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168 : ℝ), 9, 1), ((-224654337990911836519391625248553667839480272557586589223608978731149117386563109919621118175519493758751797057825522895167818159883706045317783/3273390607896141870013189696827599152216642046043064789483291368096133796404674554883270092325904157150886684127560071009217256545885393053328527589376 : ℝ), 10, 1), ((3582639647413854100232798202308224460569317287971519335675898426481048861048180805254262059044073111956079003646324972232035974655813610417875/6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106657055178752 : ℝ), 11, 1)] h y := by
  simp only [exact322, polynomial319, polynomial321, evaluate] <;> ring
theorem bound322 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact322 h y| ≤ (210498145677/549755813888 : ℝ) := by
  rw [polynomial322]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error322 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded322 rnd h y - exact322 h y| ≤ (1097871728579422613556409/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded322 exact322
  apply rounded_step rnd hrnd (propagation := (2137882167459558265231729/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (210498145677/549755813888 : ℝ))
  · convert FindOrb.add_error (error319 rnd hrnd h y hh hy) (error321 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound322 h y hh hy
  · norm_num
  · norm_num
def exact323 (h y : ℝ) : ℝ := (1/4 : ℝ)
def rounded323 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1/4 : ℝ)
theorem polynomial323 (h y : ℝ) : exact323 h y = evaluate [((1/4 : ℝ), 0, 0)] h y := by
  simp only [exact323, evaluate] <;> ring
theorem bound323 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact323 h y| ≤ (1/4 : ℝ) := by
  rw [polynomial323]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error323 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded323 rnd h y - exact323 h y| ≤ (0/1 : ℝ) := by
  simp [rounded323, exact323]
def exact324 (h y : ℝ) : ℝ := exact323 h y * exact286 h y
def rounded324 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded323 rnd h y * rounded286 rnd h y)
theorem polynomial324 (h y : ℝ) : exact324 h y = evaluate [((1/4 : ℝ), 0, 1), ((36028797018963963/144115188075855872 : ℝ), 1, 1), ((5192296858534827325360266242693937/41538374868278621028243970633760768 : ℝ), 2, 1), ((249429612771140978914079556033434521235184791159407/5986310706507378352962293074805895248510699696029696 : ℝ), 3, 1), ((280832777782819428256680892446021048623324476008619936524009365633/26959946667150639794667015087019630673637144422540572481103610249216 : ℝ), 4, 1), ((32061493216320955071401874053685894374167976944958750035793096469617181177684341/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 5, 1), ((2994286286755207251345522719845315511591974775980821924488427772593240398401716172224925364751131/8749002899132047697490008908470485461412677723572849745703082425639811996797503692894052708092215296 : ℝ), 6, 1), ((61424466923288600886667399651330982476476585188242577497455388771581253731974563342570494566605344399523880187/1231312693637327475383720003129487931408741852202045208373384168882678805359287831606695820465153613775207124697088 : ℝ), 7, 1), ((232411297748761976355626124087083636750355531172427717127325750997986169884754138440100573827644777160134564236167/40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584 : ℝ), 8, 1), ((3048871874338025025523281544655614967319630536261978037043589657955634206458597041858495139837962478341243745769012775615402215/5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223552 : ℝ), 9, 1), ((16902668847565035945433713136053068206352472561299166531232504916304553179209295845340813777807750020440303876383309777953739291/181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 : ℝ), 10, 1), ((-272818310354067841151473392356834799969881488990766738906943698960005864584782014355850865078004643770524084268849982769926375/363419362147803445274661903944002267176820680343659030140745099590319644056698961663095525356881782780381260803133088966767300814307328 : ℝ), 11, 1)] h y := by
  simp only [exact324, polynomial323, polynomial286, evaluate] <;> ring
theorem bound324 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact324 h y| ≤ (73151502213/549755813888 : ℝ) := by
  rw [polynomial324]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error324 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded324 rnd h y - exact324 h y| ≤ (21437703945088791064439/98079714615416886934934209737619787751599303819750539264 : ℝ) := by
  unfold rounded324 exact324
  apply rounded_step rnd hrnd (propagation := (1291582125213207331855807/6277101735386680763835789423207666416102355444464034512896 : ℝ)) (magnitude := (73151502213/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound323 h y hh hy) (bound286 h y hh hy)
      (error323 rnd hrnd h y hh hy) (error286 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound324 h y hh hy
  · norm_num
  · norm_num
def exact325 (h y : ℝ) : ℝ := exact322 h y + exact324 h y
def rounded325 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded322 rnd h y + rounded324 rnd h y)
theorem polynomial325 (h y : ℝ) : exact325 h y = evaluate [((144115188075855861/144115188075855872 : ℝ), 0, 1), ((10384593717069659998630494158240837/20769187434139310514121985316880384 : ℝ), 1, 1), ((31178701596392628535375143485826180160972740887103/187072209578355573530071658587684226515959365500928 : ℝ), 2, 1), ((70208194445704891196263368426588352555518660570848673221683798319/1684996666696914987166688442938726917102321526408785780068975640576 : ℝ), 3, 1), ((126475839337612749341454760810649370128141252242212186850615514620375250634885097/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 4, 1), ((2966648661001267779148665567914924331908388647209681475121757801170414802005052978125360590927/2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 : ℝ), 5, 1), ((488616148268781253277491516581200033851694077555731542050862989101229998599993155642499732302704327391203641797/2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176 : ℝ), 6, 1), ((550132875817622403464547672870906095213726037948296487994199224767078971402180265371709083300367878018023238574703118210030857/22181357552966518876627313473144669627491496603006532601363836644916970462445004984319795248833116624779129687691228574631793262592 : ℝ), 7, 1), ((31255518709780302098267304764383989574848434912336142351964682752343616188035235372759878528749759607350926264529505786534596681/11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104 : ℝ), 8, 1), ((24787746886975652123235664594431107926050862467553584054047362232230103117038611557477399047561315781881073256555235200818403047130326046298413/102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168 : ℝ), 9, 1), ((79837074502931311238385648313018360994078415505515117574553777246852362844476172715154345388987842285995623202252792504841877174898666152115561/3273390607896141870013189696827599152216642046043064789483291368096133796404674554883270092325904157150886684127560071009217256545885393053328527589376 : ℝ), 10, 1), ((-1332018115987858939988847954467464107509145716439132280045866149696349988358711684883825934650784334832483188378128792755438795279341458510125/6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106657055178752 : ℝ), 11, 1)] h y := by
  simp only [exact325, polynomial322, polynomial324, evaluate] <;> ring
theorem bound325 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact325 h y| ≤ (567299260059/1099511627776 : ℝ) := by
  rw [polynomial325]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error325 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded325 rnd h y - exact325 h y| ≤ (2616715736888214813118691/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded325 exact325
  apply rounded_step rnd hrnd (propagation := (1269373360140132942071921/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (567299260059/1099511627776 : ℝ))
  · convert FindOrb.add_error (error322 rnd hrnd h y hh hy) (error324 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound325 h y hh hy
  · norm_num
  · norm_num
def exact326 (h y : ℝ) : ℝ := exact325 h y * exact0 h y
def rounded326 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded325 rnd h y * rounded0 rnd h y)
theorem polynomial326 (h y : ℝ) : exact326 h y = evaluate [((144115188075855861/144115188075855872 : ℝ), 1, 1), ((10384593717069659998630494158240837/20769187434139310514121985316880384 : ℝ), 2, 1), ((31178701596392628535375143485826180160972740887103/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((70208194445704891196263368426588352555518660570848673221683798319/1684996666696914987166688442938726917102321526408785780068975640576 : ℝ), 4, 1), ((126475839337612749341454760810649370128141252242212186850615514620375250634885097/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 5, 1), ((2966648661001267779148665567914924331908388647209681475121757801170414802005052978125360590927/2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 : ℝ), 6, 1), ((488616148268781253277491516581200033851694077555731542050862989101229998599993155642499732302704327391203641797/2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176 : ℝ), 7, 1), ((550132875817622403464547672870906095213726037948296487994199224767078971402180265371709083300367878018023238574703118210030857/22181357552966518876627313473144669627491496603006532601363836644916970462445004984319795248833116624779129687691228574631793262592 : ℝ), 8, 1), ((31255518709780302098267304764383989574848434912336142351964682752343616188035235372759878528749759607350926264529505786534596681/11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104 : ℝ), 9, 1), ((24787746886975652123235664594431107926050862467553584054047362232230103117038611557477399047561315781881073256555235200818403047130326046298413/102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168 : ℝ), 10, 1), ((79837074502931311238385648313018360994078415505515117574553777246852362844476172715154345388987842285995623202252792504841877174898666152115561/3273390607896141870013189696827599152216642046043064789483291368096133796404674554883270092325904157150886684127560071009217256545885393053328527589376 : ℝ), 11, 1), ((-1332018115987858939988847954467464107509145716439132280045866149696349988358711684883825934650784334832483188378128792755438795279341458510125/6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106657055178752 : ℝ), 12, 1)] h y := by
  simp only [exact326, polynomial325, polynomial0, evaluate] <;> ring
theorem bound326 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact326 h y| ≤ (17728101877/549755813888 : ℝ) := by
  rw [polynomial326]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error326 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded326 rnd h y - exact326 h y| ≤ (168417797093553183553807/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded326 exact326
  apply rounded_step rnd hrnd (propagation := (2616715736888214813118691/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (17728101877/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound325 h y hh hy) (bound0 h y hh hy)
      (error325 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound326 h y hh hy
  · norm_num
  · norm_num
def exact327 (h y : ℝ) : ℝ := exact326 h y + exact3 h y
def rounded327 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded326 rnd h y + rounded3 rnd h y)
theorem polynomial327 (h y : ℝ) : exact327 h y = evaluate [((1/1 : ℝ), 0, 1), ((144115188075855861/144115188075855872 : ℝ), 1, 1), ((10384593717069659998630494158240837/20769187434139310514121985316880384 : ℝ), 2, 1), ((31178701596392628535375143485826180160972740887103/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((70208194445704891196263368426588352555518660570848673221683798319/1684996666696914987166688442938726917102321526408785780068975640576 : ℝ), 4, 1), ((126475839337612749341454760810649370128141252242212186850615514620375250634885097/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 5, 1), ((2966648661001267779148665567914924331908388647209681475121757801170414802005052978125360590927/2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 : ℝ), 6, 1), ((488616148268781253277491516581200033851694077555731542050862989101229998599993155642499732302704327391203641797/2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176 : ℝ), 7, 1), ((550132875817622403464547672870906095213726037948296487994199224767078971402180265371709083300367878018023238574703118210030857/22181357552966518876627313473144669627491496603006532601363836644916970462445004984319795248833116624779129687691228574631793262592 : ℝ), 8, 1), ((31255518709780302098267304764383989574848434912336142351964682752343616188035235372759878528749759607350926264529505786534596681/11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104 : ℝ), 9, 1), ((24787746886975652123235664594431107926050862467553584054047362232230103117038611557477399047561315781881073256555235200818403047130326046298413/102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168 : ℝ), 10, 1), ((79837074502931311238385648313018360994078415505515117574553777246852362844476172715154345388987842285995623202252792504841877174898666152115561/3273390607896141870013189696827599152216642046043064789483291368096133796404674554883270092325904157150886684127560071009217256545885393053328527589376 : ℝ), 11, 1), ((-1332018115987858939988847954467464107509145716439132280045866149696349988358711684883825934650784334832483188378128792755438795279341458510125/6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106657055178752 : ℝ), 12, 1)] h y := by
  simp only [exact327, polynomial326, polynomial3, evaluate] <;> ring
theorem bound327 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact327 h y| ≤ (292606008821/549755813888 : ℝ) := by
  rw [polynomial327]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error327 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded327 rnd h y - exact327 h y| ≤ (324406588083421588125969/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded327 exact327
  apply rounded_step rnd hrnd (propagation := (15248478801216719185809/98079714615416886934934209737619787751599303819750539264 : ℝ)) (magnitude := (292606008821/549755813888 : ℝ))
  · convert FindOrb.add_error (error326 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound327 h y hh hy
  · norm_num
  · norm_num
def exact328 (h y : ℝ) : ℝ := exact327 h y + exact2 h y
def rounded328 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded327 rnd h y + rounded2 rnd h y)
theorem polynomial328 (h y : ℝ) : exact328 h y = evaluate [((1/1 : ℝ), 0, 1), ((144115188075855861/144115188075855872 : ℝ), 1, 1), ((10384593717069659998630494158240837/20769187434139310514121985316880384 : ℝ), 2, 1), ((31178701596392628535375143485826180160972740887103/187072209578355573530071658587684226515959365500928 : ℝ), 3, 1), ((70208194445704891196263368426588352555518660570848673221683798319/1684996666696914987166688442938726917102321526408785780068975640576 : ℝ), 4, 1), ((126475839337612749341454760810649370128141252242212186850615514620375250634885097/15177100720513508366558296147058741458143803430094840009779784451085189728165691392 : ℝ), 5, 1), ((2966648661001267779148665567914924331908388647209681475121757801170414802005052978125360590927/2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 : ℝ), 6, 1), ((488616148268781253277491516581200033851694077555731542050862989101229998599993155642499732302704327391203641797/2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176 : ℝ), 7, 1), ((550132875817622403464547672870906095213726037948296487994199224767078971402180265371709083300367878018023238574703118210030857/22181357552966518876627313473144669627491496603006532601363836644916970462445004984319795248833116624779129687691228574631793262592 : ℝ), 8, 1), ((31255518709780302098267304764383989574848434912336142351964682752343616188035235372759878528749759607350926264529505786534596681/11356855067118857664833184498250070849275646260739344691898284362197488876771842551971735167402555711886914400097909030211478150447104 : ℝ), 9, 1), ((24787746886975652123235664594431107926050862467553584054047362232230103117038611557477399047561315781881073256555235200818403047130326046298413/102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168 : ℝ), 10, 1), ((79837074502931311238385648313018360994078415505515117574553777246852362844476172715154345388987842285995623202252792504841877174898666152115561/3273390607896141870013189696827599152216642046043064789483291368096133796404674554883270092325904157150886684127560071009217256545885393053328527589376 : ℝ), 11, 1), ((-1332018115987858939988847954467464107509145716439132280045866149696349988358711684883825934650784334832483188378128792755438795279341458510125/6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106657055178752 : ℝ), 12, 1)] h y := by
  simp only [exact328, polynomial327, polynomial2, evaluate] <;> ring
theorem bound328 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact328 h y| ≤ (292606008821/549755813888 : ℝ) := by
  rw [polynomial328]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error328 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded328 rnd h y - exact328 h y| ≤ (202418757673687834639497/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded328 exact328
  apply rounded_step rnd hrnd (propagation := (324406588083421588125969/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (292606008821/549755813888 : ℝ))
  · convert FindOrb.add_error (error327 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound328 h y hh hy
  · norm_num
  · norm_num
def step := rounded328
theorem stored_vs_taylor (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact328 h y - y * (∑ m ∈ Finset.range 16, h^m / m.factorial)| ≤ (6811385749998772760960612313425539033574217319738582317014245406850549437297055603464573600162342005202723575877955330388567341213298072547747963859904359919/2353245701186302471436662802711171787902758549410752026551487369495065127049294766575646995026876743585800443225069566458014260578597744509370722654302503534991895412342784000 : ℝ) := by
  have hid : exact328 h y - y * (∑ m ∈ Finset.range 16, h^m / m.factorial) =
      evaluate [((-11/144115188075855872 : ℝ), 1, 1), ((4741569501499800645/20769187434139310514121985316880384 : ℝ), 2, 1), ((98841089601163636427224938539910845/561216628735066720590214975763052679547878096502784 : ℝ), 3, 1), ((300192954049912424193028765790911447797156429439885/5054990000090744961500065328816180751306964579226357340206926921728 : ℝ), 4, 1), ((2694302034393777397869654143354871327801536759662919980043502565031/227656510807702625498374442205881121872157051451422600146696766766277845922485370880 : ℝ), 5, 1), ((169912001093920574587773208456477144868258789000563779933228937349639206096158179/96119416616440953707775976777629845157121703506049374647616872351999887660128824751033293912145920 : ℝ), 6, 1), ((160359444827331892019237190902904799784699348820456552598889086865076550438117207661406328256578919/775726996991516309491743601971577396787507366887288481275232026396087647376351333912218366893046776678380488559165440 : ℝ), 7, 1), ((128367681630445392688527546384742724857770017782013216044253835182152089960858107157944590369465943758996848835091/6987127629184453446137603744040570932659821429947057769429608543148845695670176570060735503382431736805425851622737001009014877716480 : ℝ), 8, 1), ((-116034669638919057921444885550068065270673435553166837635470976773729956700127655504925366326898012276642790823765393701591459733/32196684115281961479802078052538950857696457149196042201531636166829880965648173634839869199586245443199402324277572100649540556517539840 : ℝ), 9, 1), ((-48217502317567136769978899787464332284049586783544253343850731190185870884907680548157049692945321100293633771869588759016477693876528812925138253/1450009745841494093982405123516600561958465656333138855966426723211334267626133181733448548709990357112931835859630125204864206610560170204091621205606400 : ℝ), 10, 1), ((-338086220224739474893740040025421250344581054658277126106809189410067965680812749402332493370133805426783562062014856062285209886290296845945711971/510403430536205921081806603477843397809379911029264877300182206570389662204398879970173889145916605703752006222589804072112200726917179911840250664373452800 : ℝ), 11, 1), ((-7016425805253372805522794478517422617063219633685176019258008491486971436907376348402918575655302199161590378380219959721052836652976359061856002323/3062420583217235526490839620867060386856279466175589263801093239422337973226393279821043334875499634222512037335538824432673204361503079471041503986240716800 : ℝ), 12, 1), ((-1/6227020800 : ℝ), 13, 1), ((-1/87178291200 : ℝ), 14, 1), ((-1/1307674368000 : ℝ), 15, 1)] h y := by
    rw [polynomial328]
    norm_num [evaluate, Finset.sum_range_succ, Nat.factorial] <;> ring
  rw [hid]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem local_error (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |step rnd h y - y * Real.exp h| ≤ (579/200000000000000000000 : ℝ) := by
  have ht : |y * (∑ m ∈ Finset.range 16, h^m / m.factorial) - y * Real.exp h| ≤ (17/12350635211901892262408283488256000 : ℝ) := by
    rw [← mul_sub, abs_mul, abs_sub_comm]
    exact le_trans (mul_le_mul hy (exp_taylor_bound h hh) (abs_nonneg _) (by norm_num)) (by norm_num [Nat.factorial])
  have he := FindOrb.error_trans (error328 rnd hrnd h y hh hy)
    (FindOrb.error_trans (stored_vs_taylor h y hh hy) ht)
  exact le_trans he (by norm_num)
theorem multiple_steps (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (values steps : Nat → ℝ) (initial initialError : ℝ)
    (hstep : ∀ n, |steps n| ≤ 1/16) (hstate : ∀ n, |values n| ≤ 1/2)
    (hrec : ∀ n, values (n+1) = step rnd (steps n) (values n))
    (hzero : |values 0 - initial| ≤ initialError) :
    ∀ n, |values n - initial * Real.exp (elapsedTime steps n)| ≤
      FindOrb.errorBudget (16/15) (579/200000000000000000000 : ℝ) initialError n := by
  apply FindOrb.global_error_bound (ha := by norm_num)
  · simpa [elapsedTime] using hzero
  · intro n
    rw [hrec n, sampled_solution_step]
    exact accumulated_step (hstep n) (local_error rnd hrnd (steps n) (values n) (hstep n) (hstate n))
#print axioms stored_vs_taylor
#print axioms local_error
#print axioms multiple_steps
#print axioms polynomial0
#print axioms error0
#print axioms polynomial1
#print axioms error1
#print axioms polynomial2
#print axioms error2
#print axioms polynomial3
#print axioms error3
#print axioms polynomial4
#print axioms error4
#print axioms polynomial5
#print axioms error5
#print axioms polynomial6
#print axioms error6
#print axioms polynomial7
#print axioms error7
#print axioms polynomial8
#print axioms error8
#print axioms polynomial9
#print axioms error9
#print axioms polynomial10
#print axioms error10
#print axioms polynomial11
#print axioms error11
#print axioms polynomial12
#print axioms error12
#print axioms polynomial13
#print axioms error13
#print axioms polynomial14
#print axioms error14
#print axioms polynomial15
#print axioms error15
#print axioms polynomial16
#print axioms error16
#print axioms polynomial17
#print axioms error17
#print axioms polynomial18
#print axioms error18
#print axioms polynomial19
#print axioms error19
#print axioms polynomial20
#print axioms error20
#print axioms polynomial21
#print axioms error21
#print axioms polynomial22
#print axioms error22
#print axioms polynomial23
#print axioms error23
#print axioms polynomial24
#print axioms error24
#print axioms polynomial25
#print axioms error25
#print axioms polynomial26
#print axioms error26
#print axioms polynomial27
#print axioms error27
#print axioms polynomial28
#print axioms error28
#print axioms polynomial29
#print axioms error29
#print axioms polynomial30
#print axioms error30
#print axioms polynomial31
#print axioms error31
#print axioms polynomial32
#print axioms error32
#print axioms polynomial33
#print axioms error33
#print axioms polynomial34
#print axioms error34
#print axioms polynomial35
#print axioms error35
#print axioms polynomial36
#print axioms error36
#print axioms polynomial37
#print axioms error37
#print axioms polynomial38
#print axioms error38
#print axioms polynomial39
#print axioms error39
#print axioms polynomial40
#print axioms error40
#print axioms polynomial41
#print axioms error41
#print axioms polynomial42
#print axioms error42
#print axioms polynomial43
#print axioms error43
#print axioms polynomial44
#print axioms error44
#print axioms polynomial45
#print axioms error45
#print axioms polynomial46
#print axioms error46
#print axioms polynomial47
#print axioms error47
#print axioms polynomial48
#print axioms error48
#print axioms polynomial49
#print axioms error49
#print axioms polynomial50
#print axioms error50
#print axioms polynomial51
#print axioms error51
#print axioms polynomial52
#print axioms error52
#print axioms polynomial53
#print axioms error53
#print axioms polynomial54
#print axioms error54
#print axioms polynomial55
#print axioms error55
#print axioms polynomial56
#print axioms error56
#print axioms polynomial57
#print axioms error57
#print axioms polynomial58
#print axioms error58
#print axioms polynomial59
#print axioms error59
#print axioms polynomial60
#print axioms error60
#print axioms polynomial61
#print axioms error61
#print axioms polynomial62
#print axioms error62
#print axioms polynomial63
#print axioms error63
#print axioms polynomial64
#print axioms error64
#print axioms polynomial65
#print axioms error65
#print axioms polynomial66
#print axioms error66
#print axioms polynomial67
#print axioms error67
#print axioms polynomial68
#print axioms error68
#print axioms polynomial69
#print axioms error69
#print axioms polynomial70
#print axioms error70
#print axioms polynomial71
#print axioms error71
#print axioms polynomial72
#print axioms error72
#print axioms polynomial73
#print axioms error73
#print axioms polynomial74
#print axioms error74
#print axioms polynomial75
#print axioms error75
#print axioms polynomial76
#print axioms error76
#print axioms polynomial77
#print axioms error77
#print axioms polynomial78
#print axioms error78
#print axioms polynomial79
#print axioms error79
#print axioms polynomial80
#print axioms error80
#print axioms polynomial81
#print axioms error81
#print axioms polynomial82
#print axioms error82
#print axioms polynomial83
#print axioms error83
#print axioms polynomial84
#print axioms error84
#print axioms polynomial85
#print axioms error85
#print axioms polynomial86
#print axioms error86
#print axioms polynomial87
#print axioms error87
#print axioms polynomial88
#print axioms error88
#print axioms polynomial89
#print axioms error89
#print axioms polynomial90
#print axioms error90
#print axioms polynomial91
#print axioms error91
#print axioms polynomial92
#print axioms error92
#print axioms polynomial93
#print axioms error93
#print axioms polynomial94
#print axioms error94
#print axioms polynomial95
#print axioms error95
#print axioms polynomial96
#print axioms error96
#print axioms polynomial97
#print axioms error97
#print axioms polynomial98
#print axioms error98
#print axioms polynomial99
#print axioms error99
#print axioms polynomial100
#print axioms error100
#print axioms polynomial101
#print axioms error101
#print axioms polynomial102
#print axioms error102
#print axioms polynomial103
#print axioms error103
#print axioms polynomial104
#print axioms error104
#print axioms polynomial105
#print axioms error105
#print axioms polynomial106
#print axioms error106
#print axioms polynomial107
#print axioms error107
#print axioms polynomial108
#print axioms error108
#print axioms polynomial109
#print axioms error109
#print axioms polynomial110
#print axioms error110
#print axioms polynomial111
#print axioms error111
#print axioms polynomial112
#print axioms error112
#print axioms polynomial113
#print axioms error113
#print axioms polynomial114
#print axioms error114
#print axioms polynomial115
#print axioms error115
#print axioms polynomial116
#print axioms error116
#print axioms polynomial117
#print axioms error117
#print axioms polynomial118
#print axioms error118
#print axioms polynomial119
#print axioms error119
#print axioms polynomial120
#print axioms error120
#print axioms polynomial121
#print axioms error121
#print axioms polynomial122
#print axioms error122
#print axioms polynomial123
#print axioms error123
#print axioms polynomial124
#print axioms error124
#print axioms polynomial125
#print axioms error125
#print axioms polynomial126
#print axioms error126
#print axioms polynomial127
#print axioms error127
#print axioms polynomial128
#print axioms error128
#print axioms polynomial129
#print axioms error129
#print axioms polynomial130
#print axioms error130
#print axioms polynomial131
#print axioms error131
#print axioms polynomial132
#print axioms error132
#print axioms polynomial133
#print axioms error133
#print axioms polynomial134
#print axioms error134
#print axioms polynomial135
#print axioms error135
#print axioms polynomial136
#print axioms error136
#print axioms polynomial137
#print axioms error137
#print axioms polynomial138
#print axioms error138
#print axioms polynomial139
#print axioms error139
#print axioms polynomial140
#print axioms error140
#print axioms polynomial141
#print axioms error141
#print axioms polynomial142
#print axioms error142
#print axioms polynomial143
#print axioms error143
#print axioms polynomial144
#print axioms error144
#print axioms polynomial145
#print axioms error145
#print axioms polynomial146
#print axioms error146
#print axioms polynomial147
#print axioms error147
#print axioms polynomial148
#print axioms error148
#print axioms polynomial149
#print axioms error149
#print axioms polynomial150
#print axioms error150
#print axioms polynomial151
#print axioms error151
#print axioms polynomial152
#print axioms error152
#print axioms polynomial153
#print axioms error153
#print axioms polynomial154
#print axioms error154
#print axioms polynomial155
#print axioms error155
#print axioms polynomial156
#print axioms error156
#print axioms polynomial157
#print axioms error157
#print axioms polynomial158
#print axioms error158
#print axioms polynomial159
#print axioms error159
#print axioms polynomial160
#print axioms error160
#print axioms polynomial161
#print axioms error161
#print axioms polynomial162
#print axioms error162
#print axioms polynomial163
#print axioms error163
#print axioms polynomial164
#print axioms error164
#print axioms polynomial165
#print axioms error165
#print axioms polynomial166
#print axioms error166
#print axioms polynomial167
#print axioms error167
#print axioms polynomial168
#print axioms error168
#print axioms polynomial169
#print axioms error169
#print axioms polynomial170
#print axioms error170
#print axioms polynomial171
#print axioms error171
#print axioms polynomial172
#print axioms error172
#print axioms polynomial173
#print axioms error173
#print axioms polynomial174
#print axioms error174
#print axioms polynomial175
#print axioms error175
#print axioms polynomial176
#print axioms error176
#print axioms polynomial177
#print axioms error177
#print axioms polynomial178
#print axioms error178
#print axioms polynomial179
#print axioms error179
#print axioms polynomial180
#print axioms error180
#print axioms polynomial181
#print axioms error181
#print axioms polynomial182
#print axioms error182
#print axioms polynomial183
#print axioms error183
#print axioms polynomial184
#print axioms error184
#print axioms polynomial185
#print axioms error185
#print axioms polynomial186
#print axioms error186
#print axioms polynomial187
#print axioms error187
#print axioms polynomial188
#print axioms error188
#print axioms polynomial189
#print axioms error189
#print axioms polynomial190
#print axioms error190
#print axioms polynomial191
#print axioms error191
#print axioms polynomial192
#print axioms error192
#print axioms polynomial193
#print axioms error193
#print axioms polynomial194
#print axioms error194
#print axioms polynomial195
#print axioms error195
#print axioms polynomial196
#print axioms error196
#print axioms polynomial197
#print axioms error197
#print axioms polynomial198
#print axioms error198
#print axioms polynomial199
#print axioms error199
#print axioms polynomial200
#print axioms error200
#print axioms polynomial201
#print axioms error201
#print axioms polynomial202
#print axioms error202
#print axioms polynomial203
#print axioms error203
#print axioms polynomial204
#print axioms error204
#print axioms polynomial205
#print axioms error205
#print axioms polynomial206
#print axioms error206
#print axioms polynomial207
#print axioms error207
#print axioms polynomial208
#print axioms error208
#print axioms polynomial209
#print axioms error209
#print axioms polynomial210
#print axioms error210
#print axioms polynomial211
#print axioms error211
#print axioms polynomial212
#print axioms error212
#print axioms polynomial213
#print axioms error213
#print axioms polynomial214
#print axioms error214
#print axioms polynomial215
#print axioms error215
#print axioms polynomial216
#print axioms error216
#print axioms polynomial217
#print axioms error217
#print axioms polynomial218
#print axioms error218
#print axioms polynomial219
#print axioms error219
#print axioms polynomial220
#print axioms error220
#print axioms polynomial221
#print axioms error221
#print axioms polynomial222
#print axioms error222
#print axioms polynomial223
#print axioms error223
#print axioms polynomial224
#print axioms error224
#print axioms polynomial225
#print axioms error225
#print axioms polynomial226
#print axioms error226
#print axioms polynomial227
#print axioms error227
#print axioms polynomial228
#print axioms error228
#print axioms polynomial229
#print axioms error229
#print axioms polynomial230
#print axioms error230
#print axioms polynomial231
#print axioms error231
#print axioms polynomial232
#print axioms error232
#print axioms polynomial233
#print axioms error233
#print axioms polynomial234
#print axioms error234
#print axioms polynomial235
#print axioms error235
#print axioms polynomial236
#print axioms error236
#print axioms polynomial237
#print axioms error237
#print axioms polynomial238
#print axioms error238
#print axioms polynomial239
#print axioms error239
#print axioms polynomial240
#print axioms error240
#print axioms polynomial241
#print axioms error241
#print axioms polynomial242
#print axioms error242
#print axioms polynomial243
#print axioms error243
#print axioms polynomial244
#print axioms error244
#print axioms polynomial245
#print axioms error245
#print axioms polynomial246
#print axioms error246
#print axioms polynomial247
#print axioms error247
#print axioms polynomial248
#print axioms error248
#print axioms polynomial249
#print axioms error249
#print axioms polynomial250
#print axioms error250
#print axioms polynomial251
#print axioms error251
#print axioms polynomial252
#print axioms error252
#print axioms polynomial253
#print axioms error253
#print axioms polynomial254
#print axioms error254
#print axioms polynomial255
#print axioms error255
#print axioms polynomial256
#print axioms error256
#print axioms polynomial257
#print axioms error257
#print axioms polynomial258
#print axioms error258
#print axioms polynomial259
#print axioms error259
#print axioms polynomial260
#print axioms error260
#print axioms polynomial261
#print axioms error261
#print axioms polynomial262
#print axioms error262
#print axioms polynomial263
#print axioms error263
#print axioms polynomial264
#print axioms error264
#print axioms polynomial265
#print axioms error265
#print axioms polynomial266
#print axioms error266
#print axioms polynomial267
#print axioms error267
#print axioms polynomial268
#print axioms error268
#print axioms polynomial269
#print axioms error269
#print axioms polynomial270
#print axioms error270
#print axioms polynomial271
#print axioms error271
#print axioms polynomial272
#print axioms error272
#print axioms polynomial273
#print axioms error273
#print axioms polynomial274
#print axioms error274
#print axioms polynomial275
#print axioms error275
#print axioms polynomial276
#print axioms error276
#print axioms polynomial277
#print axioms error277
#print axioms polynomial278
#print axioms error278
#print axioms polynomial279
#print axioms error279
#print axioms polynomial280
#print axioms error280
#print axioms polynomial281
#print axioms error281
#print axioms polynomial282
#print axioms error282
#print axioms polynomial283
#print axioms error283
#print axioms polynomial284
#print axioms error284
#print axioms polynomial285
#print axioms error285
#print axioms polynomial286
#print axioms error286
#print axioms polynomial287
#print axioms error287
#print axioms polynomial288
#print axioms error288
#print axioms polynomial289
#print axioms error289
#print axioms polynomial290
#print axioms error290
#print axioms polynomial291
#print axioms error291
#print axioms polynomial292
#print axioms error292
#print axioms polynomial293
#print axioms error293
#print axioms polynomial294
#print axioms error294
#print axioms polynomial295
#print axioms error295
#print axioms polynomial296
#print axioms error296
#print axioms polynomial297
#print axioms error297
#print axioms polynomial298
#print axioms error298
#print axioms polynomial299
#print axioms error299
#print axioms polynomial300
#print axioms error300
#print axioms polynomial301
#print axioms error301
#print axioms polynomial302
#print axioms error302
#print axioms polynomial303
#print axioms error303
#print axioms polynomial304
#print axioms error304
#print axioms polynomial305
#print axioms error305
#print axioms polynomial306
#print axioms error306
#print axioms polynomial307
#print axioms error307
#print axioms polynomial308
#print axioms error308
#print axioms polynomial309
#print axioms error309
#print axioms polynomial310
#print axioms error310
#print axioms polynomial311
#print axioms error311
#print axioms polynomial312
#print axioms error312
#print axioms polynomial313
#print axioms error313
#print axioms polynomial314
#print axioms error314
#print axioms polynomial315
#print axioms error315
#print axioms polynomial316
#print axioms error316
#print axioms polynomial317
#print axioms error317
#print axioms polynomial318
#print axioms error318
#print axioms polynomial319
#print axioms error319
#print axioms polynomial320
#print axioms error320
#print axioms polynomial321
#print axioms error321
#print axioms polynomial322
#print axioms error322
#print axioms polynomial323
#print axioms error323
#print axioms polynomial324
#print axioms error324
#print axioms polynomial325
#print axioms error325
#print axioms polynomial326
#print axioms error326
#print axioms polynomial327
#print axioms error327
#print axioms polynomial328
#print axioms error328
end PDLinear
end
end FindOrbLinear
