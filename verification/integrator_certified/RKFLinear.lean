import LinearSupport
/- GPL-2.0-or-later. Generated connected proof; see generate.py. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
set_option linter.unusedVariables false
namespace FindOrbLinear
noncomputable section
namespace RKFLinear
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
def exact5 (h y : ℝ) : ℝ := (2001599834386887/9007199254740992 : ℝ)
def rounded5 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (2001599834386887/9007199254740992 : ℝ)
theorem polynomial5 (h y : ℝ) : exact5 h y = evaluate [((2001599834386887/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact5, evaluate] <;> ring
theorem bound5 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact5 h y| ≤ (61083979321/274877906944 : ℝ) := by
  rw [polynomial5]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error5 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded5 rnd h y - exact5 h y| ≤ (0/1 : ℝ) := by
  simp [rounded5, exact5]
def exact6 (h y : ℝ) : ℝ := exact5 h y * exact4 h y
def rounded6 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded5 rnd h y * rounded4 rnd h y)
theorem polynomial6 (h y : ℝ) : exact6 h y = evaluate [((2001599834386887/9007199254740992 : ℝ), 0, 1)] h y := by
  simp only [exact6, polynomial5, polynomial4, evaluate] <;> ring
theorem bound6 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact6 h y| ≤ (61083979321/549755813888 : ℝ) := by
  rw [polynomial6]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error6 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded6 rnd h y - exact6 h y| ≤ (33581272767134116610049/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded6 exact6
  apply rounded_step rnd hrnd (propagation := (4615374985372686543552270523665977/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (61083979321/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound5 h y hh hy) (bound4 h y hh hy)
      (error5 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound6 h y hh hy
  · norm_num
  · norm_num
def exact7 (h y : ℝ) : ℝ := exact2 h y + exact6 h y
def rounded7 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded6 rnd h y)
theorem polynomial7 (h y : ℝ) : exact7 h y = evaluate [((2001599834386887/9007199254740992 : ℝ), 0, 1)] h y := by
  simp only [exact7, polynomial2, polynomial6, evaluate] <;> ring
theorem bound7 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact7 h y| ≤ (61083979321/549755813888 : ℝ) := by
  rw [polynomial7]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error7 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded7 rnd h y - exact7 h y| ≤ (25185954575350587457537/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded7 exact7
  apply rounded_step rnd hrnd (propagation := (33581272767134116610049/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (61083979321/549755813888 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error6 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound7 h y hh hy
  · norm_num
  · norm_num
def exact8 (h y : ℝ) : ℝ := exact7 h y * exact0 h y
def rounded8 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded7 rnd h y * rounded0 rnd h y)
theorem polynomial8 (h y : ℝ) : exact8 h y = evaluate [((2001599834386887/9007199254740992 : ℝ), 1, 1)] h y := by
  simp only [exact8, polynomial7, polynomial0, evaluate] <;> ring
theorem bound8 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact8 h y| ≤ (954437177/137438953472 : ℝ) := by
  rw [polynomial8]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error8 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded8 rnd h y - exact8 h y| ≤ (4197659096012023660545/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded8 exact8
  apply rounded_step rnd hrnd (propagation := (25185954575350587457537/12554203470773361527671578846415332832204710888928069025792 : ℝ)) (magnitude := (954437177/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound7 h y hh hy) (bound0 h y hh hy)
      (error7 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound8 h y hh hy
  · norm_num
  · norm_num
def exact9 (h y : ℝ) : ℝ := exact8 h y + exact3 h y
def rounded9 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded8 rnd h y + rounded3 rnd h y)
theorem polynomial9 (h y : ℝ) : exact9 h y = evaluate [((1/1 : ℝ), 0, 1), ((2001599834386887/9007199254740992 : ℝ), 1, 1)] h y := by
  simp only [exact9, polynomial8, polynomial3, evaluate] <;> ring
theorem bound9 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact9 h y| ≤ (69673913913/137438953472 : ℝ) := by
  rw [polynomial9]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error9 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded9 rnd h y - exact9 h y| ≤ (156362801321933870727171/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded9 exact9
  apply rounded_step rnd hrnd (propagation := (39877761410963173539841/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (69673913913/137438953472 : ℝ))
  · convert FindOrb.add_error (error8 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound9 h y hh hy
  · norm_num
  · norm_num
def exact10 (h y : ℝ) : ℝ := exact9 h y + exact2 h y
def rounded10 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded9 rnd h y + rounded2 rnd h y)
theorem polynomial10 (h y : ℝ) : exact10 h y = evaluate [((1/1 : ℝ), 0, 1), ((2001599834386887/9007199254740992 : ℝ), 1, 1)] h y := by
  simp only [exact10, polynomial9, polynomial2, evaluate] <;> ring
theorem bound10 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact10 h y| ≤ (69673913913/137438953472 : ℝ) := by
  rw [polynomial10]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error10 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded10 rnd h y - exact10 h y| ≤ (58242519955485348593665/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded10 exact10
  apply rounded_step rnd hrnd (propagation := (156362801321933870727171/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (69673913913/137438953472 : ℝ))
  · convert FindOrb.add_error (error9 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound10 h y hh hy
  · norm_num
  · norm_num
def exact11 (h y : ℝ) : ℝ := exact10 h y + exact2 h y
def rounded11 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded10 rnd h y + rounded2 rnd h y)
theorem polynomial11 (h y : ℝ) : exact11 h y = evaluate [((1/1 : ℝ), 0, 1), ((2001599834386887/9007199254740992 : ℝ), 1, 1)] h y := by
  simp only [exact11, polynomial10, polynomial2, evaluate] <;> ring
theorem bound11 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact11 h y| ≤ (69673913913/137438953472 : ℝ) := by
  rw [polynomial11]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error11 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded11 rnd h y - exact11 h y| ≤ (309577358321948918022149/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded11 exact11
  apply rounded_step rnd hrnd (propagation := (58242519955485348593665/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (69673913913/137438953472 : ℝ))
  · convert FindOrb.add_error (error10 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound11 h y hh hy
  · norm_num
  · norm_num
def exact12 (h y : ℝ) : ℝ := (6004799503160661/72057594037927936 : ℝ)
def rounded12 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (6004799503160661/72057594037927936 : ℝ)
theorem polynomial12 (h y : ℝ) : exact12 h y = evaluate [((6004799503160661/72057594037927936 : ℝ), 0, 0)] h y := by
  simp only [exact12, evaluate] <;> ring
theorem bound12 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact12 h y| ≤ (45812984491/549755813888 : ℝ) := by
  rw [polynomial12]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error12 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded12 rnd h y - exact12 h y| ≤ (0/1 : ℝ) := by
  simp [rounded12, exact12]
def exact13 (h y : ℝ) : ℝ := exact12 h y * exact4 h y
def rounded13 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded12 rnd h y * rounded4 rnd h y)
theorem polynomial13 (h y : ℝ) : exact13 h y = evaluate [((6004799503160661/72057594037927936 : ℝ), 0, 1)] h y := by
  simp only [exact13, polynomial12, polynomial4, evaluate] <;> ring
theorem bound13 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact13 h y| ≤ (45812984491/1099511627776 : ℝ) := by
  rw [polynomial13]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error13 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded13 rnd h y - exact13 h y| ≤ (12592977287744013205505/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded13 exact13
  apply rounded_step rnd hrnd (propagation := (3461531239048404373595681473604267/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (45812984491/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound12 h y hh hy) (bound4 h y hh hy)
      (error12 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound13 h y hh hy
  · norm_num
  · norm_num
def exact14 (h y : ℝ) : ℝ := exact2 h y + exact13 h y
def rounded14 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded13 rnd h y)
theorem polynomial14 (h y : ℝ) : exact14 h y = evaluate [((6004799503160661/72057594037927936 : ℝ), 0, 1)] h y := by
  simp only [exact14, polynomial2, polynomial13, evaluate] <;> ring
theorem bound14 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact14 h y| ≤ (45812984491/1099511627776 : ℝ) := by
  rw [polynomial14]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error14 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded14 rnd h y - exact14 h y| ≤ (9444732965808009904129/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded14 exact14
  apply rounded_step rnd hrnd (propagation := (12592977287744013205505/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (45812984491/1099511627776 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error13 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound14 h y hh hy
  · norm_num
  · norm_num
def exact15 (h y : ℝ) : ℝ := (1/4 : ℝ)
def rounded15 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1/4 : ℝ)
theorem polynomial15 (h y : ℝ) : exact15 h y = evaluate [((1/4 : ℝ), 0, 0)] h y := by
  simp only [exact15, evaluate] <;> ring
theorem bound15 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact15 h y| ≤ (1/4 : ℝ) := by
  rw [polynomial15]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error15 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded15 rnd h y - exact15 h y| ≤ (0/1 : ℝ) := by
  simp [rounded15, exact15]
def exact16 (h y : ℝ) : ℝ := exact15 h y * exact11 h y
def rounded16 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded15 rnd h y * rounded11 rnd h y)
theorem polynomial16 (h y : ℝ) : exact16 h y = evaluate [((1/4 : ℝ), 0, 1), ((2001599834386887/36028797018963968 : ℝ), 1, 1)] h y := by
  simp only [exact16, polynomial15, polynomial11, evaluate] <;> ring
theorem bound16 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact16 h y| ≤ (69673913913/549755813888 : ℝ) := by
  rw [polynomial16]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error16 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded16 rnd h y - exact16 h y| ≤ (48273079602744555208705/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded16 exact16
  apply rounded_step rnd hrnd (propagation := (309577358321948918022149/6277101735386680763835789423207666416102355444464034512896 : ℝ)) (magnitude := (69673913913/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound15 h y hh hy) (bound11 h y hh hy)
      (error15 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound16 h y hh hy
  · norm_num
  · norm_num
def exact17 (h y : ℝ) : ℝ := exact14 h y + exact16 h y
def rounded17 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded14 rnd h y + rounded16 rnd h y)
theorem polynomial17 (h y : ℝ) : exact17 h y = evaluate [((24019198012642645/72057594037927936 : ℝ), 0, 1), ((2001599834386887/36028797018963968 : ℝ), 1, 1)] h y := by
  simp only [exact17, polynomial14, polynomial16, evaluate] <;> ring
theorem bound17 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact17 h y| ≤ (185160812317/1099511627776 : ℝ) := by
  rw [polynomial17]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error17 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded17 rnd h y - exact17 h y| ≤ (140883933405979017740293/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded17 exact17
  apply rounded_step rnd hrnd (propagation := (28858906284276282556417/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (185160812317/1099511627776 : ℝ))
  · convert FindOrb.add_error (error14 rnd hrnd h y hh hy) (error16 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound17 h y hh hy
  · norm_num
  · norm_num
def exact18 (h y : ℝ) : ℝ := exact17 h y * exact0 h y
def rounded18 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded17 rnd h y * rounded0 rnd h y)
theorem polynomial18 (h y : ℝ) : exact18 h y = evaluate [((24019198012642645/72057594037927936 : ℝ), 1, 1), ((2001599834386887/36028797018963968 : ℝ), 2, 1)] h y := by
  simp only [exact18, polynomial17, polynomial0, evaluate] <;> ring
theorem bound18 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact18 h y| ≤ (5786275385/549755813888 : ℝ) := by
  rw [polynomial18]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error18 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded18 rnd h y - exact18 h y| ≤ (10395765104704076382209/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded18 exact18
  apply rounded_step rnd hrnd (propagation := (140883933405979017740293/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (5786275385/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound17 h y hh hy) (bound0 h y hh hy)
      (error17 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound18 h y hh hy
  · norm_num
  · norm_num
def exact19 (h y : ℝ) : ℝ := exact18 h y + exact3 h y
def rounded19 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded18 rnd h y + rounded3 rnd h y)
theorem polynomial19 (h y : ℝ) : exact19 h y = evaluate [((1/1 : ℝ), 0, 1), ((24019198012642645/72057594037927936 : ℝ), 1, 1), ((2001599834386887/36028797018963968 : ℝ), 2, 1)] h y := by
  simp only [exact19, polynomial18, polynomial3, evaluate] <;> ring
theorem bound19 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact19 h y| ≤ (280664182329/549755813888 : ℝ) := by
  rw [polynomial19]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error19 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded19 rnd h y - exact19 h y| ≤ (163102011823363110993923/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded19 exact19
  apply rounded_step rnd hrnd (propagation := (42976814415309199900673/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (280664182329/549755813888 : ℝ))
  · convert FindOrb.add_error (error18 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound19 h y hh hy
  · norm_num
  · norm_num
def exact20 (h y : ℝ) : ℝ := exact19 h y + exact2 h y
def rounded20 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded19 rnd h y + rounded2 rnd h y)
theorem polynomial20 (h y : ℝ) : exact20 h y = evaluate [((1/1 : ℝ), 0, 1), ((24019198012642645/72057594037927936 : ℝ), 1, 1), ((2001599834386887/36028797018963968 : ℝ), 2, 1)] h y := by
  simp only [exact20, polynomial19, polynomial2, evaluate] <;> ring
theorem bound20 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact20 h y| ≤ (280664182329/549755813888 : ℝ) := by
  rw [polynomial20]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error20 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded20 rnd h y - exact20 h y| ≤ (60062598704026955546625/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded20 exact20
  apply rounded_step rnd hrnd (propagation := (163102011823363110993923/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (280664182329/549755813888 : ℝ))
  · convert FindOrb.add_error (error19 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound20 h y hh hy
  · norm_num
  · norm_num
def exact21 (h y : ℝ) : ℝ := exact20 h y + exact2 h y
def rounded21 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded20 rnd h y + rounded2 rnd h y)
theorem polynomial21 (h y : ℝ) : exact21 h y = evaluate [((1/1 : ℝ), 0, 1), ((24019198012642645/72057594037927936 : ℝ), 1, 1), ((2001599834386887/36028797018963968 : ℝ), 2, 1)] h y := by
  simp only [exact21, polynomial20, polynomial2, evaluate] <;> ring
theorem bound21 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact21 h y| ≤ (280664182329/549755813888 : ℝ) := by
  rw [polynomial21]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error21 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded21 rnd h y - exact21 h y| ≤ (317398777808852533379077/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded21 exact21
  apply rounded_step rnd hrnd (propagation := (60062598704026955546625/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (280664182329/549755813888 : ℝ))
  · convert FindOrb.add_error (error20 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound21 h y hh hy
  · norm_num
  · norm_num
def exact22 (h y : ℝ) : ℝ := (69/128 : ℝ)
def rounded22 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (69/128 : ℝ)
theorem polynomial22 (h y : ℝ) : exact22 h y = evaluate [((69/128 : ℝ), 0, 0)] h y := by
  simp only [exact22, evaluate] <;> ring
theorem bound22 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact22 h y| ≤ (69/128 : ℝ) := by
  rw [polynomial22]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error22 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded22 rnd h y - exact22 h y| ≤ (0/1 : ℝ) := by
  simp [rounded22, exact22]
def exact23 (h y : ℝ) : ℝ := exact22 h y * exact4 h y
def rounded23 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded22 rnd h y * rounded4 rnd h y)
theorem polynomial23 (h y : ℝ) : exact23 h y = evaluate [((69/128 : ℝ), 0, 1)] h y := by
  simp only [exact23, polynomial22, polynomial4, evaluate] <;> ring
theorem bound23 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact23 h y| ≤ (69/256 : ℝ) := by
  rw [polynomial23]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error23 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded23 rnd h y - exact23 h y| ≤ (81460821829501379936257/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded23 exact23
  apply rounded_step rnd hrnd (propagation := (5213492597088088315920453/200867255532373784442745261542645325315275374222849104412672 : ℝ)) (magnitude := (69/256 : ℝ))
  · convert FindOrb.mul_error (bound22 h y hh hy) (bound4 h y hh hy)
      (error22 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound23 h y hh hy
  · norm_num
  · norm_num
def exact24 (h y : ℝ) : ℝ := exact2 h y + exact23 h y
def rounded24 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded23 rnd h y)
theorem polynomial24 (h y : ℝ) : exact24 h y = evaluate [((69/128 : ℝ), 0, 1)] h y := by
  simp only [exact24, polynomial2, polynomial23, evaluate] <;> ring
theorem bound24 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact24 h y| ≤ (69/256 : ℝ) := by
  rw [polynomial24]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error24 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded24 rnd h y - exact24 h y| ≤ (61095616372126034952193/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded24 exact24
  apply rounded_step rnd hrnd (propagation := (81460821829501379936257/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (69/256 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error23 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound24 h y hh hy
  · norm_num
  · norm_num
def exact25 (h y : ℝ) : ℝ := (-243/128 : ℝ)
def rounded25 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-243/128 : ℝ)
theorem polynomial25 (h y : ℝ) : exact25 h y = evaluate [((-243/128 : ℝ), 0, 0)] h y := by
  simp only [exact25, evaluate] <;> ring
theorem bound25 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact25 h y| ≤ (243/128 : ℝ) := by
  rw [polynomial25]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error25 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded25 rnd h y - exact25 h y| ≤ (0/1 : ℝ) := by
  simp [rounded25, exact25]
def exact26 (h y : ℝ) : ℝ := exact25 h y * exact11 h y
def rounded26 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded25 rnd h y * rounded11 rnd h y)
theorem polynomial26 (h y : ℝ) : exact26 h y = evaluate [((-243/128 : ℝ), 0, 1), ((-486388759756013541/1152921504606846976 : ℝ), 1, 1)] h y := by
  simp only [exact26, polynomial25, polynomial11, evaluate] <;> ring
theorem bound26 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact26 h y| ≤ (1971/2048 : ℝ) := by
  rw [polynomial26]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error26 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded26 rnd h y - exact26 h y| ≤ (366573698233225501999109/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded26 exact26
  apply rounded_step rnd hrnd (propagation := (75227298072233587079382207/200867255532373784442745261542645325315275374222849104412672 : ℝ)) (magnitude := (1971/2048 : ℝ))
  · convert FindOrb.mul_error (bound25 h y hh hy) (bound11 h y hh hy)
      (error25 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound26 h y hh hy
  · norm_num
  · norm_num
def exact27 (h y : ℝ) : ℝ := exact24 h y + exact26 h y
def rounded27 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded24 rnd h y + rounded26 rnd h y)
theorem polynomial27 (h y : ℝ) : exact27 h y = evaluate [((-87/64 : ℝ), 0, 1), ((-486388759756013541/1152921504606846976 : ℝ), 1, 1)] h y := by
  simp only [exact27, polynomial24, polynomial26, evaluate] <;> ring
theorem bound27 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact27 h y| ≤ (1419/2048 : ℝ) := by
  rw [polynomial27]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error27 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded27 rnd h y - exact27 h y| ≤ (960042348573078488875021/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded27 exact27
  apply rounded_step rnd hrnd (propagation := (213834657302675768475651/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (1419/2048 : ℝ))
  · convert FindOrb.add_error (error24 rnd hrnd h y hh hy) (error26 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound27 h y hh hy
  · norm_num
  · norm_num
def exact28 (h y : ℝ) : ℝ := (135/64 : ℝ)
def rounded28 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (135/64 : ℝ)
theorem polynomial28 (h y : ℝ) : exact28 h y = evaluate [((135/64 : ℝ), 0, 0)] h y := by
  simp only [exact28, evaluate] <;> ring
theorem bound28 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact28 h y| ≤ (135/64 : ℝ) := by
  rw [polynomial28]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error28 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded28 rnd h y - exact28 h y| ≤ (0/1 : ℝ) := by
  simp [rounded28, exact28]
def exact29 (h y : ℝ) : ℝ := exact28 h y * exact21 h y
def rounded29 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded28 rnd h y * rounded21 rnd h y)
theorem polynomial29 (h y : ℝ) : exact29 h y = evaluate [((135/64 : ℝ), 0, 1), ((3242591731706757075/4611686018427387904 : ℝ), 1, 1), ((270215977642229745/2305843009213693952 : ℝ), 2, 1)] h y := by
  simp only [exact29, polynomial28, polynomial21, evaluate] <;> ring
theorem bound29 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact29 h y| ≤ (70575/65536 : ℝ) := by
  rw [polynomial29]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error29 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded29 rnd h y - exact29 h y| ≤ (832247917315804763258891/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded29 exact29
  apply rounded_step rnd hrnd (propagation := (42848835004195092006175395/100433627766186892221372630771322662657637687111424552206336 : ℝ)) (magnitude := (70575/65536 : ℝ))
  · convert FindOrb.mul_error (bound28 h y hh hy) (bound21 h y hh hy)
      (error28 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound29 h y hh hy
  · norm_num
  · norm_num
def exact30 (h y : ℝ) : ℝ := exact27 h y + exact29 h y
def rounded30 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded27 rnd h y + rounded29 rnd h y)
theorem polynomial30 (h y : ℝ) : exact30 h y = evaluate [((3/4 : ℝ), 0, 1), ((1297036692682702911/4611686018427387904 : ℝ), 1, 1), ((270215977642229745/2305843009213693952 : ℝ), 2, 1)] h y := by
  simp only [exact30, polynomial27, polynomial29, evaluate] <;> ring
theorem bound30 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact30 h y| ≤ (422232195073/1099511627776 : ℝ) := by
  rw [polynomial30]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error30 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded30 rnd h y - exact30 h y| ≤ (1850321416901901726777369/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded30 exact30
  apply rounded_step rnd hrnd (propagation := (224036283236110406516739/196159429230833773869868419475239575503198607639501078528 : ℝ)) (magnitude := (422232195073/1099511627776 : ℝ))
  · convert FindOrb.add_error (error27 rnd hrnd h y hh hy) (error29 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound30 h y hh hy
  · norm_num
  · norm_num
def exact31 (h y : ℝ) : ℝ := exact30 h y * exact0 h y
def rounded31 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded30 rnd h y * rounded0 rnd h y)
theorem polynomial31 (h y : ℝ) : exact31 h y = evaluate [((3/4 : ℝ), 1, 1), ((1297036692682702911/4611686018427387904 : ℝ), 2, 1), ((270215977642229745/2305843009213693952 : ℝ), 3, 1)] h y := by
  simp only [exact31, polynomial30, polynomial0, evaluate] <;> ring
theorem bound31 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact31 h y| ≤ (26389512193/1099511627776 : ℝ) := by
  rw [polynomial31]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error31 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded31 rnd h y - exact31 h y| ≤ (59636017747405680803841/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded31 exact31
  apply rounded_step rnd hrnd (propagation := (1850321416901901726777369/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (26389512193/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound30 h y hh hy) (bound0 h y hh hy)
      (error30 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound31 h y hh hy
  · norm_num
  · norm_num
def exact32 (h y : ℝ) : ℝ := exact31 h y + exact3 h y
def rounded32 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded31 rnd h y + rounded3 rnd h y)
theorem polynomial32 (h y : ℝ) : exact32 h y = evaluate [((1/1 : ℝ), 0, 1), ((3/4 : ℝ), 1, 1), ((1297036692682702911/4611686018427387904 : ℝ), 2, 1), ((270215977642229745/2305843009213693952 : ℝ), 3, 1)] h y := by
  simp only [exact32, polynomial31, polynomial3, evaluate] <;> ring
theorem bound32 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact32 h y| ≤ (576145326081/1099511627776 : ℝ) := by
  rw [polynomial32]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error32 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded32 rnd h y - exact32 h y| ≤ (68503677471270628032513/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded32 exact32
  apply rounded_step rnd hrnd (propagation := (194829899220725685026819/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (576145326081/1099511627776 : ℝ))
  · convert FindOrb.add_error (error31 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound32 h y hh hy
  · norm_num
  · norm_num
def exact33 (h y : ℝ) : ℝ := exact32 h y + exact2 h y
def rounded33 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded32 rnd h y + rounded2 rnd h y)
theorem polynomial33 (h y : ℝ) : exact33 h y = evaluate [((1/1 : ℝ), 0, 1), ((3/4 : ℝ), 1, 1), ((1297036692682702911/4611686018427387904 : ℝ), 2, 1), ((270215977642229745/2305843009213693952 : ℝ), 3, 1)] h y := by
  simp only [exact33, polynomial32, polynomial2, evaluate] <;> ring
theorem bound33 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact33 h y| ≤ (576145326081/1099511627776 : ℝ) := by
  rw [polynomial33]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error33 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded33 rnd h y - exact33 h y| ≤ (353199520549439339233285/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded33 exact33
  apply rounded_step rnd hrnd (propagation := (68503677471270628032513/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (576145326081/1099511627776 : ℝ))
  · convert FindOrb.add_error (error32 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound33 h y hh hy
  · norm_num
  · norm_num
def exact34 (h y : ℝ) : ℝ := exact33 h y + exact2 h y
def rounded34 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded33 rnd h y + rounded2 rnd h y)
theorem polynomial34 (h y : ℝ) : exact34 h y = evaluate [((1/1 : ℝ), 0, 1), ((3/4 : ℝ), 1, 1), ((1297036692682702911/4611686018427387904 : ℝ), 2, 1), ((270215977642229745/2305843009213693952 : ℝ), 3, 1)] h y := by
  simp only [exact34, polynomial33, polynomial2, evaluate] <;> ring
theorem bound34 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact34 h y| ≤ (576145326081/1099511627776 : ℝ) := by
  rw [polynomial34]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error34 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded34 rnd h y - exact34 h y| ≤ (216192165606898083168259/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded34 exact34
  apply rounded_step rnd hrnd (propagation := (353199520549439339233285/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (576145326081/1099511627776 : ℝ))
  · convert FindOrb.add_error (error33 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound34 h y hh hy
  · norm_num
  · norm_num
def exact35 (h y : ℝ) : ℝ := (-6380099472108203/4503599627370496 : ℝ)
def rounded35 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-6380099472108203/4503599627370496 : ℝ)
theorem polynomial35 (h y : ℝ) : exact35 h y = evaluate [((-6380099472108203/4503599627370496 : ℝ), 0, 0)] h y := by
  simp only [exact35, evaluate] <;> ring
theorem bound35 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact35 h y| ≤ (1557641472683/1099511627776 : ℝ) := by
  rw [polynomial35]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error35 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded35 rnd h y - exact35 h y| ≤ (0/1 : ℝ) := by
  simp [rounded35, exact35]
def exact36 (h y : ℝ) : ℝ := exact35 h y * exact4 h y
def rounded36 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded35 rnd h y * rounded4 rnd h y)
theorem polynomial36 (h y : ℝ) : exact36 h y = evaluate [((-6380099472108203/4503599627370496 : ℝ), 0, 1)] h y := by
  simp only [exact36, polynomial35, polynomial4, evaluate] <;> ring
theorem bound36 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact36 h y| ≤ (389410368171/549755813888 : ℝ) := by
  rw [polynomial36]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error36 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded36 rnd h y - exact36 h y| ≤ (107040306945102557741057/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded36 exact36
  apply rounded_step rnd hrnd (propagation := (117692062126814612201268112544934571/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (389410368171/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound35 h y hh hy) (bound4 h y hh hy)
      (error35 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound36 h y hh hy
  · norm_num
  · norm_num
def exact37 (h y : ℝ) : ℝ := exact2 h y + exact36 h y
def rounded37 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded36 rnd h y)
theorem polynomial37 (h y : ℝ) : exact37 h y = evaluate [((-6380099472108203/4503599627370496 : ℝ), 0, 1)] h y := by
  simp only [exact37, polynomial2, polynomial36, evaluate] <;> ring
theorem bound37 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact37 h y| ≤ (389410368171/549755813888 : ℝ) := by
  rw [polynomial37]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error37 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded37 rnd h y - exact37 h y| ≤ (321120920835342032961539/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded37 exact37
  apply rounded_step rnd hrnd (propagation := (107040306945102557741057/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (389410368171/549755813888 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error36 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound37 h y hh hy
  · norm_num
  · norm_num
def exact38 (h y : ℝ) : ℝ := (27/4 : ℝ)
def rounded38 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (27/4 : ℝ)
theorem polynomial38 (h y : ℝ) : exact38 h y = evaluate [((27/4 : ℝ), 0, 0)] h y := by
  simp only [exact38, evaluate] <;> ring
theorem bound38 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact38 h y| ≤ (27/4 : ℝ) := by
  rw [polynomial38]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error38 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded38 rnd h y - exact38 h y| ≤ (0/1 : ℝ) := by
  simp [rounded38, exact38]
def exact39 (h y : ℝ) : ℝ := exact38 h y * exact11 h y
def rounded39 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded38 rnd h y * rounded11 rnd h y)
theorem polynomial39 (h y : ℝ) : exact39 h y = evaluate [((27/4 : ℝ), 0, 1), ((54043195528445949/36028797018963968 : ℝ), 1, 1)] h y := by
  simp only [exact39, polynomial38, polynomial11, evaluate] <;> ring
theorem bound39 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact39 h y| ≤ (219/64 : ℝ) := by
  rw [polynomial39]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error39 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded39 rnd h y - exact39 h y| ≤ (1303373149273690673774609/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded39 exact39
  apply rounded_step rnd hrnd (propagation := (8358588674692620786598023/6277101735386680763835789423207666416102355444464034512896 : ℝ)) (magnitude := (219/64 : ℝ))
  · convert FindOrb.mul_error (bound38 h y hh hy) (bound11 h y hh hy)
      (error38 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound39 h y hh hy
  · norm_num
  · norm_num
def exact40 (h y : ℝ) : ℝ := exact37 h y + exact39 h y
def rounded40 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded37 rnd h y + rounded39 rnd h y)
theorem polynomial40 (h y : ℝ) : exact40 h y = evaluate [((24019198012642645/4503599627370496 : ℝ), 0, 1), ((54043195528445949/36028797018963968 : ℝ), 1, 1)] h y := by
  simp only [exact40, polynomial37, polynomial39, evaluate] <;> ring
theorem bound40 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact40 h y| ≤ (2983570614955/1099511627776 : ℝ) := by
  rw [polynomial40]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error40 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded40 rnd h y - exact40 h y| ≤ (1668963021155975026442259/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded40 exact40
  apply rounded_step rnd hrnd (propagation := (2927867219382723380510757/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (2983570614955/1099511627776 : ℝ))
  · convert FindOrb.add_error (error37 rnd hrnd h y hh hy) (error39 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound40 h y hh hy
  · norm_num
  · norm_num
def exact41 (h y : ℝ) : ℝ := (-3039929748475085/562949953421312 : ℝ)
def rounded41 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-3039929748475085/562949953421312 : ℝ)
theorem polynomial41 (h y : ℝ) : exact41 h y = evaluate [((-3039929748475085/562949953421312 : ℝ), 0, 0)] h y := by
  simp only [exact41, evaluate] <;> ring
theorem bound41 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact41 h y| ≤ (5937362789991/1099511627776 : ℝ) := by
  rw [polynomial41]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error41 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded41 rnd h y - exact41 h y| ≤ (0/1 : ℝ) := by
  simp [rounded41, exact41]
def exact42 (h y : ℝ) : ℝ := exact41 h y * exact21 h y
def rounded42 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded41 rnd h y * rounded21 rnd h y)
theorem polynomial42 (h y : ℝ) : exact42 h y = evaluate [((-3039929748475085/562949953421312 : ℝ), 0, 1), ((-73016674573146017316739790999825/40564819207303340847894502572032 : ℝ), 1, 1), ((-6084722881095501189734170210395/20282409603651670423947251286016 : ℝ), 2, 1)] h y := by
  simp only [exact42, polynomial41, polynomial21, evaluate] <;> ring
theorem bound42 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact42 h y| ≤ (3031173169153/1099511627776 : ℝ) := by
  rw [polynomial42]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error42 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded42 rnd h y - exact42 h y| ≤ (532638667082192709100073/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded42 exact42
  apply rounded_step rnd hrnd (propagation := (1884511692950902175281885071544418307/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (3031173169153/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound41 h y hh hy) (bound21 h y hh hy)
      (error41 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound42 h y hh hy
  · norm_num
  · norm_num
def exact43 (h y : ℝ) : ℝ := exact40 h y + exact42 h y
def rounded43 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded40 rnd h y + rounded42 rnd h y)
theorem polynomial43 (h y : ℝ) : exact43 h y = evaluate [((-300239975158035/4503599627370496 : ℝ), 0, 1), ((-12169445762191009422597757669649/40564819207303340847894502572032 : ℝ), 1, 1), ((-6084722881095501189734170210395/20282409603651670423947251286016 : ℝ), 2, 1)] h y := by
  simp only [exact43, polynomial40, polynomial42, evaluate] <;> ring
theorem bound43 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact43 h y| ≤ (23801277099/549755813888 : ℝ) := by
  rw [polynomial43]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error43 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded43 rnd h y - exact43 h y| ≤ (5475023155872288169560267/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded43 exact43
  apply rounded_step rnd hrnd (propagation := (2734240355320360444642405/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (23801277099/549755813888 : ℝ))
  · convert FindOrb.add_error (error40 rnd hrnd h y hh hy) (error42 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound43 h y hh hy
  · norm_num
  · norm_num
def exact44 (h y : ℝ) : ℝ := (4803839602528529/4503599627370496 : ℝ)
def rounded44 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (4803839602528529/4503599627370496 : ℝ)
theorem polynomial44 (h y : ℝ) : exact44 h y = evaluate [((4803839602528529/4503599627370496 : ℝ), 0, 0)] h y := by
  simp only [exact44, evaluate] <;> ring
theorem bound44 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact44 h y| ≤ (586406201481/549755813888 : ℝ) := by
  rw [polynomial44]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error44 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded44 rnd h y - exact44 h y| ≤ (0/1 : ℝ) := by
  simp [rounded44, exact44]
def exact45 (h y : ℝ) : ℝ := exact44 h y * exact34 h y
def rounded45 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded44 rnd h y * rounded34 rnd h y)
theorem polynomial45 (h y : ℝ) : exact45 h y = evaluate [((4803839602528529/4503599627370496 : ℝ), 0, 1), ((14411518807585587/18014398509481984 : ℝ), 1, 1), ((6230756230241793370409377708847919/20769187434139310514121985316880384 : ℝ), 2, 1), ((1298074214633706817060631534895105/10384593717069655257060992658440192 : ℝ), 3, 1)] h y := by
  simp only [exact45, polynomial44, polynomial34, evaluate] <;> ring
theorem bound45 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact45 h y| ≤ (307277507243/549755813888 : ℝ) := by
  rw [polynomial45]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error45 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded45 rnd h y - exact45 h y| ≤ (136418437834252146315539/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded45 exact45
  apply rounded_step rnd hrnd (propagation := (126776426623492396001798781977991579/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (307277507243/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound44 h y hh hy) (bound34 h y hh hy)
      (error44 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound45 h y hh hy
  · norm_num
  · norm_num
def exact46 (h y : ℝ) : ℝ := exact43 h y + exact45 h y
def rounded46 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded43 rnd h y + rounded45 rnd h y)
theorem polynomial46 (h y : ℝ) : exact46 h y = evaluate [((2251799813685247/2251799813685248 : ℝ), 0, 1), ((20282409603651662805357881650927/40564819207303340847894502572032 : ℝ), 1, 1), ((152121587413403439/20769187434139310514121985316880384 : ℝ), 2, 1), ((1298074214633706817060631534895105/10384593717069655257060992658440192 : ℝ), 3, 1)] h y := by
  simp only [exact46, polynomial43, polynomial45, evaluate] <;> ring
theorem bound46 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact46 h y| ≤ (33793/65536 : ℝ) := by
  rw [polynomial46]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error46 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded46 rnd h y - exact46 h y| ≤ (762327282502456889317795/196159429230833773869868419475239575503198607639501078528 : ℝ) := by
  unfold rounded46 exact46
  apply rounded_step rnd hrnd (propagation := (6020696907209296754822423/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (33793/65536 : ℝ))
  · convert FindOrb.add_error (error43 rnd hrnd h y hh hy) (error45 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound46 h y hh hy
  · norm_num
  · norm_num
def exact47 (h y : ℝ) : ℝ := exact46 h y * exact0 h y
def rounded47 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded46 rnd h y * rounded0 rnd h y)
theorem polynomial47 (h y : ℝ) : exact47 h y = evaluate [((2251799813685247/2251799813685248 : ℝ), 1, 1), ((20282409603651662805357881650927/40564819207303340847894502572032 : ℝ), 2, 1), ((152121587413403439/20769187434139310514121985316880384 : ℝ), 3, 1), ((1298074214633706817060631534895105/10384593717069655257060992658440192 : ℝ), 4, 1)] h y := by
  simp only [exact47, polynomial46, polynomial0, evaluate] <;> ring
theorem bound47 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact47 h y| ≤ (33793/1048576 : ℝ) := by
  rw [polynomial47]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error47 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded47 rnd h y - exact47 h y| ≤ (193016862900937921070697/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded47 exact47
  apply rounded_step rnd hrnd (propagation := (762327282502456889317795/3138550867693340381917894711603833208051177722232017256448 : ℝ)) (magnitude := (33793/1048576 : ℝ))
  · convert FindOrb.mul_error (bound46 h y hh hy) (bound0 h y hh hy)
      (error46 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound47 h y hh hy
  · norm_num
  · norm_num
def exact48 (h y : ℝ) : ℝ := exact47 h y + exact3 h y
def rounded48 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded47 rnd h y + rounded3 rnd h y)
theorem polynomial48 (h y : ℝ) : exact48 h y = evaluate [((1/1 : ℝ), 0, 1), ((2251799813685247/2251799813685248 : ℝ), 1, 1), ((20282409603651662805357881650927/40564819207303340847894502572032 : ℝ), 2, 1), ((152121587413403439/20769187434139310514121985316880384 : ℝ), 3, 1), ((1298074214633706817060631534895105/10384593717069655257060992658440192 : ℝ), 4, 1)] h y := by
  simp only [exact48, polynomial47, polynomial3, evaluate] <;> ring
theorem bound48 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact48 h y| ≤ (558081/1048576 : ℝ) := by
  rw [polynomial48]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error48 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded48 rnd h y - exact48 h y| ≤ (135504884451087971615541/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded48 exact48
  apply rounded_step rnd hrnd (propagation := (461591589527790165560531/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (558081/1048576 : ℝ))
  · convert FindOrb.add_error (error47 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound48 h y hh hy
  · norm_num
  · norm_num
def exact49 (h y : ℝ) : ℝ := exact48 h y + exact2 h y
def rounded49 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded48 rnd h y + rounded2 rnd h y)
theorem polynomial49 (h y : ℝ) : exact49 h y = evaluate [((1/1 : ℝ), 0, 1), ((2251799813685247/2251799813685248 : ℝ), 1, 1), ((20282409603651662805357881650927/40564819207303340847894502572032 : ℝ), 2, 1), ((152121587413403439/20769187434139310514121985316880384 : ℝ), 3, 1), ((1298074214633706817060631534895105/10384593717069655257060992658440192 : ℝ), 4, 1)] h y := by
  simp only [exact49, polynomial48, polynomial2, evaluate] <;> ring
theorem bound49 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact49 h y| ≤ (558081/1048576 : ℝ) := by
  rw [polynomial49]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error49 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded49 rnd h y - exact49 h y| ≤ (622447486080913607363797/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded49 exact49
  apply rounded_step rnd hrnd (propagation := (135504884451087971615541/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (558081/1048576 : ℝ))
  · convert FindOrb.add_error (error48 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound49 h y hh hy
  · norm_num
  · norm_num
def exact50 (h y : ℝ) : ℝ := exact49 h y + exact2 h y
def rounded50 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded49 rnd h y + rounded2 rnd h y)
theorem polynomial50 (h y : ℝ) : exact50 h y = evaluate [((1/1 : ℝ), 0, 1), ((2251799813685247/2251799813685248 : ℝ), 1, 1), ((20282409603651662805357881650927/40564819207303340847894502572032 : ℝ), 2, 1), ((152121587413403439/20769187434139310514121985316880384 : ℝ), 3, 1), ((1298074214633706817060631534895105/10384593717069655257060992658440192 : ℝ), 4, 1)] h y := by
  simp only [exact50, polynomial49, polynomial2, evaluate] <;> ring
theorem bound50 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact50 h y| ≤ (558081/1048576 : ℝ) := by
  rw [polynomial50]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error50 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded50 rnd h y - exact50 h y| ≤ (351437717178737664132715/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded50 exact50
  apply rounded_step rnd hrnd (propagation := (622447486080913607363797/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (558081/1048576 : ℝ))
  · convert FindOrb.add_error (error49 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound50 h y hh hy
  · norm_num
  · norm_num
def exact51 (h y : ℝ) : ℝ := (2710499775732243/18014398509481984 : ℝ)
def rounded51 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (2710499775732243/18014398509481984 : ℝ)
theorem polynomial51 (h y : ℝ) : exact51 h y = evaluate [((2710499775732243/18014398509481984 : ℝ), 0, 0)] h y := by
  simp only [exact51, evaluate] <;> ring
theorem bound51 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact51 h y| ≤ (10339736083/68719476736 : ℝ) := by
  rw [polynomial51]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error51 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded51 rnd h y - exact51 h y| ≤ (0/1 : ℝ) := by
  simp [rounded51, exact51]
def exact52 (h y : ℝ) : ℝ := exact51 h y * exact4 h y
def rounded52 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded51 rnd h y * rounded4 rnd h y)
theorem polynomial52 (h y : ℝ) : exact52 h y = evaluate [((2710499775732243/18014398509481984 : ℝ), 0, 1)] h y := by
  simp only [exact52, polynomial51, polynomial4, evaluate] <;> ring
theorem bound52 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact52 h y| ≤ (10339736083/137438953472 : ℝ) := by
  rw [polynomial52]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error52 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded52 rnd h y - exact52 h y| ≤ (22737320102787144482817/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded52 exact52
  apply rounded_step rnd hrnd (propagation := (781248369921233152023382771620371/107839786668602559178668060348078522694548577690162289924414440996864 : ℝ)) (magnitude := (10339736083/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound51 h y hh hy) (bound4 h y hh hy)
      (error51 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound52 h y hh hy
  · norm_num
  · norm_num
def exact53 (h y : ℝ) : ℝ := exact2 h y + exact52 h y
def rounded53 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded52 rnd h y)
theorem polynomial53 (h y : ℝ) : exact53 h y = evaluate [((2710499775732243/18014398509481984 : ℝ), 0, 1)] h y := by
  simp only [exact53, polynomial2, polynomial52, evaluate] <;> ring
theorem bound53 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact53 h y| ≤ (10339736083/137438953472 : ℝ) := by
  rw [polynomial53]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error53 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded53 rnd h y - exact53 h y| ≤ (17052990077090358362113/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded53 exact53
  apply rounded_step rnd hrnd (propagation := (22737320102787144482817/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (10339736083/137438953472 : ℝ))
  · convert FindOrb.add_error (error2 rnd hrnd h y hh hy) (error52 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound53 h y hh hy
  · norm_num
  · norm_num
def exact54 (h y : ℝ) : ℝ := (-5/16 : ℝ)
def rounded54 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (-5/16 : ℝ)
theorem polynomial54 (h y : ℝ) : exact54 h y = evaluate [((-5/16 : ℝ), 0, 0)] h y := by
  simp only [exact54, evaluate] <;> ring
theorem bound54 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact54 h y| ≤ (5/16 : ℝ) := by
  rw [polynomial54]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error54 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded54 rnd h y - exact54 h y| ≤ (0/1 : ℝ) := by
  simp [rounded54, exact54]
def exact55 (h y : ℝ) : ℝ := exact54 h y * exact11 h y
def rounded55 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded54 rnd h y * rounded11 rnd h y)
theorem polynomial55 (h y : ℝ) : exact55 h y = evaluate [((-5/16 : ℝ), 0, 1), ((-10007999171934435/144115188075855872 : ℝ), 1, 1)] h y := by
  simp only [exact55, polynomial54, polynomial11, evaluate] <;> ring
theorem bound55 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact55 h y| ≤ (174184784783/1099511627776 : ℝ) := by
  rw [polynomial55]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error55 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded55 rnd h y - exact55 h y| ≤ (60341349503465053749249/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded55 exact55
  apply rounded_step rnd hrnd (propagation := (1547886791609744590110745/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (174184784783/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound54 h y hh hy) (bound11 h y hh hy)
      (error54 rnd hrnd h y hh hy) (error11 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound55 h y hh hy
  · norm_num
  · norm_num
def exact56 (h y : ℝ) : ℝ := exact53 h y + exact55 h y
def rounded56 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded53 rnd h y + rounded55 rnd h y)
theorem polynomial56 (h y : ℝ) : exact56 h y = evaluate [((-2918999758480877/18014398509481984 : ℝ), 0, 1), ((-10007999171934435/144115188075855872 : ℝ), 1, 1)] h y := by
  simp only [exact56, polynomial53, polynomial55, evaluate] <;> ring
theorem bound56 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact56 h y| ≤ (91466896119/1099511627776 : ℝ) := by
  rw [polynomial56]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error56 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded56 rnd h y - exact56 h y| ≤ (167359793641038322597893/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded56 exact56
  apply rounded_step rnd hrnd (propagation := (38697169790277706055681/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (91466896119/1099511627776 : ℝ))
  · convert FindOrb.add_error (error53 rnd hrnd h y hh hy) (error55 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound56 h y hh hy
  · norm_num
  · norm_num
def exact57 (h y : ℝ) : ℝ := (13/16 : ℝ)
def rounded57 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (13/16 : ℝ)
theorem polynomial57 (h y : ℝ) : exact57 h y = evaluate [((13/16 : ℝ), 0, 0)] h y := by
  simp only [exact57, evaluate] <;> ring
theorem bound57 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact57 h y| ≤ (13/16 : ℝ) := by
  rw [polynomial57]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error57 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded57 rnd h y - exact57 h y| ≤ (0/1 : ℝ) := by
  simp [rounded57, exact57]
def exact58 (h y : ℝ) : ℝ := exact57 h y * exact21 h y
def rounded58 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded57 rnd h y * rounded21 rnd h y)
theorem polynomial58 (h y : ℝ) : exact58 h y = evaluate [((13/16 : ℝ), 0, 1), ((312249574164354385/1152921504606846976 : ℝ), 1, 1), ((26020797847029531/576460752303423488 : ℝ), 2, 1)] h y := by
  simp only [exact58, polynomial57, polynomial21, evaluate] <;> ring
theorem bound58 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact58 h y| ≤ (456079296285/1099511627776 : ℝ) := by
  rw [polynomial58]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error58 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded58 rnd h y - exact58 h y| ≤ (320569568151349300822021/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded58 exact58
  apply rounded_step rnd hrnd (propagation := (4126184111515082933928001/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (456079296285/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound57 h y hh hy) (bound21 h y hh hy)
      (error57 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound58 h y hh hy
  · norm_num
  · norm_num
def exact59 (h y : ℝ) : ℝ := exact56 h y + exact58 h y
def rounded59 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded56 rnd h y + rounded58 rnd h y)
theorem polynomial59 (h y : ℝ) : exact59 h y = evaluate [((11717699030473235/18014398509481984 : ℝ), 0, 1), ((232185580788878905/1152921504606846976 : ℝ), 1, 1), ((26020797847029531/576460752303423488 : ℝ), 2, 1)] h y := by
  simp only [exact59, polynomial56, polynomial58, evaluate] <;> ring
theorem bound59 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact59 h y| ≤ (182306200083/549755813888 : ℝ) := by
  rw [polynomial59]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error59 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded59 rnd h y - exact59 h y| ≤ (538041308494116742496267/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded59 exact59
  apply rounded_step rnd hrnd (propagation := (243964680896193811709957/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (182306200083/549755813888 : ℝ))
  · convert FindOrb.add_error (error56 rnd hrnd h y hh hy) (error58 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound59 h y hh hy
  · norm_num
  · norm_num
def exact60 (h y : ℝ) : ℝ := (667199944795629/4503599627370496 : ℝ)
def rounded60 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (667199944795629/4503599627370496 : ℝ)
theorem polynomial60 (h y : ℝ) : exact60 h y = evaluate [((667199944795629/4503599627370496 : ℝ), 0, 0)] h y := by
  simp only [exact60, evaluate] <;> ring
theorem bound60 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact60 h y| ≤ (162890611523/1099511627776 : ℝ) := by
  rw [polynomial60]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error60 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded60 rnd h y - exact60 h y| ≤ (0/1 : ℝ) := by
  simp [rounded60, exact60]
def exact61 (h y : ℝ) : ℝ := exact60 h y * exact34 h y
def rounded61 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded60 rnd h y * rounded34 rnd h y)
theorem polynomial61 (h y : ℝ) : exact61 h y = evaluate [((667199944795629/4503599627370496 : ℝ), 0, 1), ((2001599834386887/18014398509481984 : ℝ), 1, 1), ((865382809755804598750283218376019/20769187434139310514121985316880384 : ℝ), 2, 1), ((180288085365792605974643889784605/10384593717069655257060992658440192 : ℝ), 3, 1)] h y := by
  simp only [exact61, polynomial60, polynomial34, evaluate] <;> ring
theorem bound61 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact61 h y| ≤ (85354863123/1099511627776 : ℝ) := by
  rw [polynomial61]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error61 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded61 rnd h y - exact61 h y| ≤ (75788021019217960307069/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded61 exact61
  apply rounded_step rnd hrnd (propagation := (35215674062189317194414221813248457/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (85354863123/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound60 h y hh hy) (bound34 h y hh hy)
      (error60 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound61 h y hh hy
  · norm_num
  · norm_num
def exact62 (h y : ℝ) : ℝ := exact59 h y + exact61 h y
def rounded62 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded59 rnd h y + rounded61 rnd h y)
theorem polynomial62 (h y : ℝ) : exact62 h y = evaluate [((14386498809655751/18014398509481984 : ℝ), 0, 1), ((360287970189639673/1152921504606846976 : ℝ), 1, 1), ((1802880853657926201860027139315027/20769187434139310514121985316880384 : ℝ), 2, 1), ((180288085365792605974643889784605/10384593717069655257060992658440192 : ℝ), 3, 1)] h y := by
  simp only [exact62, polynomial59, polynomial61, evaluate] <;> ring
theorem bound62 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact62 h y| ≤ (449967263289/1099511627776 : ℝ) := by
  rw [polynomial62]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error62 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded62 rnd h y - exact62 h y| ≤ (675672359276434747492745/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded62 exact62
  apply rounded_step rnd hrnd (propagation := (76728666189166837850417/196159429230833773869868419475239575503198607639501078528 : ℝ)) (magnitude := (449967263289/1099511627776 : ℝ))
  · convert FindOrb.add_error (error59 rnd hrnd h y hh hy) (error61 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound62 h y hh hy
  · norm_num
  · norm_num
def exact63 (h y : ℝ) : ℝ := (2501999792983609/72057594037927936 : ℝ)
def rounded63 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (2501999792983609/72057594037927936 : ℝ)
theorem polynomial63 (h y : ℝ) : exact63 h y = evaluate [((2501999792983609/72057594037927936 : ℝ), 0, 0)] h y := by
  simp only [exact63, evaluate] <;> ring
theorem bound63 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact63 h y| ≤ (9544371769/274877906944 : ℝ) := by
  rw [polynomial63]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error63 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded63 rnd h y - exact63 h y| ≤ (0/1 : ℝ) := by
  simp [rounded63, exact63]
def exact64 (h y : ℝ) : ℝ := exact63 h y * exact50 h y
def rounded64 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded63 rnd h y * rounded50 rnd h y)
theorem polynomial64 (h y : ℝ) : exact64 h y = evaluate [((2501999792983609/72057594037927936 : ℝ), 0, 1), ((5634002667681017310407756116423/162259276829213363391578010288128 : ℝ), 1, 1), ((50746584629545223407297764776495231219970655543/2923003274661805836407369665432566039311865085952 : ℝ), 2, 1), ((380608180216673384864195031231351/1496577676626844588240573268701473812127674924007424 : ℝ), 3, 1), ((3247781416290895292656327880318384175224799333945/748288838313422294120286634350736906063837462003712 : ℝ), 4, 1)] h y := by
  simp only [exact64, polynomial63, polynomial50, evaluate] <;> ring
theorem bound64 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact64 h y| ≤ (20319109121/1099511627776 : ℝ) := by
  rw [polynomial64]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error64 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded64 rnd h y - exact64 h y| ≤ (27198034119658952708909/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded64 exact64
  apply rounded_step rnd hrnd (propagation := (3354252226402550088605288915322835/215679573337205118357336120696157045389097155380324579848828881993728 : ℝ)) (magnitude := (20319109121/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound63 h y hh hy) (bound50 h y hh hy)
      (error63 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound64 h y hh hy
  · norm_num
  · norm_num
def exact65 (h y : ℝ) : ℝ := exact62 h y + exact64 h y
def rounded65 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded62 rnd h y + rounded64 rnd h y)
theorem polynomial65 (h y : ℝ) : exact65 h y = evaluate [((60047995031606613/72057594037927936 : ℝ), 0, 1), ((56340026676810192385113465844167/162259276829213363391578010288128 : ℝ), 1, 1), ((304479507777271416315022513430037895210676569399/2923003274661805836407369665432566039311865085952 : ℝ), 2, 1), ((25982251330327160486286544723392036094018135681911/1496577676626844588240573268701473812127674924007424 : ℝ), 3, 1), ((3247781416290895292656327880318384175224799333945/748288838313422294120286634350736906063837462003712 : ℝ), 4, 1)] h y := by
  simp only [exact65, polynomial62, polynomial64, evaluate] <;> ring
theorem bound65 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact65 h y| ≤ (470286372409/1099511627776 : ℝ) := by
  rw [polynomial65]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error65 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded65 rnd h y - exact65 h y| ≤ (767506060252129915755703/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded65 exact65
  apply rounded_step rnd hrnd (propagation := (351435196698046850100827/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (470286372409/1099511627776 : ℝ))
  · convert FindOrb.add_error (error62 rnd hrnd h y hh hy) (error64 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound65 h y hh hy
  · norm_num
  · norm_num
def exact66 (h y : ℝ) : ℝ := exact65 h y * exact0 h y
def rounded66 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded65 rnd h y * rounded0 rnd h y)
theorem polynomial66 (h y : ℝ) : exact66 h y = evaluate [((60047995031606613/72057594037927936 : ℝ), 1, 1), ((56340026676810192385113465844167/162259276829213363391578010288128 : ℝ), 2, 1), ((304479507777271416315022513430037895210676569399/2923003274661805836407369665432566039311865085952 : ℝ), 3, 1), ((25982251330327160486286544723392036094018135681911/1496577676626844588240573268701473812127674924007424 : ℝ), 4, 1), ((3247781416290895292656327880318384175224799333945/748288838313422294120286634350736906063837462003712 : ℝ), 5, 1)] h y := by
  simp only [exact66, polynomial65, polynomial0, evaluate] <;> ring
theorem bound66 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact66 h y| ≤ (7348224569/274877906944 : ℝ) := by
  rw [polynomial66]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error66 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded66 rnd h y - exact66 h y| ≤ (13002214486080128187251/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded66 exact66
  apply rounded_step rnd hrnd (propagation := (767506060252129915755703/25108406941546723055343157692830665664409421777856138051584 : ℝ)) (magnitude := (7348224569/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound65 h y hh hy) (bound0 h y hh hy)
      (error65 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound66 h y hh hy
  · norm_num
  · norm_num
def exact67 (h y : ℝ) : ℝ := exact66 h y + exact3 h y
def rounded67 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded66 rnd h y + rounded3 rnd h y)
theorem polynomial67 (h y : ℝ) : exact67 h y = evaluate [((1/1 : ℝ), 0, 1), ((60047995031606613/72057594037927936 : ℝ), 1, 1), ((56340026676810192385113465844167/162259276829213363391578010288128 : ℝ), 2, 1), ((304479507777271416315022513430037895210676569399/2923003274661805836407369665432566039311865085952 : ℝ), 3, 1), ((25982251330327160486286544723392036094018135681911/1496577676626844588240573268701473812127674924007424 : ℝ), 4, 1), ((3247781416290895292656327880318384175224799333945/748288838313422294120286634350736906063837462003712 : ℝ), 5, 1)] h y := by
  simp only [exact67, polynomial66, polynomial3, evaluate] <;> ring
theorem bound67 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact67 h y| ≤ (144787178041/274877906944 : ℝ) := by
  rw [polynomial67]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error67 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded67 rnd h y - exact67 h y| ≤ (103582157287355776300775/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded67 exact67
  apply rounded_step rnd hrnd (propagation := (127566721670234836168141/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (144787178041/274877906944 : ℝ))
  · convert FindOrb.add_error (error66 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound67 h y hh hy
  · norm_num
  · norm_num
def exact68 (h y : ℝ) : ℝ := exact67 h y + exact2 h y
def rounded68 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded67 rnd h y + rounded2 rnd h y)
theorem polynomial68 (h y : ℝ) : exact68 h y = evaluate [((1/1 : ℝ), 0, 1), ((60047995031606613/72057594037927936 : ℝ), 1, 1), ((56340026676810192385113465844167/162259276829213363391578010288128 : ℝ), 2, 1), ((304479507777271416315022513430037895210676569399/2923003274661805836407369665432566039311865085952 : ℝ), 3, 1), ((25982251330327160486286544723392036094018135681911/1496577676626844588240573268701473812127674924007424 : ℝ), 4, 1), ((3247781416290895292656327880318384175224799333945/748288838313422294120286634350736906063837462003712 : ℝ), 5, 1)] h y := by
  simp only [exact68, polynomial67, polynomial2, evaluate] <;> ring
theorem bound68 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact68 h y| ≤ (144787178041/274877906944 : ℝ) := by
  rw [polynomial68]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error68 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded68 rnd h y - exact68 h y| ≤ (286761907479188269034959/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded68 exact68
  apply rounded_step rnd hrnd (propagation := (103582157287355776300775/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (144787178041/274877906944 : ℝ))
  · convert FindOrb.add_error (error67 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound68 h y hh hy
  · norm_num
  · norm_num
def exact69 (h y : ℝ) : ℝ := exact68 h y + exact2 h y
def rounded69 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded68 rnd h y + rounded2 rnd h y)
theorem polynomial69 (h y : ℝ) : exact69 h y = evaluate [((1/1 : ℝ), 0, 1), ((60047995031606613/72057594037927936 : ℝ), 1, 1), ((56340026676810192385113465844167/162259276829213363391578010288128 : ℝ), 2, 1), ((304479507777271416315022513430037895210676569399/2923003274661805836407369665432566039311865085952 : ℝ), 3, 1), ((25982251330327160486286544723392036094018135681911/1496577676626844588240573268701473812127674924007424 : ℝ), 4, 1), ((3247781416290895292656327880318384175224799333945/748288838313422294120286634350736906063837462003712 : ℝ), 5, 1)] h y := by
  simp only [exact69, polynomial68, polynomial2, evaluate] <;> ring
theorem bound69 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact69 h y| ≤ (144787178041/274877906944 : ℝ) := by
  rw [polynomial69]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error69 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded69 rnd h y - exact69 h y| ≤ (22897468773979061591773/98079714615416886934934209737619787751599303819750539264 : ℝ) := by
  unfold rounded69 exact69
  apply rounded_step rnd hrnd (propagation := (286761907479188269034959/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (144787178041/274877906944 : ℝ))
  · convert FindOrb.add_error (error68 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound69 h y hh hy
  · norm_num
  · norm_num
def exact70 (h y : ℝ) : ℝ := (940751922161837/9007199254740992 : ℝ)
def rounded70 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (940751922161837/9007199254740992 : ℝ)
theorem polynomial70 (h y : ℝ) : exact70 h y = evaluate [((940751922161837/9007199254740992 : ℝ), 0, 0)] h y := by
  simp only [exact70, evaluate] <;> ring
theorem bound70 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact70 h y| ≤ (28709470281/274877906944 : ℝ) := by
  rw [polynomial70]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error70 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded70 rnd h y - exact70 h y| ≤ (0/1 : ℝ) := by
  simp [rounded70, exact70]
def exact71 (h y : ℝ) : ℝ := exact70 h y * exact4 h y
def rounded71 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded70 rnd h y * rounded4 rnd h y)
theorem polynomial71 (h y : ℝ) : exact71 h y = evaluate [((940751922161837/9007199254740992 : ℝ), 0, 1)] h y := by
  simp only [exact71, polynomial70, polynomial4, evaluate] <;> ring
theorem bound71 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact71 h y| ≤ (28709470281/549755813888 : ℝ) := by
  rw [polynomial71]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error71 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded71 rnd h y - exact71 h y| ≤ (15783198200624503062529/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded71 exact71
  apply rounded_step rnd hrnd (propagation := (2169226243134985197753936008167497/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (28709470281/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound70 h y hh hy) (bound4 h y hh hy)
      (error70 rnd hrnd h y hh hy) (error4 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound71 h y hh hy
  · norm_num
  · norm_num
def exact72 (h y : ℝ) : ℝ := exact2 h y + exact71 h y
def rounded72 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded2 rnd h y + rounded71 rnd h y)
theorem polynomial72 (h y : ℝ) : exact72 h y = evaluate [((940751922161837/9007199254740992 : ℝ), 0, 1)] h y := by
  simp only [exact72, polynomial2, polynomial71, evaluate] <;> ring
theorem bound72 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact72 h y| ≤ (28709470281/549755813888 : ℝ) := by
  rw [polynomial72]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error72 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded72 rnd h y - exact72 h y| ≤ (11837398650468377296897/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded72 exact72
  apply rounded_step rnd hrnd (propagation := (15783198200624503062529/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (28709470281/549755813888 : ℝ))
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
theorem polynomial75 (h y : ℝ) : exact75 h y = evaluate [((940751922161837/9007199254740992 : ℝ), 0, 1)] h y := by
  simp only [exact75, polynomial72, polynomial74, evaluate] <;> ring
theorem bound75 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact75 h y| ≤ (28709470281/549755813888 : ℝ) := by
  rw [polynomial75]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error75 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded75 rnd h y - exact75 h y| ≤ (7891599100312251531265/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded75 exact75
  apply rounded_step rnd hrnd (propagation := (23674797300936754593795/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (28709470281/549755813888 : ℝ))
  · convert FindOrb.add_error (error72 rnd hrnd h y hh hy) (error74 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound75 h y hh hy
  · norm_num
  · norm_num
def exact76 (h y : ℝ) : ℝ := (1080863910568919/2251799813685248 : ℝ)
def rounded76 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1080863910568919/2251799813685248 : ℝ)
theorem polynomial76 (h y : ℝ) : exact76 h y = evaluate [((1080863910568919/2251799813685248 : ℝ), 0, 0)] h y := by
  simp only [exact76, evaluate] <;> ring
theorem bound76 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact76 h y| ≤ (527765581333/1099511627776 : ℝ) := by
  rw [polynomial76]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error76 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded76 rnd h y - exact76 h y| ≤ (0/1 : ℝ) := by
  simp [rounded76, exact76]
def exact77 (h y : ℝ) : ℝ := exact76 h y * exact21 h y
def rounded77 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded76 rnd h y * rounded21 rnd h y)
theorem polynomial77 (h y : ℝ) : exact77 h y = evaluate [((1080863910568919/2251799813685248 : ℝ), 0, 1), ((25961484292674136821596590950755/162259276829213363391578010288128 : ℝ), 1, 1), ((2163457024389511311727723365153/81129638414606681695789005144064 : ℝ), 2, 1)] h y := by
  simp only [exact77, polynomial76, polynomial21, evaluate] <;> ring
theorem bound77 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact77 h y| ≤ (67359403759/274877906944 : ℝ) := by
  rw [polynomial77]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error77 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded77 rnd h y - exact77 h y| ≤ (47345659296234694332617/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded77 exact77
  apply rounded_step rnd hrnd (propagation := (167512150484672757232478359763969641/1725436586697640946858688965569256363112777243042596638790631055949824 : ℝ)) (magnitude := (67359403759/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound76 h y hh hy) (bound21 h y hh hy)
      (error76 rnd hrnd h y hh hy) (error21 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound77 h y hh hy
  · norm_num
  · norm_num
def exact78 (h y : ℝ) : ℝ := exact75 h y + exact77 h y
def rounded78 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded75 rnd h y + rounded77 rnd h y)
theorem polynomial78 (h y : ℝ) : exact78 h y = evaluate [((5264207564437513/9007199254740992 : ℝ), 0, 1), ((25961484292674136821596590950755/162259276829213363391578010288128 : ℝ), 1, 1), ((2163457024389511311727723365153/81129638414606681695789005144064 : ℝ), 2, 1)] h y := by
  simp only [exact78, polynomial75, polynomial77, evaluate] <;> ring
theorem bound78 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact78 h y| ≤ (163428277799/549755813888 : ℝ) := by
  rw [polynomial78]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error78 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded78 rnd h y - exact78 h y| ≤ (265871856523039486591785/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded78 exact78
  apply rounded_step rnd hrnd (propagation := (27618629198273472931941/196159429230833773869868419475239575503198607639501078528 : ℝ)) (magnitude := (163428277799/549755813888 : ℝ))
  · convert FindOrb.add_error (error75 rnd hrnd h y hh hy) (error77 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound78 h y hh hy
  · norm_num
  · norm_num
def exact79 (h y : ℝ) : ℝ := (5124095576030431/36028797018963968 : ℝ)
def rounded79 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (5124095576030431/36028797018963968 : ℝ)
theorem polynomial79 (h y : ℝ) : exact79 h y = evaluate [((5124095576030431/36028797018963968 : ℝ), 0, 0)] h y := by
  simp only [exact79, evaluate] <;> ring
theorem bound79 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact79 h y| ≤ (78187493531/549755813888 : ℝ) := by
  rw [polynomial79]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error79 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded79 rnd h y - exact79 h y| ≤ (0/1 : ℝ) := by
  simp [rounded79, exact79]
def exact80 (h y : ℝ) : ℝ := exact79 h y * exact34 h y
def rounded80 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded79 rnd h y * rounded34 rnd h y)
theorem polynomial80 (h y : ℝ) : exact80 h y = evaluate [((5124095576030431/36028797018963968 : ℝ), 0, 1), ((15372286728091293/144115188075855872 : ℝ), 1, 1), ((6646139978924579681572449068284641/166153499473114484112975882535043072 : ℝ), 2, 1), ((1384612495609287289545738813370095/83076749736557242056487941267521536 : ℝ), 3, 1)] h y := by
  simp only [exact80, polynomial79, polynomial34, evaluate] <;> ring
theorem bound80 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact80 h y| ≤ (81940668599/1099511627776 : ℝ) := by
  rw [polynomial80]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error80 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded80 rnd h y - exact80 h y| ≤ (72756500178544225631311/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded80 exact80
  apply rounded_step rnd hrnd (propagation := (16903523549842224566694550547032529/431359146674410236714672241392314090778194310760649159697657763987456 : ℝ)) (magnitude := (81940668599/1099511627776 : ℝ))
  · convert FindOrb.mul_error (bound79 h y hh hy) (bound34 h y hh hy)
      (error79 rnd hrnd h y hh hy) (error34 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound80 h y hh hy
  · norm_num
  · norm_num
def exact81 (h y : ℝ) : ℝ := exact78 h y + exact80 h y
def rounded81 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded78 rnd h y + rounded80 rnd h y)
theorem polynomial81 (h y : ℝ) : exact81 h y = evaluate [((26180925833780483/36028797018963968 : ℝ), 0, 1), ((43269140487790228901686246623587/162259276829213363391578010288128 : ℝ), 1, 1), ((11076899964874298847990826520117985/166153499473114484112975882535043072 : ℝ), 2, 1), ((1384612495609287289545738813370095/83076749736557242056487941267521536 : ℝ), 3, 1)] h y := by
  simp only [exact81, polynomial78, polynomial80, evaluate] <;> ring
theorem bound81 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact81 h y| ≤ (102199306049/274877906944 : ℝ) := by
  rw [polynomial81]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error81 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded81 rnd h y - exact81 h y| ≤ (394813019377340508831609/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded81 exact81
  apply rounded_step rnd hrnd (propagation := (42328544587697964027887/196159429230833773869868419475239575503198607639501078528 : ℝ)) (magnitude := (102199306049/274877906944 : ℝ))
  · convert FindOrb.add_error (error78 rnd hrnd h y hh hy) (error80 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound81 h y hh hy
  · norm_num
  · norm_num
def exact82 (h y : ℝ) : ℝ := (4803839602528529/144115188075855872 : ℝ)
def rounded82 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (4803839602528529/144115188075855872 : ℝ)
theorem polynomial82 (h y : ℝ) : exact82 h y = evaluate [((4803839602528529/144115188075855872 : ℝ), 0, 0)] h y := by
  simp only [exact82, evaluate] <;> ring
theorem bound82 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact82 h y| ≤ (36650387593/1099511627776 : ℝ) := by
  rw [polynomial82]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error82 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded82 rnd h y - exact82 h y| ≤ (0/1 : ℝ) := by
  simp [rounded82, exact82]
def exact83 (h y : ℝ) : ℝ := exact82 h y * exact50 h y
def rounded83 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded82 rnd h y * rounded50 rnd h y)
theorem polynomial83 (h y : ℝ) : exact83 h y = evaluate [((4803839602528529/144115188075855872 : ℝ), 0, 1), ((10817285121947552605478943911663/324518553658426726783156020576256 : ℝ), 1, 1), ((97433442488726823262937019348405258442136796383/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((730767706016012856345209984211231/2993155353253689176481146537402947624255349848014848 : ℝ), 3, 1), ((6235740319278518598439369432773388839454784950545/1496577676626844588240573268701473812127674924007424 : ℝ), 4, 1)] h y := by
  simp only [exact83, polynomial82, polynomial50, evaluate] <;> ring
theorem bound83 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact83 h y| ≤ (4876586189/274877906944 : ℝ) := by
  rw [polynomial83]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error83 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded83 rnd h y - exact83 h y| ≤ (26110112754876174827339/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded83 exact83
  apply rounded_step rnd hrnd (propagation := (12880328549399849848931458941404995/862718293348820473429344482784628181556388621521298319395315527974912 : ℝ)) (magnitude := (4876586189/274877906944 : ℝ))
  · convert FindOrb.mul_error (bound82 h y hh hy) (bound50 h y hh hy)
      (error82 rnd hrnd h y hh hy) (error50 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound83 h y hh hy
  · norm_num
  · norm_num
def exact84 (h y : ℝ) : ℝ := exact81 h y + exact83 h y
def rounded84 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded81 rnd h y + rounded83 rnd h y)
theorem polynomial84 (h y : ℝ) : exact84 h y = evaluate [((109527542937650461/144115188075855872 : ℝ), 0, 1), ((97355566097528010408851437158837/324518553658426726783156020576256 : ℝ), 1, 1), ((487167212443634264849531427484423028007677639903/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((49885922554228150859626016599697020364033437948191/2993155353253689176481146537402947624255349848014848 : ℝ), 3, 1), ((6235740319278518598439369432773388839454784950545/1496577676626844588240573268701473812127674924007424 : ℝ), 4, 1)] h y := by
  simp only [exact84, polynomial81, polynomial83, evaluate] <;> ring
theorem bound84 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact84 h y| ≤ (428303568951/1099511627776 : ℝ) := by
  rw [polynomial84]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error84 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded84 rnd h y - exact84 h y| ≤ (479788726417164716506821/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded84 exact84
  apply rounded_step rnd hrnd (propagation := (105230783033054170914737/392318858461667547739736838950479151006397215279002157056 : ℝ)) (magnitude := (428303568951/1099511627776 : ℝ))
  · convert FindOrb.add_error (error81 rnd hrnd h y hh hy) (error83 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound84 h y hh hy
  · norm_num
  · norm_num
def exact85 (h y : ℝ) : ℝ := (1080863910568919/4503599627370496 : ℝ)
def rounded85 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := (1080863910568919/4503599627370496 : ℝ)
theorem polynomial85 (h y : ℝ) : exact85 h y = evaluate [((1080863910568919/4503599627370496 : ℝ), 0, 0)] h y := by
  simp only [exact85, evaluate] <;> ring
theorem bound85 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact85 h y| ≤ (263882790667/1099511627776 : ℝ) := by
  rw [polynomial85]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error85 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded85 rnd h y - exact85 h y| ≤ (0/1 : ℝ) := by
  simp [rounded85, exact85]
def exact86 (h y : ℝ) : ℝ := exact85 h y * exact69 h y
def rounded86 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded85 rnd h y * rounded69 rnd h y)
theorem polynomial86 (h y : ℝ) : exact86 h y = evaluate [((1080863910568919/4503599627370496 : ℝ), 0, 1), ((64903710731685342594423432661347/324518553658426726783156020576256 : ℝ), 1, 1), ((60895901555454282506170144327524162187567645473/730750818665451459101842416358141509827966271488 : ℝ), 2, 1), ((329100911464241169254630502502544564183685879851352393275909681/13164036458569648337239753460458804039861886925068638906788872192 : ℝ), 3, 1), ((28083277778281912707003573926813039332929043526633543466027124209/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 4, 1), ((3510409722285239338995912697965686165858456543637906037218655455/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 5, 1)] h y := by
  simp only [exact86, polynomial85, polynomial69, evaluate] <;> ring
theorem bound86 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact86 h y| ≤ (17374461365/137438953472 : ℝ) := by
  rw [polynomial86]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error86 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded86 rnd h y - exact86 h y| ≤ (53514851194747601462651/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded86 exact86
  apply rounded_step rnd hrnd (propagation := (6042247959288085846662934368382591/107839786668602559178668060348078522694548577690162289924414440996864 : ℝ)) (magnitude := (17374461365/137438953472 : ℝ))
  · convert FindOrb.mul_error (bound85 h y hh hy) (bound69 h y hh hy)
      (error85 rnd hrnd h y hh hy) (error69 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound86 h y hh hy
  · norm_num
  · norm_num
def exact87 (h y : ℝ) : ℝ := exact84 h y + exact86 h y
def rounded87 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded84 rnd h y + rounded86 rnd h y)
theorem polynomial87 (h y : ℝ) : exact87 h y = evaluate [((144115188075855869/144115188075855872 : ℝ), 0, 1), ((20282409603651669125409358727523/40564819207303340847894502572032 : ℝ), 1, 1), ((974334424887268524898892582104616325508218803687/5846006549323611672814739330865132078623730171904 : ℝ), 2, 1), ((548501519107068632386430083263071233979187581624588297134122545/13164036458569648337239753460458804039861886925068638906788872192 : ℝ), 3, 1), ((56166555556563826821379094913013867503188385384735858917779244529/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 4, 1), ((3510409722285239338995912697965686165858456543637906037218655455/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 5, 1)] h y := by
  simp only [exact87, polynomial84, polynomial86, evaluate] <;> ring
theorem bound87 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact87 h y| ≤ (283649629935/549755813888 : ℝ) := by
  rw [polynomial87]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error87 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded87 rnd h y - exact87 h y| ≤ (166196861347158221550191/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded87 exact87
  apply rounded_step rnd hrnd (propagation := (586818428806659919432123/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (283649629935/549755813888 : ℝ))
  · convert FindOrb.add_error (error84 rnd hrnd h y hh hy) (error86 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound87 h y hh hy
  · norm_num
  · norm_num
def exact88 (h y : ℝ) : ℝ := exact87 h y * exact0 h y
def rounded88 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded87 rnd h y * rounded0 rnd h y)
theorem polynomial88 (h y : ℝ) : exact88 h y = evaluate [((144115188075855869/144115188075855872 : ℝ), 1, 1), ((20282409603651669125409358727523/40564819207303340847894502572032 : ℝ), 2, 1), ((974334424887268524898892582104616325508218803687/5846006549323611672814739330865132078623730171904 : ℝ), 3, 1), ((548501519107068632386430083263071233979187581624588297134122545/13164036458569648337239753460458804039861886925068638906788872192 : ℝ), 4, 1), ((56166555556563826821379094913013867503188385384735858917779244529/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 5, 1), ((3510409722285239338995912697965686165858456543637906037218655455/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 6, 1)] h y := by
  simp only [exact88, polynomial87, polynomial0, evaluate] <;> ring
theorem bound88 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact88 h y| ≤ (17728101871/549755813888 : ℝ) := by
  rw [polynomial88]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error88 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded88 rnd h y - exact88 h y| ≤ (11605569718295011419943/392318858461667547739736838950479151006397215279002157056 : ℝ) := by
  unfold rounded88 exact88
  apply rounded_step rnd hrnd (propagation := (166196861347158221550191/6277101735386680763835789423207666416102355444464034512896 : ℝ)) (magnitude := (17728101871/549755813888 : ℝ))
  · convert FindOrb.mul_error (bound87 h y hh hy) (bound0 h y hh hy)
      (error87 rnd hrnd h y hh hy) (error0 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound88 h y hh hy
  · norm_num
  · norm_num
def exact89 (h y : ℝ) : ℝ := exact88 h y + exact3 h y
def rounded89 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded88 rnd h y + rounded3 rnd h y)
theorem polynomial89 (h y : ℝ) : exact89 h y = evaluate [((1/1 : ℝ), 0, 1), ((144115188075855869/144115188075855872 : ℝ), 1, 1), ((20282409603651669125409358727523/40564819207303340847894502572032 : ℝ), 2, 1), ((974334424887268524898892582104616325508218803687/5846006549323611672814739330865132078623730171904 : ℝ), 3, 1), ((548501519107068632386430083263071233979187581624588297134122545/13164036458569648337239753460458804039861886925068638906788872192 : ℝ), 4, 1), ((56166555556563826821379094913013867503188385384735858917779244529/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 5, 1), ((3510409722285239338995912697965686165858456543637906037218655455/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 6, 1)] h y := by
  simp only [exact89, polynomial88, polynomial3, evaluate] <;> ring
theorem bound89 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact89 h y| ≤ (292606008815/549755813888 : ℝ) := by
  rw [polynomial89]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error89 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded89 rnd h y - exact89 h y| ≤ (101205534930699591405135/784637716923335095479473677900958302012794430558004314112 : ℝ) := by
  unfold rounded89 exact89
  apply rounded_step rnd hrnd (propagation := (121980142599094369098909/1569275433846670190958947355801916604025588861116008628224 : ℝ)) (magnitude := (292606008815/549755813888 : ℝ))
  · convert FindOrb.add_error (error88 rnd hrnd h y hh hy) (error3 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound89 h y hh hy
  · norm_num
  · norm_num
def exact90 (h y : ℝ) : ℝ := exact89 h y + exact2 h y
def rounded90 (rnd : ℝ → ℝ) (h y : ℝ) : ℝ := rnd (rounded89 rnd h y + rounded2 rnd h y)
theorem polynomial90 (h y : ℝ) : exact90 h y = evaluate [((1/1 : ℝ), 0, 1), ((144115188075855869/144115188075855872 : ℝ), 1, 1), ((20282409603651669125409358727523/40564819207303340847894502572032 : ℝ), 2, 1), ((974334424887268524898892582104616325508218803687/5846006549323611672814739330865132078623730171904 : ℝ), 3, 1), ((548501519107068632386430083263071233979187581624588297134122545/13164036458569648337239753460458804039861886925068638906788872192 : ℝ), 4, 1), ((56166555556563826821379094913013867503188385384735858917779244529/6739986666787659948666753771754907668409286105635143120275902562304 : ℝ), 5, 1), ((3510409722285239338995912697965686165858456543637906037218655455/3369993333393829974333376885877453834204643052817571560137951281152 : ℝ), 6, 1)] h y := by
  simp only [exact90, polynomial89, polynomial2, evaluate] <;> ring
theorem bound90 (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact90 h y| ≤ (292606008815/549755813888 : ℝ) := by
  rw [polynomial90]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem error90 (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |rounded90 rnd h y - exact90 h y| ≤ (282841997123703996521631/1569275433846670190958947355801916604025588861116008628224 : ℝ) := by
  unfold rounded90 exact90
  apply rounded_step rnd hrnd (propagation := (101205534930699591405135/784637716923335095479473677900958302012794430558004314112 : ℝ)) (magnitude := (292606008815/549755813888 : ℝ))
  · convert FindOrb.add_error (error89 rnd hrnd h y hh hy) (error2 rnd hrnd h y hh hy) using 1 <;> norm_num
  · exact bound90 h y hh hy
  · norm_num
  · norm_num
def step := rounded90
theorem stored_vs_taylor (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |exact90 h y - y * (∑ m ∈ Finset.range 16, h^m / m.factorial)| ≤ (774041074907143501037450970056507330000801037228869012444623154560383859/72201894337085274632779445707499234395631343808656318614702808013131479645159424000 : ℝ) := by
  have hid : exact90 h y - y * (∑ m ∈ Finset.range 16, h^m / m.factorial) =
      evaluate [((-3/144115188075855872 : ℝ), 1, 1), ((-1298537892558493/40564819207303340847894502572032 : ℝ), 2, 1), ((-261710691919118717062787208674891/17538019647970835018444217992595396235871190515712 : ℝ), 3, 1), ((-144995678932768136803045173120759814971946241389/39492109375708945011719260381376412119585660775205916720366616576 : ℝ), 4, 1), ((-91262657797774155446003334982433355006267799152353/101099800001814899230001306576323615026139291584527146804138538434560 : ℝ), 5, 1), ((-52656145834278603141019983958884987174159646337392450833782459597/151649700002722348845001959864485422539208937376790720206207807651840 : ℝ), 6, 1), ((-1/5040 : ℝ), 7, 1), ((-1/40320 : ℝ), 8, 1), ((-1/362880 : ℝ), 9, 1), ((-1/3628800 : ℝ), 10, 1), ((-1/39916800 : ℝ), 11, 1), ((-1/479001600 : ℝ), 12, 1), ((-1/6227020800 : ℝ), 13, 1), ((-1/87178291200 : ℝ), 14, 1), ((-1/1307674368000 : ℝ), 15, 1)] h y := by
    rw [polynomial90]
    norm_num [evaluate, Finset.sum_range_succ, Nat.factorial] <;> ring
  rw [hid]
  exact le_trans (evaluate_bound _ h y hh hy) (by norm_num [magnitude])
theorem local_error (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (h y : ℝ) (hh : |h| ≤ 1/16) (hy : |y| ≤ 1/2) :
    |step rnd h y - y * Real.exp h| ≤ (43/4000000000000 : ℝ) := by
  have ht : |y * (∑ m ∈ Finset.range 16, h^m / m.factorial) - y * Real.exp h| ≤ (17/12350635211901892262408283488256000 : ℝ) := by
    rw [← mul_sub, abs_mul, abs_sub_comm]
    exact le_trans (mul_le_mul hy (exp_taylor_bound h hh) (abs_nonneg _) (by norm_num)) (by norm_num [Nat.factorial])
  have he := FindOrb.error_trans (error90 rnd hrnd h y hh hy)
    (FindOrb.error_trans (stored_vs_taylor h y hh hy) ht)
  exact le_trans he (by norm_num)
theorem multiple_steps (rnd : ℝ → ℝ) (hrnd : RoundingModel rnd)
    (values steps : Nat → ℝ) (initial initialError : ℝ)
    (hstep : ∀ n, |steps n| ≤ 1/16) (hstate : ∀ n, |values n| ≤ 1/2)
    (hrec : ∀ n, values (n+1) = step rnd (steps n) (values n))
    (hzero : |values 0 - initial| ≤ initialError) :
    ∀ n, |values n - initial * Real.exp (elapsedTime steps n)| ≤
      FindOrb.errorBudget (16/15) (43/4000000000000 : ℝ) initialError n := by
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
end RKFLinear
end
end FindOrbLinear
