; benchmark generated from python API
(set-info :status unknown)
(declare-fun a_limb () Int)
(declare-fun b_limb () Int)
(declare-fun existing_digit () Int)
(declare-fun carry () Int)
(assert
 (>= a_limb 0))
(assert
 (>= b_limb 0))
(assert
 (>= existing_digit 0))
(assert
 (>= carry 0))
(assert
 (< a_limb 4294967296))
(assert
 (< b_limb 4294967296))
(assert
 (< existing_digit 4294967296))
(assert
 (< carry 4294967296))
(assert
 (let ((?x19 (* a_limb b_limb)))
(let ((?x20 (+ ?x19 existing_digit)))
(let ((?x21 (+ ?x20 carry)))
(let (($x61 (and (<= ?x19 ?x21) (<= ?x20 ?x21))))
(not $x61))))))
(check-sat)
