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
 (let (($x25 (and (>= (+ (+ (* a_limb b_limb) existing_digit) carry) 0) (<= (+ (+ (* a_limb b_limb) existing_digit) carry) 18446744073709551615))))
(not $x25)))
(check-sat)
