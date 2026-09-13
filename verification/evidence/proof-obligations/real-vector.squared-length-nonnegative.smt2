; benchmark generated from python API
(set-info :status unknown)
(declare-fun a2 () Real)
(declare-fun a1 () Real)
(declare-fun a0 () Real)
(assert
 (let (($x160 (>= (+ (+ (* a0 a0) (* a1 a1)) (* a2 a2)) 0.0)))
(not $x160)))
(check-sat)
