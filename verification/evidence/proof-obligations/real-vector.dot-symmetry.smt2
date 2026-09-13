; benchmark generated from python API
(set-info :status unknown)
(declare-fun a2 () Real)
(declare-fun b2 () Real)
(declare-fun a1 () Real)
(declare-fun b1 () Real)
(declare-fun a0 () Real)
(declare-fun b0 () Real)
(assert
 (let (($x236 (= (+ (+ (* a0 b0) (* a1 b1)) (* a2 b2)) (+ (+ (* b0 a0) (* b1 a1)) (* b2 a2)))))
(not $x236)))
(check-sat)
