; benchmark generated from python API
(set-info :status unknown)
(declare-fun a2 () Real)
(declare-fun b0 () Real)
(declare-fun a1 () Real)
(declare-fun b1 () Real)
(declare-fun a0 () Real)
(declare-fun b2 () Real)
(assert
 (let ((?x39 (+ (* (- (* a1 b2) (* a2 b1)) a0) (* (- (* a2 b0) (* a0 b2)) a1))))
(let (($x327 (= (+ ?x39 (* (- (* a0 b1) (* a1 b0)) a2)) 0.0)))
(not $x327))))
(check-sat)
