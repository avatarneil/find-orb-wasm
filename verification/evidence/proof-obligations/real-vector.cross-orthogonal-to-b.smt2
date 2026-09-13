; benchmark generated from python API
(set-info :status unknown)
(declare-fun b2 () Real)
(declare-fun b0 () Real)
(declare-fun a1 () Real)
(declare-fun b1 () Real)
(declare-fun a0 () Real)
(declare-fun a2 () Real)
(assert
 (let ((?x99 (+ (* (- (* a1 b2) (* a2 b1)) b0) (* (- (* a2 b0) (* a0 b2)) b1))))
(let (($x172 (= (+ ?x99 (* (- (* a0 b1) (* a1 b0)) b2)) 0.0)))
(not $x172))))
(check-sat)
