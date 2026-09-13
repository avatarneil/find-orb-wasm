; benchmark generated from python API
(set-info :status unknown)
(declare-fun na () Int)
(declare-fun ticks () Int)
(assert
 (or (= na 1) (= na 2) (= na 4) (= na 8)))
(assert
 (>= ticks 0))
(assert
 (<= ticks 68719476736))
(assert
 (let ((?x20 (* na ticks)))
(let ((?x21 (div ?x20 68719476736)))
(let (($x22 (= ?x21 na)))
(let ((?x28 (ite $x22 68719476736 (- (* 2 (mod ?x20 68719476736)) 68719476736))))
(let (($x95 (and (>= ?x20 0) (< ?x20 9007199254740992) (> ?x28 (- 9007199254740992)) (< ?x28 9007199254740992))))
(not $x95)))))))
(check-sat)
