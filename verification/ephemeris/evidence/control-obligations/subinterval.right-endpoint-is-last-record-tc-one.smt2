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
 (= ticks 68719476736))
(assert
 (let ((?x20 (* na ticks)))
(let ((?x21 (div ?x20 68719476736)))
(let (($x22 (= ?x21 na)))
(let ((?x28 (ite $x22 68719476736 (- (* 2 (mod ?x20 68719476736)) 68719476736))))
(let (($x110 (and (= (ite $x22 (- ?x21 1) ?x21) (- na 1)) (= ?x28 68719476736))))
(not $x110)))))))
(check-sat)
