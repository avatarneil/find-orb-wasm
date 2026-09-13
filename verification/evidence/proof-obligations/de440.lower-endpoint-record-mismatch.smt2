; benchmark generated from python API
(set-info :status unknown)
(declare-fun first () Int)
(declare-fun ticks () Int)
(assert
 (> first 0))
(assert
 (let ((?x96 (* first 68719476736)))
 (= ticks ?x96)))
(assert
 (let (($x120 (and (= (mod (- ticks (* first 68719476736)) 68719476736) 0) (> (div (- ticks (* first 68719476736)) 68719476736) 0))))
(let ((?x96 (* first 68719476736)))
(let ((?x146 (- ticks ?x96)))
(let ((?x143 (div ?x146 68719476736)))
(let ((?x84 (- ?x143 (ite $x120 1 0))))
(let ((?x95 (mod ticks 68719476736)))
(let (($x80 (= ?x95 0)))
(let (($x92 (and $x80 (> (div ticks 68719476736) 0))))
(let ((?x79 (div ticks 68719476736)))
(let ((?x148 (- ?x79 (ite $x92 1 0))))
(let (($x137 (and (distinct ?x148 (+ first ?x84)) true)))
(not $x137)))))))))))))
(check-sat)
