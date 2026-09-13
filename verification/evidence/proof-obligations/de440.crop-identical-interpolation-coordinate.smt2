; benchmark generated from python API
(set-info :status unknown)
(declare-fun first () Int)
(declare-fun count () Int)
(declare-fun full_count () Int)
(declare-fun ticks () Int)
(assert
 (>= first 0))
(assert
 (> count 0))
(assert
 (let ((?x153 (+ first count)))
 (<= ?x153 full_count)))
(assert
 (< full_count 16384))
(assert
 (let ((?x96 (* first 68719476736)))
 (< ?x96 ticks)))
(assert
 (<= ticks (* (+ first count) 68719476736)))
(assert
 (let ((?x96 (* first 68719476736)))
(let ((?x146 (- ticks ?x96)))
(let ((?x94 (mod ?x146 68719476736)))
(let (($x120 (and (= ?x94 0) (> (div ?x146 68719476736) 0))))
(let ((?x119 (ite $x120 68719476736 ?x94)))
(let ((?x95 (mod ticks 68719476736)))
(let (($x80 (= ?x95 0)))
(let (($x92 (and $x80 (> (div ticks 68719476736) 0))))
(let ((?x75 (ite $x92 68719476736 ?x95)))
(let (($x78 (= ?x75 ?x119)))
(not $x78))))))))))))
(check-sat)
