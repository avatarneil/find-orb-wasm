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
 (let (($x238 (and (> ticks 0) (< ticks 9007199254740992) (> (- ticks (* first 68719476736)) 0) (< (- ticks (* first 68719476736)) 9007199254740992))))
(not $x238)))
(check-sat)
