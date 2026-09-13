; benchmark generated from python API
(set-info :status unknown)
(declare-fun cache () (Array Int Real))
(declare-fun tc () Real)
(assert
 (let ((?x284 (select cache 0)))
 (= ?x284 1.0)))
(assert
 (>= tc (- 1.0)))
(assert
 (<= tc 1.0))
(assert
 (let (($x5078 (and (= (select (store cache 1 tc) 0) 1.0) (= (select (store cache 1 tc) 1) tc))))
(not $x5078)))
(check-sat)
