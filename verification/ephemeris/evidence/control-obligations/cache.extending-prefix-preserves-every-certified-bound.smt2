; benchmark generated from python API
(set-info :status unknown)
(declare-fun k () Int)
(declare-fun error () (Array Int Real))
(declare-fun exact () (Array Int Real))
(declare-fun cache () (Array Int Real))
(declare-fun computed_value () Real)
(assert
 (>= k 2))
(assert
 (< k 17))
(assert
 (forall ((j Int) )(let ((?x261 (select error j)))
 (let ((?x12598 (select exact j)))
 (let ((?x13219 (select cache j)))
 (let ((?x385 (- ?x13219 ?x12598)))
 (=> (and (>= j 0) (< j k)) (<= (ite (> ?x385 0.0) ?x385 (- ?x385)) ?x261)))))))
 )
(assert
 (let ((?x6052 (select error k)))
 (let ((?x12504 (select exact k)))
 (let ((?x48 (- computed_value ?x12504)))
 (<= (ite (> ?x48 0.0) ?x48 (- ?x48)) ?x6052)))))
(assert
 (let (($x101681 (forall ((j Int) )(let ((?x261 (select error j)))
(let ((?x12598 (select exact j)))
(let ((?x143 (store cache k computed_value)))
(let ((?x101772 (select ?x143 j)))
(let ((?x303 (- ?x101772 ?x12598)))
(=> (and (>= j 0) (< j (+ k 1))) (<= (ite (> ?x303 0.0) ?x303 (- ?x303)) ?x261))))))))
))
(not $x101681)))
(check-sat)
