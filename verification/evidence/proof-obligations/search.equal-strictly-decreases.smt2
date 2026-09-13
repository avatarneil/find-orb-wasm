; benchmark generated from python API
(set-info :status unknown)
(declare-fun N () Int)
(declare-fun L () Int)
(declare-fun U () Int)
(declare-fun n () Int)
(declare-fun lo () Int)
(declare-fun found () Bool)
(assert
 (>= N 0))
(assert
 (<= N 4294967295))
(assert
 (>= L 0))
(assert
 (<= L U))
(assert
 (<= U N))
(assert
 (let (($x53 (>= n 0)))
 (let (($x45 (>= lo 0)))
 (and $x45 $x53 (<= (+ lo n) N) (<= lo L) (<= L (+ lo n)) (=> found (< L U)) (or found (= L U) (< L (+ lo n)))))))
(assert
 (> n 0))
(assert
 (and (<= L (+ lo (div n 2))) (< (+ lo (div n 2)) U)))
(assert
 (let ((?x59 (div n 2)))
(let (($x94 (>= ?x59 0)))
(let (($x76 (and $x94 (< ?x59 n) (<= ?x59 ?x59))))
(not $x76)))))
(check-sat)
