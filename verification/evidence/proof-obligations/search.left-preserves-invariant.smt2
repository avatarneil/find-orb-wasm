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
 (let (($x62 (=> found (< L U))))
 (let (($x61 (<= lo L)))
 (let (($x53 (>= n 0)))
 (let (($x45 (>= lo 0)))
 (and $x45 $x53 (<= (+ lo n) N) $x61 (<= L (+ lo n)) $x62 (or found (= L U) (< L (+ lo n)))))))))
(assert
 (> n 0))
(assert
 (let ((?x59 (div n 2)))
 (let ((?x28 (+ lo ?x59)))
 (<= U ?x28))))
(assert
 (let (($x62 (=> found (< L U))))
(let ((?x59 (div n 2)))
(let ((?x28 (+ lo ?x59)))
(let (($x87 (<= L ?x28)))
(let (($x61 (<= lo L)))
(let (($x94 (>= ?x59 0)))
(let (($x45 (>= lo 0)))
(let (($x26 (and $x45 $x94 (<= ?x28 N) $x61 $x87 $x62 (or found (= L U) (< L ?x28)))))
(not $x26))))))))))
(check-sat)
