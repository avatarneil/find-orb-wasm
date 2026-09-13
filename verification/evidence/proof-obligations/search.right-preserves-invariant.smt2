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
 (let (($x53 (>= n 0)))
 (let (($x45 (>= lo 0)))
 (and $x45 $x53 (<= (+ lo n) N) (<= lo L) (<= L (+ lo n)) $x62 (or found (= L U) (< L (+ lo n))))))))
(assert
 (> n 0))
(assert
 (let ((?x59 (div n 2)))
 (let ((?x28 (+ lo ?x59)))
 (< ?x28 L))))
(assert
 (let ((?x86 (div (- n 1) 2)))
(let ((?x59 (div n 2)))
(let ((?x28 (+ lo ?x59)))
(let ((?x83 (+ ?x28 1)))
(let ((?x94 (+ ?x83 ?x86)))
(let (($x23 (= L U)))
(let (($x62 (=> found (< L U))))
(let (($x77 (and (>= ?x83 0) (>= ?x86 0) (<= ?x94 N) (<= ?x83 L) (<= L ?x94) $x62 (or found $x23 (< L ?x94)))))
(not $x77))))))))))
(check-sat)
