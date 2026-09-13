; benchmark generated from python API
(set-info :status unknown)
(declare-fun N () Int)
(declare-fun L () Int)
(declare-fun U () Int)
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
 (let (($x15 (>= L 0)))
(let (($x12 (>= N 0)))
(let (($x26 (and true $x12 (<= (+ 0 N) N) $x15 (<= L (+ 0 N)) (=> false (< L U)) (or false (= L U) (< L (+ 0 N))))))
(not $x26)))))
(check-sat)
