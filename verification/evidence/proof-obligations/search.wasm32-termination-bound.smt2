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
 (let ((?x73 (div (div (div (div (div (div N 2) 2) 2) 2) 2) 2)))
(let ((?x29 (div (div (div (div (div (div ?x73 2) 2) 2) 2) 2) 2)))
(let ((?x113 (div (div (div (div (div (div ?x29 2) 2) 2) 2) 2) 2)))
(let ((?x121 (div (div (div (div (div (div ?x113 2) 2) 2) 2) 2) 2)))
(let ((?x97 (div (div (div (div (div (div ?x121 2) 2) 2) 2) 2) 2)))
(let ((?x66 (div (div ?x97 2) 2)))
(let (($x107 (= ?x66 0)))
(not $x107)))))))))
(check-sat)
