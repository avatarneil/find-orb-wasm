; benchmark generated from python API
(set-info :status unknown)
(declare-fun unsigned128_a () Int)
(declare-fun unsigned128_b () Int)
(assert
 (let ((?x182 (* unsigned128_b unsigned128_a)))
(let (($x202 (= (* unsigned128_a unsigned128_b) ?x182)))
(not $x202))))
(check-sat)
