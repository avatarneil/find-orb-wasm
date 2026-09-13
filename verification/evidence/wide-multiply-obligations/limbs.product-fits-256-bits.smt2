; benchmark generated from python API
(set-info :status unknown)
(declare-fun unsigned128_a () Int)
(declare-fun unsigned128_b () Int)
(assert
 (>= unsigned128_a 0))
(assert
 (< unsigned128_a 340282366920938463463374607431768211456))
(assert
 (>= unsigned128_b 0))
(assert
 (< unsigned128_b 340282366920938463463374607431768211456))
(assert
 (let (($x28 (and (>= (* unsigned128_a unsigned128_b) 0) (< (* unsigned128_a unsigned128_b) 115792089237316195423570985008687907853269984665640564039457584007913129639936))))
(not $x28)))
(check-sat)
