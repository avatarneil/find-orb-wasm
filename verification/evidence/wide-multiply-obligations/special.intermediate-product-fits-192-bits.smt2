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
 (< unsigned128_b 18446744073709551616))
(assert
 (let (($x183 (and (>= (* unsigned128_a unsigned128_b) 0) (< (* unsigned128_a unsigned128_b) 6277101735386680763835789423207666416102355444464034512896))))
(not $x183)))
(check-sat)
