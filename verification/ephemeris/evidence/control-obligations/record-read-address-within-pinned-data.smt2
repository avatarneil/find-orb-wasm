; benchmark generated from python API
(set-info :status unknown)
(declare-fun nr () Int)
(assert
 (>= nr 0))
(assert
 (< nr 12556))
(assert
 (let (($x177 (and (>= (* (+ nr 2) 8144) 16288) (<= (* (+ nr 3) 8144) 102272352))))
(not $x177)))
(check-sat)
