; benchmark generated from python API
(set-info :status unknown)
(declare-fun row () Int)
(declare-fun column () Int)
(assert
 (>= row 0))
(assert
 (< row 4))
(assert
 (>= column 0))
(assert
 (< column 4))
(assert
 (let (($x37 (and (>= (+ row column) 0) (< (+ row column) 8) (>= (+ row 4) 0) (< (+ row 4) 8))))
(not $x37)))
(check-sat)
