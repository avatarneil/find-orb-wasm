; benchmark generated from python API
(set-info :status unknown)
(declare-fun special_row () Int)
(declare-fun special_column () Int)
(assert
 (>= special_row 0))
(assert
 (< special_row 4))
(assert
 (>= special_column 0))
(assert
 (< special_column 2))
(assert
 (let ((?x229 (+ special_row special_column)))
(let (($x177 (>= ?x229 0)))
(let (($x375 (and $x177 (< ?x229 6) (>= (+ special_row 2) 0) (< (+ special_row 2) 6))))
(not $x375)))))
(check-sat)
