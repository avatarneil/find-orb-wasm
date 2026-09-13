; benchmark generated from python API
(set-info :status unknown)
(declare-fun ncf () Int)
(declare-fun ncm () Int)
(declare-fun na () Int)
(declare-fun sub () Int)
(declare-fun component () Int)
(assert
 (>= ncf 2))
(assert
 (< ncf 18))
(assert
 (>= ncm 1))
(assert
 (<= ncm 3))
(assert
 (>= na 1))
(assert
 (<= na 8))
(assert
 (>= sub 0))
(assert
 (< sub na))
(assert
 (>= component 0))
(assert
 (< component ncm))
(assert
 (let (($x107701 (and (< (* (* (* 8 ncf) ncm) na) 4294967296) true (< (* 24 ncm) 4294967296))))
(not $x107701)))
(check-sat)
