; benchmark generated from python API
(set-info :status unknown)
(declare-fun ncf () Int)
(declare-fun ncm () Int)
(declare-fun na () Int)
(declare-fun sub () Int)
(declare-fun component () Int)
(declare-fun available () Int)
(declare-fun k () Int)
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
 (>= available 2))
(assert
 (< available ncf))
(assert
 (<= available k))
(assert
 (< k ncf))
(assert
 (let (($x88 (and (>= (- k 2) 0) (< (- k 1) 18) (< k 18))))
(not $x88)))
(check-sat)
