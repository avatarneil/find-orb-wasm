; benchmark generated from python API
(set-info :status unknown)
(declare-fun ncf () Int)
(declare-fun ncm () Int)
(declare-fun na () Int)
(declare-fun sub () Int)
(declare-fun component () Int)
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
 (>= k 0))
(assert
 (< k 3))
(assert
 (let (($x13251 (and (>= (+ (* k ncm) component) 0) (< (+ (* k ncm) component) (* 3 ncm)))))
(not $x13251)))
(check-sat)
