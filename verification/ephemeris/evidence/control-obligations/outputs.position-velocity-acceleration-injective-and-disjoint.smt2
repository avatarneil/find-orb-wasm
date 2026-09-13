; benchmark generated from python API
(set-info :status unknown)
(declare-fun ncf () Int)
(declare-fun ncm () Int)
(declare-fun na () Int)
(declare-fun sub () Int)
(declare-fun component () Int)
(declare-fun k () Int)
(declare-fun other_kind () Int)
(declare-fun other_component () Int)
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
 (>= other_kind 0))
(assert
 (< other_kind 3))
(assert
 (>= other_component 0))
(assert
 (< other_component ncm))
(assert
 (or (and (distinct k other_kind) true) (and (distinct component other_component) true)))
(assert
 (let (($x13316 (and (distinct (+ (* k ncm) component) (+ (* other_kind ncm) other_component)) true)))
(not $x13316)))
(check-sat)
