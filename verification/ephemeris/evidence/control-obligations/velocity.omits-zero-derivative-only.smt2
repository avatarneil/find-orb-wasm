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
 (>= k 1))
(assert
 (< k ncf))
(assert
 (let ((?x110 (* ncf (+ component (* sub ncm)))))
(let ((?x7717 (+ ?x110 k)))
(let (($x182 (>= k 1)))
(let (($x90 (and $x182 (< k 18) (>= ?x7717 0) (< ?x7717 (* (* ncf ncm) na)))))
(not $x90))))))
(check-sat)
