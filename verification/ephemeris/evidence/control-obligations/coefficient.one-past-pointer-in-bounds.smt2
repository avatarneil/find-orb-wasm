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
 (let ((?x226 (* sub ncm)))
(let ((?x225 (+ component ?x226)))
(let ((?x110 (* ncf ?x225)))
(let ((?x346 (+ ?x110 ncf)))
(let (($x181 (and (> ?x346 0) (<= ?x346 (* (* ncf ncm) na)))))
(not $x181)))))))
(check-sat)
