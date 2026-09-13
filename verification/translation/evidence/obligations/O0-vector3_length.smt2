; benchmark generated from python API
(set-info :status unknown)
(declare-fun vect_2 () (_ FloatingPoint 11 53))
(declare-fun vect_1 () (_ FloatingPoint 11 53))
(declare-fun vect_0 () (_ FloatingPoint 11 53))
(declare-fun arithmetic_0 () (_ FloatingPoint 11 53))
(assert
 (let (($x1794 (and (distinct vect_2 vect_2) true)))
(let (($x103 (and (distinct vect_1 vect_1) true)))
(let (($x1793 (and (distinct vect_0 vect_0) true)))
(let (($x1746 (and true (or (and (distinct arithmetic_0 arithmetic_0) true) $x1793 $x103 $x1794))))
(let (($x16 (not (or true))))
(or $x16 $x1746)))))))
(check-sat)
