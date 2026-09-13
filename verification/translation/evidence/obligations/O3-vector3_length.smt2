; benchmark generated from python API
(set-info :status unknown)
(declare-fun vect_2 () (_ FloatingPoint 11 53))
(declare-fun vect_1 () (_ FloatingPoint 11 53))
(declare-fun vect_0 () (_ FloatingPoint 11 53))
(declare-fun arithmetic_0 () (_ FloatingPoint 11 53))
(assert
 (let (($x1764 (and (distinct vect_2 vect_2) true)))
(let (($x1867 (and (distinct vect_1 vect_1) true)))
(let (($x1866 (and (distinct vect_0 vect_0) true)))
(let (($x54 (and true (or (and (distinct arithmetic_0 arithmetic_0) true) $x1866 $x1867 $x1764))))
(let (($x1906 (not (or true))))
(or $x1906 $x54)))))))
(check-sat)
