; benchmark generated from python API
(set-info :status unknown)
(declare-fun sqrt_input () (_ FloatingPoint 11 53))
(assert
 (let (($x10 (fp.eq sqrt_input (_ +zero 11 53))))
(let (($x9 (fp.eq (fp.sqrt roundNearestTiesToEven sqrt_input) (_ +zero 11 53))))
(and (distinct $x9 $x10) true))))
(check-sat)
