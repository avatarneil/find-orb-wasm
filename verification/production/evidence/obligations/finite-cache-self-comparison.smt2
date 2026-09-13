; benchmark generated from python API
(set-info :status unknown)
(declare-fun tc () (_ FloatingPoint 11 53))
(assert
 (let (($x99 (not (fp.eq tc tc))))
(let (($x198 (not (fp.isNaN tc))))
(and $x198 $x99))))
(check-sat)
