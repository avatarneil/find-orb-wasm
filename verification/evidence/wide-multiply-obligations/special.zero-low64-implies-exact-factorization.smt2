; benchmark generated from python API
(set-info :status unknown)
(declare-fun input128 () (_ BitVec 128))
(assert
 (let ((?x225 ((_ extract 63 0) input128)))
 (= ?x225 (_ bv0 64))))
(assert
 (let (($x382 (= input128 (bvshl ((_ zero_extend 64) ((_ extract 127 64) input128)) (_ bv64 128)))))
(not $x382)))
(check-sat)
