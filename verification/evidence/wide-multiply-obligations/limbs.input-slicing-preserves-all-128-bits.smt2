; benchmark generated from python API
(set-info :status unknown)
(declare-fun input128 () (_ BitVec 128))
(assert
 (let ((?x65 (bvor (bvor (_ bv0 128) (bvshl ((_ zero_extend 96) ((_ extract 31 0) input128)) (_ bv0 128))) (bvshl ((_ zero_extend 96) ((_ extract 63 32) input128)) (_ bv32 128)))))
(let ((?x39 (bvor (bvor ?x65 (bvshl ((_ zero_extend 96) ((_ extract 95 64) input128)) (_ bv64 128))) (bvshl ((_ zero_extend 96) ((_ extract 127 96) input128)) (_ bv96 128)))))
(let (($x35 (= ?x39 input128)))
(not $x35)))))
(check-sat)
