; benchmark generated from python API
(set-info :status unknown)
(declare-fun uint64_word () (_ BitVec 64))
(assert
 (let ((?x60 (bvadd ((_ zero_extend 32) ((_ extract 31 0) uint64_word)) (bvshl (bvlshr uint64_word (_ bv32 64)) (_ bv32 64)))))
(let (($x51 (= ?x60 uint64_word)))
(not $x51))))
(check-sat)
