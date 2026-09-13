; benchmark generated from python API
(set-info :status unknown)
(declare-fun coefficient_pointer () (_ BitVec 32))
(declare-fun record_base () (_ BitVec 32))
(assert
 (and (distinct (bvsub (bvadd record_base (bvshl coefficient_pointer (_ bv3 32))) (_ bv8 32)) (bvadd record_base (bvshl (bvsub coefficient_pointer (_ bv1 32)) (_ bv3 32)))) true))
(check-sat)
