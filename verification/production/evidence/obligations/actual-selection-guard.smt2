; benchmark generated from python API
(set-info :status unknown)
(declare-fun expected_na () (_ BitVec 32))
(declare-fun actual_na () (_ BitVec 32))
(declare-fun quantities () (_ BitVec 32))
(assert
 (let (($x204 (= actual_na expected_na)))
(let ((?x157 (ite $x204 (_ bv1 32) (_ bv0 32))))
(let (($x12 (and (distinct quantities (_ bv0 32)) true)))
(let ((?x39 (ite $x12 ?x157 (_ bv0 32))))
(and (distinct (and (distinct ?x39 (_ bv0 32)) true) (and $x12 $x204)) true))))))
(check-sat)
