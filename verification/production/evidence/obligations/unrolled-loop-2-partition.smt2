; benchmark generated from python API
(set-info :status unknown)
(declare-fun available () (_ BitVec 32))
(declare-fun count () (_ BitVec 32))
(assert
 (let ((?x164 (bvsub count available)))
(let ((?x170 (bvand ?x164 (_ bv1 32))))
(let ((?x176 (bvlshr (bvsub ?x164 ?x170) (_ bv1 32))))
(let (($x71 (or (and (distinct (bvadd ?x170 (bvmul (_ bv2 32) ?x176)) ?x164) true) (bvuge ?x170 (_ bv2 32)) (bvugt ?x176 (_ bv6 32)))))
(and (bvuge count (_ bv6 32)) (bvule count (_ bv14 32)) (bvuge available (_ bv2 32)) (bvult available count) $x71))))))
(check-sat)
