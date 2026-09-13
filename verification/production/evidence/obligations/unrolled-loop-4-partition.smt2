; benchmark generated from python API
(set-info :status unknown)
(declare-fun available () (_ BitVec 32))
(declare-fun count () (_ BitVec 32))
(assert
 (let ((?x164 (bvsub count available)))
(let ((?x72 (bvand ?x164 (_ bv3 32))))
(let ((?x147 (bvlshr (bvsub ?x164 ?x72) (_ bv2 32))))
(let (($x214 (or (and (distinct (bvadd ?x72 (bvmul (_ bv4 32) ?x147)) ?x164) true) (bvuge ?x72 (_ bv4 32)) (bvugt ?x147 (_ bv6 32)))))
(and (bvuge count (_ bv6 32)) (bvule count (_ bv14 32)) (bvuge available (_ bv2 32)) (bvult available count) $x214))))))
(check-sat)
