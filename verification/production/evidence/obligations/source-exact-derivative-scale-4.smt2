; benchmark generated from python API
(set-info :status unknown)
(assert
 (let ((?x112 (fp.div roundNearestTiesToEven (fp.add roundNearestTiesToEven (fp #b0 #b10000000001 #x0000000000000) (fp #b0 #b10000000001 #x0000000000000)) (fp #b0 #b10000000100 #x0000000000000))))
(and (distinct (fp #b0 #b01111111101 #x0000000000000) ?x112) true)))
(check-sat)
