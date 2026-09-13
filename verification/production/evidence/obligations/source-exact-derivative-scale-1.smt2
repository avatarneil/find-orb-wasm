; benchmark generated from python API
(set-info :status unknown)
(assert
 (let ((?x111 (fp.div roundNearestTiesToEven (fp.add roundNearestTiesToEven (fp #b0 #b01111111111 #x0000000000000) (fp #b0 #b01111111111 #x0000000000000)) (fp #b0 #b10000000100 #x0000000000000))))
(and (distinct (fp #b0 #b01111111011 #x0000000000000) ?x111) true)))
(check-sat)
