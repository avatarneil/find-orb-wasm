; benchmark generated from python API
(set-info :status unknown)
(assert
 (let ((?x2807 (fp.div roundNearestTiesToEven (fp.add roundNearestTiesToEven (fp #b0 #b10000000000 #x0000000000000) (fp #b0 #b10000000000 #x0000000000000)) (fp #b0 #b10000000100 #x0000000000000))))
(and (distinct (fp #b0 #b01111111100 #x0000000000000) ?x2807) true)))
(check-sat)
