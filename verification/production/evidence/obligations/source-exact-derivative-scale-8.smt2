; benchmark generated from python API
(set-info :status unknown)
(assert
 (let ((?x80 (fp.div roundNearestTiesToEven (fp.add roundNearestTiesToEven (fp #b0 #b10000000010 #x0000000000000) (fp #b0 #b10000000010 #x0000000000000)) (fp #b0 #b10000000100 #x0000000000000))))
(and (distinct (fp #b0 #b01111111110 #x0000000000000) ?x80) true)))
(check-sat)
