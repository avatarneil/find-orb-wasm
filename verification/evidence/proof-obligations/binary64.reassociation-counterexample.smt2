; benchmark generated from python API
(set-info :status unknown)
(assert
 (let ((?x264 (fp.add roundNearestTiesToEven (fp #b0 #b10000110100 #x1c37937e08000) (fp.add roundNearestTiesToEven (fp #b1 #b10000110100 #x1c37937e08000) (fp #b0 #b01111111111 #x0000000000000)))))
(let ((?x238 (fp.add roundNearestTiesToEven (fp.add roundNearestTiesToEven (fp #b0 #b10000110100 #x1c37937e08000) (fp #b1 #b10000110100 #x1c37937e08000)) (fp #b0 #b01111111111 #x0000000000000))))
(let (($x176 (not (fp.eq ?x238 ?x264))))
(not $x176)))))
(check-sat)
