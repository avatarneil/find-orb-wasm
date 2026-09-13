; benchmark generated from python API
(set-info :status unknown)
(assert
 (let ((?x161 (fp.fma roundNearestTiesToEven (fp #b0 #b01111111111 #x0000002000000) (fp #b0 #b01111111110 #xffffffc000000) (fp #b1 #b01111111111 #x0000000000000))))
(let ((?x703 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven (fp #b0 #b01111111111 #x0000002000000) (fp #b0 #b01111111110 #xffffffc000000)) (fp #b1 #b01111111111 #x0000000000000))))
(let (($x243 (not (fp.eq ?x703 ?x161))))
(not $x243)))))
(check-sat)
