; benchmark generated from python API
(set-info :status unknown)
(declare-fun tc () Real)
(assert
 (>= tc (- 1.0)))
(assert
 (<= tc 1.0))
(assert
 (let (($x13228 (and (distinct tc (- 2.0)) true)))
(not $x13228)))
(check-sat)
