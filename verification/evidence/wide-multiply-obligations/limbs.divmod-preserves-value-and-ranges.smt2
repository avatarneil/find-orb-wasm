; benchmark generated from python API
(set-info :status unknown)
(declare-fun accumulator () Int)
(assert
 (>= accumulator 0))
(assert
 (<= accumulator 18446744073709551615))
(assert
 (let ((?x41 (div accumulator 4294967296)))
(let (($x37 (>= ?x41 0)))
(let (($x64 (and (= (+ (mod accumulator 4294967296) (* 4294967296 ?x41)) accumulator) (>= (mod accumulator 4294967296) 0) (< (mod accumulator 4294967296) 4294967296) $x37 (< ?x41 4294967296))))
(not $x64)))))
(check-sat)
