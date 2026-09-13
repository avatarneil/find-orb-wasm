; benchmark generated from python API
(set-info :status unknown)
(declare-fun nr () Int)
(declare-fun cached () Int)
(declare-fun contents () Int)
(assert
 (= cached nr))
(assert
 (and (distinct contents nr) true))
(assert
 (>= nr 0))
(assert
 (< nr 12556))
(check-sat)
