; benchmark generated from python API
(set-info :status unknown)
(declare-fun nr () Int)
(declare-fun nrecords () Int)
(declare-fun cached () Int)
(declare-fun contents () Int)
(declare-fun io_ok () Bool)
(assert
 (>= nr 0))
(assert
 (< nr nrecords))
(assert
 (let (($x12514 (= contents cached)))
 (let (($x78322 (= nr cached)))
 (=> $x78322 $x12514))))
(assert
 (let (($x78322 (= nr cached)))
 (or $x78322 io_ok)))
(assert
 (let (($x78322 (= nr cached)))
(let ((?x179 (ite $x78322 contents nr)))
(let (($x6002 (= ?x179 nr)))
(not $x6002)))))
(check-sat)
