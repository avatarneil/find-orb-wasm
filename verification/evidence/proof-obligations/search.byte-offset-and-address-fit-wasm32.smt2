; benchmark generated from python API
(set-info :status unknown)
(declare-fun N () Int)
(declare-fun L () Int)
(declare-fun U () Int)
(declare-fun element_size () Int)
(declare-fun base_address () Int)
(declare-fun index () Int)
(assert
 (>= N 0))
(assert
 (<= N 4294967295))
(assert
 (>= L 0))
(assert
 (<= L U))
(assert
 (<= U N))
(assert
 (> element_size 0))
(assert
 (>= base_address 0))
(assert
 (<= (+ base_address (* N element_size)) 536870912))
(assert
 (>= index 0))
(assert
 (<= index N))
(assert
 (let (($x44 (and (<= (* index element_size) 4294967295) (<= (+ base_address (* index element_size)) 536870912))))
(not $x44)))
(check-sat)
