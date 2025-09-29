; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 2))
(assert
 (= q 4365655703))
(assert
 (= n 34028236692093846344460723086997759132))
(assert
 (= (* p q) n))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
