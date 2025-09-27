; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 14816995995298780013))
(assert
 (= q 17049352720286778533))
(assert
 (= n 252620190978925558602321844388817860929))
(assert
 (= (* p q) n))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
