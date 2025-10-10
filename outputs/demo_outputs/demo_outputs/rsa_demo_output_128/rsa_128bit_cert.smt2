; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 8191))
(assert
 (= q 39853778216833174944791229697603021))
(assert
 (= n 326442297374080535972784962453066345011))
(assert
 (let ((?x31 (* p q)))
 (= ?x31 n)))
(assert
 (> p 1))
(assert
 (> q 1))
(assert
 (< p n))
(assert
 (< q n))
(check-sat)
