; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 2335456861))
(assert
 (= q 4227576593))
(assert
 (= n 9873322759524854573))
(assert
 (let ((?x31 (* p q)))
 (= ?x31 n)))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
