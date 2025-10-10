; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 8191))
(assert
 (= q 25599577707296307409155259226411521))
(assert
 (= n 209686141000464053988390728323536768511))
(assert
 (let ((?x31 (* p q)))
 (= ?x31 n)))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
