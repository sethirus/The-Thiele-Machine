; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 2645525093))
(assert
 (= q 2718432533))
(assert
 (= n 7191681479679050569))
(assert
 (let ((?x31 (* p q)))
 (= ?x31 n)))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
