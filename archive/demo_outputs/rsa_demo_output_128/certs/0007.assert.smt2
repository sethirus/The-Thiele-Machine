; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 8191))
(assert
 (= q 28326831690526017469806496019495053))
(assert
 (= n 232025078377098609095185008895683979123))
(assert
 (let ((?x31 (* p q)))
 (= ?x31 n)))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
