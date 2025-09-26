; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 8191))
(assert
 (= q 30382769752103617735601879042514929))
(assert
 (= n 248865267039480732872314991237239783439))
(assert
 (let ((?x31 (* p q)))
 (= ?x31 n)))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
