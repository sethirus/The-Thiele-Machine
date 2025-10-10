; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 13387598225810684503))
(assert
 (= q 15134274805957779097))
(assert
 (= n 202611590541171704913272606411235233791))
(assert
 (= (* p q) n))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
