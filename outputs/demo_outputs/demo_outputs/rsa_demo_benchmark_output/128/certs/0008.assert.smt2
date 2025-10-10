; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 9330389435047756841))
(assert
 (= q 17464953979363550089))
(assert
 (= n 162954822092648946804763692057795908849))
(assert
 (= (* p q) n))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
