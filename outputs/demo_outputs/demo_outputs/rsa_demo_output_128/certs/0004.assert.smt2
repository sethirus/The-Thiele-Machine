; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 18446744073709551557))
(assert
 (= q 18446744073709551629))
(assert
 (= n 340282366920938462614824380041128836353))
(assert
 (= (* p q) n))
(assert
 (> p 1))
(assert
 (> q 1))
(check-sat)
