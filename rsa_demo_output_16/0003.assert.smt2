; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 227))
(assert
 (= q 241))
(assert
 (= n 54707))
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
(assert
 (>= p 2))
(assert
 (>= q 2))
(assert
 (let (($x61 (= p 2)))
 (or $x61 (and (distinct (mod p 2) 0) true))))
(assert
 (let (($x68 (= q 2)))
 (or $x68 (and (distinct (mod q 2) 0) true))))
(assert
 (let (($x76 (= p 3)))
 (or $x76 (and (distinct (mod p 3) 0) true))))
(assert
 (let (($x83 (= q 3)))
 (or $x83 (and (distinct (mod q 3) 0) true))))
(assert
 (let (($x91 (= p 5)))
 (or $x91 (and (distinct (mod p 5) 0) true))))
(assert
 (let (($x98 (= q 5)))
 (or $x98 (and (distinct (mod q 5) 0) true))))
(assert
 (let (($x106 (= p 7)))
 (or $x106 (and (distinct (mod p 7) 0) true))))
(assert
 (let (($x113 (= q 7)))
 (or $x113 (and (distinct (mod q 7) 0) true))))
(assert
 (let (($x121 (= p 11)))
 (or $x121 (and (distinct (mod p 11) 0) true))))
(assert
 (let (($x128 (= q 11)))
 (or $x128 (and (distinct (mod q 11) 0) true))))
(assert
 (let (($x136 (= p 13)))
 (or $x136 (and (distinct (mod p 13) 0) true))))
(assert
 (let (($x143 (= q 13)))
 (or $x143 (and (distinct (mod q 13) 0) true))))
(assert
 (let (($x151 (= p 17)))
 (or $x151 (and (distinct (mod p 17) 0) true))))
(assert
 (let (($x158 (= q 17)))
 (or $x158 (and (distinct (mod q 17) 0) true))))
(assert
 (let (($x166 (= p 19)))
 (or $x166 (and (distinct (mod p 19) 0) true))))
(assert
 (let (($x173 (= q 19)))
 (or $x173 (and (distinct (mod q 19) 0) true))))
(assert
 (let (($x181 (= p 23)))
 (or $x181 (and (distinct (mod p 23) 0) true))))
(assert
 (let (($x188 (= q 23)))
(or $x188 (and (distinct (mod q 23) 0) true))))
(check-sat)
