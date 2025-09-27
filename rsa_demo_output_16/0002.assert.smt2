; benchmark generated from python API
(set-info :status unknown)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun n () Int)
(assert
 (= p 181))
(assert
 (= q 181))
(assert
 (= n 32761))
(assert
 (let ((?x30 (* p q)))
 (= ?x30 n)))
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
 (let (($x60 (= p 2)))
 (or $x60 (and (distinct (mod p 2) 0) true))))
(assert
 (let (($x67 (= q 2)))
 (or $x67 (and (distinct (mod q 2) 0) true))))
(assert
 (let (($x75 (= p 3)))
 (or $x75 (and (distinct (mod p 3) 0) true))))
(assert
 (let (($x82 (= q 3)))
 (or $x82 (and (distinct (mod q 3) 0) true))))
(assert
 (let (($x90 (= p 5)))
 (or $x90 (and (distinct (mod p 5) 0) true))))
(assert
 (let (($x97 (= q 5)))
 (or $x97 (and (distinct (mod q 5) 0) true))))
(assert
 (let (($x105 (= p 7)))
 (or $x105 (and (distinct (mod p 7) 0) true))))
(assert
 (let (($x112 (= q 7)))
 (or $x112 (and (distinct (mod q 7) 0) true))))
(assert
 (let (($x120 (= p 11)))
 (or $x120 (and (distinct (mod p 11) 0) true))))
(assert
 (let (($x127 (= q 11)))
 (or $x127 (and (distinct (mod q 11) 0) true))))
(assert
 (let (($x135 (= p 13)))
 (or $x135 (and (distinct (mod p 13) 0) true))))
(assert
 (let (($x142 (= q 13)))
 (or $x142 (and (distinct (mod q 13) 0) true))))
(assert
 (let (($x150 (= p 17)))
 (or $x150 (and (distinct (mod p 17) 0) true))))
(assert
 (let (($x157 (= q 17)))
 (or $x157 (and (distinct (mod q 17) 0) true))))
(assert
 (let (($x165 (= p 19)))
 (or $x165 (and (distinct (mod p 19) 0) true))))
(assert
 (let (($x172 (= q 19)))
 (or $x172 (and (distinct (mod q 19) 0) true))))
(assert
 (let (($x180 (= p 23)))
 (or $x180 (and (distinct (mod p 23) 0) true))))
(assert
 (let (($x187 (= q 23)))
(or $x187 (and (distinct (mod q 23) 0) true))))
(check-sat)
