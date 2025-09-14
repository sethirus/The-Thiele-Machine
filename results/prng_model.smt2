; benchmark generated from python API
(set-info :status unknown)
(declare-fun seed () (_ BitVec 32))
(assert
 (let ((?x13 (bvadd (bvmul (_ bv1664525 32) (bvurem (bvadd (bvmul (_ bv1664525 32) seed) (_ bv1013904223 32)) (_ bv0 32))) (_ bv1013904223 32))))
 (let ((?x14 (bvurem ?x13 (_ bv0 32))))
 (= ?x14 (_ bv3761641487 32)))))
(assert
 (let ((?x13 (bvadd (bvmul (_ bv1664525 32) (bvurem (bvadd (bvmul (_ bv1664525 32) seed) (_ bv1013904223 32)) (_ bv0 32))) (_ bv1013904223 32))))
(let ((?x14 (bvurem ?x13 (_ bv0 32))))
(let ((?x17 (bvurem (bvadd (bvmul (_ bv1664525 32) ?x14) (_ bv1013904223 32)) (_ bv0 32))))
(= ?x17 (_ bv2252023330 32))))))
(check-sat)
