; benchmark generated from python API
(set-info :status unknown)
(declare-fun req_2 () (_ BitVec 8))
(declare-fun req_1 () (_ BitVec 8))
(assert
 (exists ((i (_ BitVec 16)) )(let ((?x28 (bvadd (bvmul ((_ zero_extend 8) req_1) (_ bv256 16)) ((_ zero_extend 8) req_2))))
(let (($x39 (bvsle (_ bv16 16) i)))
(and $x39 (bvslt i ?x28) (bvslt i (bvadd (_ bv16 16) (_ bv16 16)))))))
)
(check-sat)
