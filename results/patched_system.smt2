; benchmark generated from python API
(set-info :status unknown)
(declare-fun req_2 () (_ BitVec 8))
(declare-fun req_1 () (_ BitVec 8))
(assert
 (let ((?x15 (bvadd (bvmul ((_ zero_extend 8) req_1) (_ bv256 16)) ((_ zero_extend 8) req_2))))
 (bvsge (_ bv16 16) ?x15)))
(assert
 (exists ((i (_ BitVec 16)) )(let ((?x15 (bvadd (bvmul ((_ zero_extend 8) req_1) (_ bv256 16)) ((_ zero_extend 8) req_2))))
(let (($x44 (bvsle (_ bv16 16) i)))
(and $x44 (bvslt i ?x15) (bvslt i (bvadd (_ bv16 16) (_ bv16 16)))))))
)
(check-sat)
