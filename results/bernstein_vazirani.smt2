; benchmark generated from python API
(set-info :status unknown)
(declare-fun s () (_ BitVec 4))
(assert
 (let ((?x15 (bvxor (bvxor (_ bv0 1) (bvand ((_ extract 0 0) s) ((_ extract 0 0) (_ bv1 4)))) (bvand ((_ extract 1 1) s) ((_ extract 1 1) (_ bv1 4))))))
 (let ((?x23 (bvxor (bvxor ?x15 (bvand ((_ extract 2 2) s) ((_ extract 2 2) (_ bv1 4)))) (bvand ((_ extract 3 3) s) ((_ extract 3 3) (_ bv1 4))))))
 (= (_ bv0 1) ?x23))))
(assert
 (let ((?x63 (bvxor (bvxor (_ bv0 1) (bvand ((_ extract 0 0) s) ((_ extract 0 0) (_ bv2 4)))) (bvand ((_ extract 1 1) s) ((_ extract 1 1) (_ bv2 4))))))
 (let ((?x69 (bvxor (bvxor ?x63 (bvand ((_ extract 2 2) s) ((_ extract 2 2) (_ bv2 4)))) (bvand ((_ extract 3 3) s) ((_ extract 3 3) (_ bv2 4))))))
 (= (_ bv1 1) ?x69))))
(assert
 (let ((?x82 (bvxor (bvxor (_ bv0 1) (bvand ((_ extract 0 0) s) ((_ extract 0 0) (_ bv4 4)))) (bvand ((_ extract 1 1) s) ((_ extract 1 1) (_ bv4 4))))))
 (let ((?x88 (bvxor (bvxor ?x82 (bvand ((_ extract 2 2) s) ((_ extract 2 2) (_ bv4 4)))) (bvand ((_ extract 3 3) s) ((_ extract 3 3) (_ bv4 4))))))
 (= (_ bv0 1) ?x88))))
(assert
 (let ((?x99 (bvxor (bvxor (_ bv0 1) (bvand ((_ extract 0 0) s) ((_ extract 0 0) (_ bv8 4)))) (bvand ((_ extract 1 1) s) ((_ extract 1 1) (_ bv8 4))))))
(let ((?x105 (bvxor (bvxor ?x99 (bvand ((_ extract 2 2) s) ((_ extract 2 2) (_ bv8 4)))) (bvand ((_ extract 3 3) s) ((_ extract 3 3) (_ bv8 4))))))
(= (_ bv1 1) ?x105))))
(check-sat)
