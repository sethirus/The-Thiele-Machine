(set-logic QF_LRA)
; Linear model for All pieces
(declare-fun a0 () Real)
(declare-fun b0 () Real)
(declare-fun c0 () Real)
(assert (= (+ (* 0 a0) (* 0 b0) c0) 0))
(assert (= (+ (* 1 a0) (* 0 b0) c0) 0))
(assert (= (+ (* 0 a0) (* 1 b0) c0) 0))
(assert (= (+ (* 1 a0) (* 1 b0) c0) 1))
