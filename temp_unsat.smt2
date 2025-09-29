(set-logic QF_BV)
(declare-const m0 (_ BitVec 1))
(declare-const m1 (_ BitVec 1))
(declare-const m2 (_ BitVec 1))
(assert (= m0 #b1))  ; input b1 = 1
(assert (= m1 #b1))  ; input b2 = 1
(assert (= m2 #b0))  ; candidate write (XOR result = 0)
; Policy axiom: forbid (m2=0 ∧ m0=1 ∧ m1=1)
(assert (not (and (= m2 #b0) (= m0 #b1) (= m1 #b1))))
(check-sat)