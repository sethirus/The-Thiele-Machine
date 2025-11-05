(set-logic QF_LIA)
; --- Declarations ---
(declare-const tour (Array Int Int))
(declare-const cost Int)
; --- Axioms for a Valid Tour ---
(assert (Distinct (select tour 1) (select tour 2) (select tour 3) (select tour 4) (select tour 5) (select tour 6)))
(assert (and (>= (select tour 1) 1) (<= (select tour 1) 6)))
(assert (and (>= (select tour 2) 1) (<= (select tour 2) 6)))
(assert (and (>= (select tour 3) 1) (<= (select tour 3) 6)))
(assert (and (>= (select tour 4) 1) (<= (select tour 4) 6)))
(assert (and (>= (select tour 5) 1) (<= (select tour 5) 6)))
(assert (and (>= (select tour 6) 1) (<= (select tour 6) 6)))
; --- Axioms for Cost Calculation (Proxy) ---
(assert (= cost (+ (select tour 1) (select tour 2) (select tour 3) (select tour 4) (select tour 5) (select tour 6))))
; --- The Optimality Constraint ---
(assert (< cost 8))
(check-sat)
(get-model)
