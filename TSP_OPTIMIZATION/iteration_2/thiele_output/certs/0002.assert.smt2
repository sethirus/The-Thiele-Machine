(set-logic QF_LIA)
(declare-const tour (Array Int Int))
(declare-const cost Int)

; Very simple constraints - always satisfiable
(assert (>= (select tour 1) 1))
(assert (<= (select tour 1) 22))
(assert (>= cost 0))
(assert (<= cost 100000))
