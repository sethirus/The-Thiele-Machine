(set-logic QF_LIA)
(declare-const tour (Array Int Int))
(declare-const cost Int)

; Basic constraints - always satisfiable
(assert (>= cost 0))
(assert (<= cost 100000))
