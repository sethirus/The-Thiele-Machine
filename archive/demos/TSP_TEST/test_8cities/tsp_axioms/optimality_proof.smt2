(set-logic QF_LIA)
(declare-const tour (Array Int Int))
(declare-const cost Int)

; Simple constraints that PDISCOVER can try to create paradoxes with
(assert (>= cost 0))
(assert (<= cost 100000))

; Add some basic tour constraints that might create contradictions
(assert (and (>= (select tour 1) 1) (<= (select tour 1) 8)))
(assert (and (>= (select tour 2) 1) (<= (select tour 2) 8)))
(assert (and (>= (select tour 3) 1) (<= (select tour 3) 8)))
