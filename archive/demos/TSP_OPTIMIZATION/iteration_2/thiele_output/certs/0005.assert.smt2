(set-logic QF_LIA)
(declare-const tour (Array Int Int))
(declare-const cost Int)

; Basic bounds
(assert (>= (select tour 1) 1))
(assert (<= (select tour 1) 6))
(assert (>= cost 0))

; Triangle inequality pruning - eliminate geometrically impossible tours
; Triangle inequality for cities 2,3,5 (dist: 268)
(assert (<= (+ 111 79) (+ 79 1)))
(assert (<= (+ 111 79) (+ 79 1)))
(assert (<= (+ 79 79) (+ 111 1)))
; Triangle inequality for cities 1,2,5 (dist: 268)
(assert (<= (+ 111 79) (+ 79 1)))
(assert (<= (+ 111 79) (+ 79 1)))
(assert (<= (+ 79 79) (+ 111 1)))
; Triangle inequality for cities 3,4,5 (dist: 268)
(assert (<= (+ 111 79) (+ 79 1)))
(assert (<= (+ 111 79) (+ 79 1)))
(assert (<= (+ 79 79) (+ 111 1)))
; Triangle inequality for cities 1,4,5 (dist: 268)
(assert (<= (+ 111 79) (+ 79 1)))
(assert (<= (+ 111 79) (+ 79 1)))
(assert (<= (+ 79 79) (+ 111 1)))
; Triangle inequality for cities 1,3,5 (dist: 314)
(assert (<= (+ 157 79) (+ 79 1)))
(assert (<= (+ 157 79) (+ 79 1)))
(assert (<= (+ 79 79) (+ 157 1)))

; MST lower bound pruning
(assert (>= cost 438))
