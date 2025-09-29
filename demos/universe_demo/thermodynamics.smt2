; Constants for entropy at time 1 and time 2 in a closed system
(declare-const entropy_t1 Real)
(declare-const entropy_t2 Real)

; Axiom: Second Law of Thermodynamics - entropy of a closed system never decreases
(assert (>= entropy_t2 entropy_t1))

; No contradiction; this is a universal inequality
(check-sat)