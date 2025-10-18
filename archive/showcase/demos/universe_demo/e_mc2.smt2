(set-logic QF_LRA)

; Constants for mass, speed of light, energy
(declare-const Mass Real)
(declare-const c Real)
(declare-const Energy Real)

; Axiom: Speed of light is constant (approx 3e8 m/s, but symbolic)
(assert (= c 299792458.0))

; Axiom: E = m * c^2 (fundamental relation)
(assert (= Energy (* Mass (* c c))))

; No contradiction introduced here; this is just the definition
(check-sat)