; Assertions for blinker pattern in 3x3 grid (assumes declarations in rules.smt2)
; Initial state: middle row alive (vertical bar)
(assert (not cell00)) (assert (not cell01)) (assert (not cell02))
(assert cell10) (assert cell11) (assert cell12)
(assert (not cell20)) (assert (not cell21)) (assert (not cell22))

; Expected next state: horizontal bar in middle column
(assert (not next00)) (assert next01) (assert (not next02))
(assert (not next10)) (assert next11) (assert (not next12))
(assert (not next20)) (assert next21) (assert (not next22))

; Mass-equivalent: total live cells current = 3
(declare-const mass_current Int)
(assert (= mass_current (+ (ite cell00 1 0) (ite cell01 1 0) (ite cell02 1 0)
                           (ite cell10 1 0) (ite cell11 1 0) (ite cell12 1 0)
                           (ite cell20 1 0) (ite cell21 1 0) (ite cell22 1 0))))
(assert (= mass_current 3))

; Mass next = 3 (conservation)
(declare-const mass_next Int)
(assert (= mass_next (+ (ite next00 1 0) (ite next01 1 0) (ite next02 1 0)
                        (ite next10 1 0) (ite next11 1 0) (ite next12 1 0)
                        (ite next20 1 0) (ite next21 1 0) (ite next22 1 0))))
(assert (= mass_next 3))

; Energy-equivalent: number of state changes = 4 (2 births, 2 deaths)
(declare-const changes Int)
(assert (= changes (+ (ite (= cell00 next00) 0 1) (ite (= cell01 next01) 0 1) (ite (= cell02 next02) 0 1)
                      (ite (= cell10 next10) 0 1) (ite (= cell11 next11) 0 1) (ite (= cell12 next12) 0 1)
                      (ite (= cell20 next20) 0 1) (ite (= cell21 next21) 0 1) (ite (= cell22 next22) 0 1))))
(assert (= changes 4))

; Verify rules hold for this transition (rules from game_of_life_rules.smt2 ensure this is SAT)

(check-sat)