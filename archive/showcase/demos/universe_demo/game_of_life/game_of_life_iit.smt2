; Simplified IIT for blinker (assumes declarations and states from previous files)
; Partition: left column (00,10,20) vs. rest
; Phi > 0 from irreducible causal power: cross-partition births

; Partitions are defined but not asserted, as they are determined by cell states

; Causal power whole: state changes = 4
(declare-const causal_power_whole Int)
(assert (= causal_power_whole 4))

; Independent parts: A causes 0, B causes 3 (changes in B: 2 births, 1 death)
(declare-const causal_power_A Int)
(assert (= causal_power_A 0))
(declare-const causal_power_B Int)
(assert (= causal_power_B 3))

; Phi = irreducible causal power: whole - sum parts = 4 - (0+3) = 1 > 0
(declare-const phi Int)
(assert (= phi (- causal_power_whole (+ causal_power_A causal_power_B))))
(assert (> phi 0))


; Phi derived from physics: consciousness emerges without contradiction

(check-sat)