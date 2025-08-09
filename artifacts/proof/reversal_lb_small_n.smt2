; asserts n=2 reversal requires at least 4 moves
; benchmark generated from python API
(set-info :status unknown)
(declare-fun moves () Int)
(assert
 (<= moves 3))
(assert
 (>= moves 4))
(check-sat)
