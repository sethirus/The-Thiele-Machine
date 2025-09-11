(declare-const max_prob Real)
(assert (= max_prob 0.9))

; Bind: (declare-const max_prob Real) and (assert (= max_prob <VALUE>))
(assert (> max_prob 0.95))
(check-sat)
