(declare-const out Real)
(assert (= out 0.5021006182077947))

; Bind: (declare-const out Real) and (assert (= out <VALUE>))
(assert (and (>= out 0.0) (<= out 1.0)))
(check-sat)
