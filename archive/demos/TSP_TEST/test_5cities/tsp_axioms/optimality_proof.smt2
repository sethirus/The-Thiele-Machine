; Additional constraints for PDISCOVER to find contradictions
; Variables tour and cost are assumed to be already declared

; Add some basic tour constraints that might create contradictions
(assert (and (>= (select tour 1) 1) (<= (select tour 1) 5)))
(assert (and (>= (select tour 2) 1) (<= (select tour 2) 5)))
(assert (and (>= (select tour 3) 1) (<= (select tour 3) 5)))

; Add constraint that total tour length should be reasonable
(assert (<= cost 5000))

; Add constraint that might create paradoxes when partitioned
(assert (>= (select tour 1) 1))
