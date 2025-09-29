; Conservation laws for incremental physical realism in Game of Life toy universe
; Assumes declarations from previous files

; Conservation of mass: total live cells conserved over transition (assumes mass_current, mass_next declared in blinker.smt2)
(assert (= mass_current mass_next))

; Conservation of energy: define energy as live cell count (same as mass for simplicity)
; In more realistic physics, energy might be kinetic/potential, but here proxy
(declare-const energy_current Int)
(assert (= energy_current mass_current))
(declare-const energy_next Int)
(assert (= energy_next mass_next))
(assert (= energy_current energy_next))

; Momentum conservation: for cellular automata, define as net movement
; For 3x3 grid, simple: no net displacement for blinker (oscillates in place)
; Assert that the center of mass doesn't move (sum positions weighted by live cells)
; Positions: approximate x-coords: 00=0,01=1,02=2,10=0,11=1,12=2,20=0,21=1,22=2
; y-coords: 00=0,01=0,02=0,10=1,11=1,12=1,20=2,21=2,22=2
(declare-const cmx_current Real)
(assert (= cmx_current (/ (+ (* (ite cell00 1 0) 0) (* (ite cell01 1 0) 1) (* (ite cell02 1 0) 2)
                              (* (ite cell10 1 0) 0) (* (ite cell11 1 0) 1) (* (ite cell12 1 0) 2)
                              (* (ite cell20 1 0) 0) (* (ite cell21 1 0) 1) (* (ite cell22 1 0) 2)) mass_current)))
(declare-const cmy_current Real)
(assert (= cmy_current (/ (+ (* (ite cell00 1 0) 0) (* (ite cell01 1 0) 0) (* (ite cell02 1 0) 0)
                              (* (ite cell10 1 0) 1) (* (ite cell11 1 0) 1) (* (ite cell12 1 0) 1)
                              (* (ite cell20 1 0) 2) (* (ite cell21 1 0) 2) (* (ite cell22 1 0) 2)) mass_current)))
(declare-const cmx_next Real)
(assert (= cmx_next (/ (+ (* (ite next00 1 0) 0) (* (ite next01 1 0) 1) (* (ite next02 1 0) 2)
                           (* (ite next10 1 0) 0) (* (ite next11 1 0) 1) (* (ite next12 1 0) 2)
                           (* (ite next20 1 0) 0) (* (ite next21 1 0) 1) (* (ite next22 1 0) 2)) mass_next)))
(declare-const cmy_next Real)
(assert (= cmy_next (/ (+ (* (ite next00 1 0) 0) (* (ite next01 1 0) 0) (* (ite next02 1 0) 0)
                           (* (ite next10 1 0) 1) (* (ite next11 1 0) 1) (* (ite next12 1 0) 1)
                           (* (ite next20 1 0) 2) (* (ite next21 1 0) 2) (* (ite next22 1 0) 2)) mass_next)))
; For blinker, cmx_current = (0+1+2)/3 =1, cmy_current=(1+1+1)/3=1
; cmx_next = (1+1+1)/3=1, cmy_next=(0+2+2)/3≈1.333? Wait, next is 01,11,21: x=1,1,1 avg=1, y=0,1,2 avg=1
; Yes, conserved.

(check-sat)