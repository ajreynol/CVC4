; COMMAND-LINE: --nl-ext
; EXPECT: unsat
(set-logic QF_UFNIRAT)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun w () Int)



(assert ( >= x 0))
(assert ( >= y 0))
(assert ( >= z 0))
(assert ( >= w 0))



(assert (< x w))

(assert (> (^ 2 x) (^ 2 y)))
(assert (> (^ 2 y) (^ 2 z)))
(assert (> (^ 2 z) (^ 2 w)))


(check-sat)
