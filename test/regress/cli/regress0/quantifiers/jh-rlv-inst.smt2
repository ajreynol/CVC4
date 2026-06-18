; COMMAND-LINE: --decision=justification --jh-rlv-inst
; COMMAND-LINE: --decision=stoponly --jh-rlv-inst
; EXPECT: unsat
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (P x)))
(assert (not (P a)))
(check-sat)
