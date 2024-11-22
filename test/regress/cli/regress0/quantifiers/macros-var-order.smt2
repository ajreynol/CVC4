; COMMAND-LINE: --macros-quant
; EXPECT: unsat
(set-logic UFLIRA)
(declare-fun P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (P y x)))
(assert (not (P 1 2)))
(check-sat)
