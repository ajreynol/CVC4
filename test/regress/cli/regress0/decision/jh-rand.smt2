; COMMAND-LINE: --decision=justification --jh-rand
; COMMAND-LINE: --decision=justification --jh-rand --seed=1
; COMMAND-LINE: --decision=justification --jh-rand --seed=7
; COMMAND-LINE: --decision=justification --jh-rand --seed=17
; EXPECT: unsat
(set-logic QF_UF)
(set-info :status unsat)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
; the conjunction below is a tautology, so its negation is unsatisfiable
(assert (not (and (= (and p q) (and q p))
                  (= (or p q) (or q p))
                  (= (and p (or q r)) (or (and p q) (and p r)))
                  (or p (not p))
                  (=> (and p q) p))))
(check-sat)
