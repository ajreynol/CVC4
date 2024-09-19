; COMMAND-LINE: --eager-inst --no-e-matching
(set-logic ALL)
(set-info :status unsat)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (! (not (P x)) :pattern ((Q x) (P x)))))
(assert (and (P 0) (Q 0)))
(check-sat)
