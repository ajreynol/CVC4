; COMMAND-LINE: --eager-inst --no-e-matching
(set-logic ALL)
(set-info :status unsat)
(declare-fun P (Int Int) Bool)
(declare-fun a () Int)
(assert (forall ((x Int)) (! (not (P x a)) :pattern ((P x a)))))
(assert (or
          (and (P 0 0) (= a 0))
          (and (P 1 1) (= a 1))
          (and (P 2 2) (= a 2))
        )
)
(check-sat)
