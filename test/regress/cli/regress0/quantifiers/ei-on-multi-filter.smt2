; COMMAND-LINE: --eager-inst --no-e-matching
(set-logic ALL)
(set-info :status unsat)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)
(declare-fun a () Int)
(assert (forall ((x Int)) (! (not (P x)) :pattern ((P x) (Q x)))))
(assert (or
          (and (P 0) (Q a) (= a 0))
          (and (P 1) (Q a) (= a 1))
          (and (P 2) (Q a) (= a 2))))
(check-sat)
