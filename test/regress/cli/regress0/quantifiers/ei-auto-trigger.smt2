; COMMAND-LINE: --eager-inst --no-e-matching --no-cbqi
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-info :status unsat)

(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun a () Int)

(assert (forall ((x Int)) (=> (P x) (Q x))))
(assert (P a))
(assert (not (Q a)))
(check-sat)
