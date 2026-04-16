; COMMAND-LINE: --eager-inst --no-eager-inst-simple --no-e-matching
; EXPECT: unsat
(set-logic ALL)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (=> (P (f x)) (Q x)) :pattern ((P (f x))))))
(assert (or
          (and (= (f a) 0) (P 0))
          (and (= (f b) 1) (P 1))
        )
)
(assert (and (not (Q a)) (not (Q b))))
(check-sat)
