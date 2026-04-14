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
          (and (P 0) (= (f a) 0))
          (and (P 1) (= (f b) 1))
        )
)
(assert (and (not (Q a)) (not (Q b))))
(check-sat)
