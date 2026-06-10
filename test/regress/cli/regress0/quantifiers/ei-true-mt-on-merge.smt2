; COMMAND-LINE: --eager-inst --no-e-matching
; EXPECT: unsat
(set-logic ALL)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(assert (forall ((x Int) (y Int) (z Int)) (! (=> (and (P x y) (P y z)) (Q x z)) :pattern ((P x y) (P y z)))))
(assert (P a b))
(assert (or 
          (and (P c d) (= b c)) 
          (and (P e d) (= b e))
        )
)
(assert (not (Q a d)))
(check-sat)
