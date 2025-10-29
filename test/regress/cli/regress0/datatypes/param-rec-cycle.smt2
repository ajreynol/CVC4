; EXPECT: unsat
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((List 1)) (
(par ( X ) 
( (cons (head X) (tail (List X))) (nil))
)
))
(declare-fun a () (List Int))
(assert (not ((_ is nil) a)))
(assert (= a (tail a)))
(check-sat)
