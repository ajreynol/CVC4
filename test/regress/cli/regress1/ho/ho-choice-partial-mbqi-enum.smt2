; COMMAND-LINE: --mbqi-enum-choice-grammar --sygus-grammar-ho-partial
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort a 0)
(declare-sort b 0)
(declare-fun r (a b) Bool)
(assert
(and
(exists ((J (-> (-> b Bool) b))) (forall ((P (-> b Bool))) (or (forall ((X b)) (not (P X))) (P (J P)))))
(not (= (forall ((X a)) (exists ((Y b)) (r X Y))) (exists ((F (-> a b))) (forall ((X a)) (r X (F X))))))
))
(set-info :filename SYO268^5)
(check-sat-assuming ( true ))
