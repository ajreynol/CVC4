; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (not (= (str.len (str.replace_all x "A" "B")) (str.len x))))
(check-sat)
