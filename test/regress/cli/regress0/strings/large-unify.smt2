; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (=
(=
(str.++ x "abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd") (str.++ y "dabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"))
(=
(str.++ x "abc") y)
)))
(check-sat)
