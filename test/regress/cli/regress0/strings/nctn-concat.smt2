; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(assert (str.contains "ABCDEFG" (str.++ x "C" y "F" z "E" w)))
(check-sat)
