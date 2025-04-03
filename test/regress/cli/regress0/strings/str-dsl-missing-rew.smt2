; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(assert (or
(not (= (str.len (str.substr (str.++ a b c) 0 (str.len b))) (str.len b)))
(not (= (str.len (str.replace_all a "A" "B")) (str.len a)))
))
(check-sat)
