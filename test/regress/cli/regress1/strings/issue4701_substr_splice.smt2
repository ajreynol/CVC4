(set-logic QF_SLIA)
(set-info :status sat)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun e () String)
(assert (= e (str.++ b (str.substr a 0 1))))
(assert (= a (str.substr c 0 (str.len e))))
(assert (= "a" b))
(assert (= (str.++ b a) (str.replace c e a)))
(check-sat)
