; COMMAND-LINE: --decision=justification --jh-rand
; COMMAND-LINE: --decision=justification --jh-rand --seed=2
; COMMAND-LINE: --decision=justification --jh-rand --seed=13
; EXPECT: sat
(set-logic QF_UF)
(set-info :status sat)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(assert (or (and a b) c d))
(assert (or e (not a)))
(assert (=> b (xor c d)))
(assert (ite a (= b c) (= d e)))
(check-sat)
