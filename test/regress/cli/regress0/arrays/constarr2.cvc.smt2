; COMMAND-LINE: --arrays-exp
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun all1 () (Array Int Int))
(declare-fun all2 () (Array Int Int))
(declare-fun a () Int)
(declare-fun i () Int)
(assert (= all1 ((as const (Array Int Int)) 1)))
(assert (= all2 ((as const (Array Int Int)) 2)))
(assert (= all1 all2))
(check-sat)
