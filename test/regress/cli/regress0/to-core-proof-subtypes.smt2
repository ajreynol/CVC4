; COMMAND-LINE: --check-proofs
; SCRUBBER: grep -E 'unsat'
; EXPECT: unsat
; DISABLE-TESTER: lfsc
; DISABLE-TESTER: cpc
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(assert (> x 0))
(assert (= (/ x x) 2))
(get-timeout-core)
(get-proof)
