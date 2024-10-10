; COMMAND-LINE: --dump-proofs -o trusted-proof-steps
; SCRUBBER: grep -E '\(trusted-proof-step'
; EXPECT: (trusted-proof-step (= (= 0 1) false) :rule TRUST_THEORY_REWRITE)
(set-logic ALL)
(set-option :dump-proofs true)
(assert (= 0 1))
(check-sat)
