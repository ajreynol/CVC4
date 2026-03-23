; EXPECT: (error "Cannot handle assertion with term of kind STORE_ALL in this configuration. Try --arrays-exp.")
; EXIT: 1
(set-logic QF_AUFLIA)
(assert (= ((as const (Array Int Int)) 0) ((as const (Array Int Int)) 0)))
(check-sat)
