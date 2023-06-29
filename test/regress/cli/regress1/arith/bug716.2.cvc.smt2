; EXIT: 1
; COMMAND-LINE: -i
; EXPECT: (error "The exponent of the POW(^) operator can only be a positive integral constant below 67108864. Exception occurred in:
; EXPECT:   (^ x 67108864)")
(set-logic ALL)
(declare-fun x () Int)
(assert (= (^ x 67108864) 8))
(check-sat-assuming ( (= x 3) ))
