; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (> a 0))
(get-abduct A (> b 1))
