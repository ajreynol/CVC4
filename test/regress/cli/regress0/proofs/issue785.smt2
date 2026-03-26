; COMMAND-LINE: --check-proofs
; EXPECT: sat
; Reduced from cvc5-projects issue #785.
(set-logic ALL)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert
 (and
  (>= (+ (+ (* x2 19)
            (* (+ x1
                  (+ (+ (+ (* (- 19) x0) (* (- 29) x1)) (* 2 x2))
                     (* 26 x3)))
               x2))
         (* (mod (+ (* (- 19) x0)
                    (* (* 19 (* (- (* (- 19) (* (abs 3) x2))) x0))
                       (* (+ (+ (+ (* (- x3 2) x0) (* (- 29) x1)) (* 2 x2))
                             (* (* (- 19) (* 26 x3)) (+ x2 x1)))
                          (+ (+ (* (- 19) x0) (* (- 29) x1)) (* 2 x2)))))
                 (* 19 2))
              x3))
         3)
  (>= (+ (+ (* x2 19)
            (* (+ x1
                  (+ (+ (+ (* (- 19) x0) (* (- 29) x1)) (* 2 x2))
                     (* 26 x3)))
               x2))
         (* (mod (+ (* (- 19) x0)
                    (* (* 19 (* (- (* (- 19) (* (abs 3) x2))) x0))
                       (* (+ (+ (+ (* (- x3 2) x0) (* (- 29) x1)) (* 2 x2))
                             (* (* (- 19) (* 26 x3)) (+ x2 x1)))
                          (+ (+ (* (- 19) x0) (* (- 29) x1)) (* 2 x2)))))
                 (* 19 2))
              x3))
         3)))
(check-sat)
