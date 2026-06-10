; COMMAND-LINE: --dt-split-relevant
; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-fun c () Color)
(declare-fun f (Color) Int)
(assert (distinct (f red) (f c)))
(assert (distinct (f green) (f c)))
(assert (distinct (f blue) (f c)))
(check-sat)
