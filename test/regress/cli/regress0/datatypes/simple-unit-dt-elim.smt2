; COMMAND-LINE: --dt-elim
; EXPECT: sat
(set-logic ALL)
(declare-datatype Unit ((mkUnit (tmp Int))))
(declare-fun f (Unit Int) Int)
(assert (= (f (mkUnit 5) 3) 7))
(declare-fun g () Unit)
(declare-fun h () Unit)
(assert (or (= (tmp g) 6) (= g h)))
(assert (= (tmp h) 5))
(declare-fun u (Int) Unit)
(assert (not (= (u 4) (u 3))))
(declare-fun j () Unit)
(assert (= (f j 3) 7))

(assert (or (= j (mkUnit 100)) (= j (mkUnit 101))))


(declare-datatype BasicUnit ((mkBasicUnit)))

(declare-fun b (BasicUnit) Int)
(assert (= (b mkBasicUnit) 3))

(declare-datatype Nested ((mkNested (tmpn Unit))))
(declare-fun n () Nested)
(assert (= (tmpn n) g))

(check-sat)
