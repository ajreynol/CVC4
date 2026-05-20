; COMMAND-LINE: --no-cbqi --user-pat=strict --ee-mode=central
; EXPECT: unsat
(set-logic UFDTLIA)
(set-info :status unsat)
(declare-sort Poly 0)
(declare-datatypes ((R 0)) (((mk (a Int)))))
(declare-fun to_poly (R) Poly)
(declare-fun from_poly (Poly) R)
(declare-fun ext_eq (Poly Poly) Bool)
(assert (forall ((x Poly) (y Poly))
  (! (= (= x y) (ext_eq x y)) :pattern ((ext_eq x y)))))
(assert (forall ((x R))
  (! (= x (from_poly (to_poly x))) :pattern ((to_poly x)))))
(declare-const input R)
(declare-const ret R)
(assert
  (not
    (=>
      (= ret (mk (a (from_poly (to_poly input)))))
      (ext_eq (to_poly ret) (to_poly input)))))
(check-sat)
