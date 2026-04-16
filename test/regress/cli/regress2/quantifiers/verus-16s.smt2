(set-logic ALL)

;; Prelude

;; AIR prelude
(declare-sort %%Function%% 0)

(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
    :qid prelude_fuel_defaults
))))
(declare-sort Char 0)
(declare-fun char%from_unicode (Int) Char)
(declare-fun char%to_unicode (Char) Int)
(declare-sort StrSlice 0)
(declare-fun str%strslice_is_ascii (StrSlice) Bool)
(declare-fun str%strslice_len (StrSlice) Int)
(declare-fun str%strslice_get_char (StrSlice Int) Char)
(declare-fun str%new_strlit (Int) StrSlice)
(declare-fun str%from_strlit (StrSlice) Int)
(declare-datatypes ((fndef 0)) (((fndef_singleton))))
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun F (fndef) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun %F (Poly) fndef)
(declare-fun S (StrSlice) Poly)
(declare-fun %S (Poly) StrSlice)
(declare-fun C (Char) Poly)
(declare-fun %C (Poly) Char)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const STRSLICE Type)
(declare-const CHAR Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-fun REF (Dcr) Dcr)
(declare-fun MUT_REF (Dcr) Dcr)
(declare-fun BOX (Dcr) Dcr)
(declare-fun RC (Dcr) Dcr)
(declare-fun ARC (Dcr) Dcr)
(declare-fun GHOST (Dcr) Dcr)
(declare-fun TRACKED (Dcr) Dcr)
(declare-fun NEVER (Dcr) Dcr)
(declare-fun ARRAY (Dcr Type Dcr Type) Type)
(declare-fun SLICE (Dcr Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(assert
 (forall ((i Int)) (!
   (= i (const_int (CONST_INT i)))
   :pattern ((CONST_INT i))
   :qid prelude_type_id_const_int
)))
(assert
 (forall ((b Bool)) (!
   (has_type (B b) BOOL)
   :pattern ((has_type (B b) BOOL))
   :qid prelude_has_type_bool
)))
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid prelude_as_type
)))
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid prelude_mk_fun
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid prelude_unbox_box_bool
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid prelude_box_unbox_bool
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid prelude_box_unbox_nat
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_box_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_box_unbox_sint
)))
(assert
 (forall ((x Int)) (!
   (= (str%from_strlit (str%new_strlit x)) x)
   :pattern ((str%new_strlit x))
   :qid prelude_strlit_injective
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x STRSLICE)
    (= x (S (%S x)))
   )
   :pattern ((has_type x STRSLICE))
   :qid prelude_box_unbox_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (= x (%S (S x)))
   :pattern ((S x))
   :qid prelude_unbox_box_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (has_type (S x) STRSLICE)
   :pattern ((has_type (S x) STRSLICE))
   :qid prelude_has_type_strslice
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
)))
(declare-const SZ Int)
(assert
 (or
  (= SZ 32)
  (= SZ 64)
))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 8) 256)
)
(assert
 (= (uHi 16) 65536)
)
(assert
 (= (uHi 32) 4294967296)
)
(assert
 (= (uHi 64) 18446744073709551616)
)
(assert
 (= (uHi 128) (+ 1 340282366920938463463374607431768211455))
)
(assert
 (= (iLo 8) (- 128))
)
(assert
 (= (iLo 16) (- 32768))
)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iLo 64) (- 9223372036854775808))
)
(assert
 (= (iLo 128) (- 170141183460469231731687303715884105728))
)
(assert
 (= (iHi 8) 128)
)
(assert
 (= (iHi 16) 32768)
)
(assert
 (= (iHi 32) 2147483648)
)
(assert
 (= (iHi 64) 9223372036854775808)
)
(assert
 (= (iHi 128) 170141183460469231731687303715884105728)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid prelude_nat_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid prelude_u_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= (iLo bits) (iClip bits i))
    (< (iClip bits i) (iHi bits))
    (=>
     (and
      (<= (iLo bits) i)
      (< i (iHi bits))
     )
     (= i (iClip bits i))
   ))
   :pattern ((iClip bits i))
   :qid prelude_i_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid prelude_i_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid prelude_has_type_nat
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid prelude_has_type_sint
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid prelude_unbox_int
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_unbox_sint
)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Add x y) (+ x y))
   :pattern ((Add x y))
   :qid prelude_add
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Sub x y) (- x y))
   :pattern ((Sub x y))
   :qid prelude_sub
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid prelude_eucmod
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (<= 0 y)
    )
    (<= 0 (Mul x y))
   )
   :pattern ((Mul x y))
   :qid prelude_mul_nats
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucDiv x y))
     (<= (EucDiv x y) x)
   ))
   :pattern ((EucDiv x y))
   :qid prelude_div_unsigned_in_bounds
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucMod x y))
     (< (EucMod x y) y)
   ))
   :pattern ((EucMod x y))
   :qid prelude_mod_unsigned_in_bounds
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (C (%C x)))
   )
   :pattern ((has_type x CHAR))
   :qid prelude_box_unbox_char
)))
(assert
 (forall ((x Char)) (!
   (= x (%C (C x)))
   :pattern ((C x))
   :qid prelude_unbox_box_char
)))
(assert
 (forall ((x Char)) (!
   (has_type (C x) CHAR)
   :pattern ((has_type (C x) CHAR))
   :qid prelude_has_type_char
)))
(assert
 (forall ((x Int)) (!
   (=>
    (and
     (<= 0 x)
     (< x (uHi 32))
    )
    (= x (char%to_unicode (char%from_unicode x)))
   )
   :pattern ((char%from_unicode x))
   :qid prelude_char_injective
)))
(assert
 (forall ((c Char)) (!
   (and
    (<= 0 (char%to_unicode c))
    (< (char%to_unicode c) (uHi 32))
   )
   :pattern ((char%to_unicode c))
   :qid prelude_to_unicode_bounds
)))
(declare-fun uintxor (Int Poly Poly) Int)
(declare-fun uintand (Int Poly Poly) Int)
(declare-fun uintor (Int Poly Poly) Int)
(declare-fun uintshr (Int Poly Poly) Int)
(declare-fun uintshl (Int Poly Poly) Int)
(declare-fun uintnot (Int Poly) Int)
(declare-fun singular_mod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (not (= y 0))
    (= (EucMod x y) (singular_mod x y))
   )
   :pattern ((singular_mod x y))
   :qid prelude_singularmod
)))
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int cur prev otherwise))
   :qid prelude_check_decrease_int
)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert
 (forall ((cur Poly) (prev Poly) (otherwise Bool)) (!
   (= (check_decrease_height cur prev otherwise) (or
     (height_lt (height cur) (height prev))
     (and
      (= (height cur) (height prev))
      otherwise
   )))
   :pattern ((check_decrease_height cur prev otherwise))
   :qid prelude_check_decrease_height
)))
(declare-fun partial-order (Height Height) Bool)
(assert
 (forall ((x Height)) (partial-order x x))
)
(assert
 (forall ((x Height) (y Height)) (=>
   (and
    (partial-order x y)
    (partial-order y x)
   )
   (= x y)
)))
(assert
 (forall ((x Height) (y Height) (z Height)) (=>
   (and
    (partial-order x y)
    (partial-order y z)
   )
   (partial-order x z)
)))
(assert
 (forall ((x Height) (y Height)) (= (height_lt x y) (and
    (partial-order x y)
    (not (= x y))
))))

;; MODULE 'module net_sht_v, function lib::net_sht_v::sht_marshal_data_injective'

;; Fuel
(declare-const fuel%vstd!std_specs.vec.impl&%2.spec_len. FuelId)
(declare-const fuel%vstd!std_specs.vec.impl&%2.spec_index. FuelId)
(declare-const fuel%vstd!map.impl&%0.spec_index. FuelId)
(declare-const fuel%vstd!map_lib.impl&%0.contains_pair. FuelId)
(declare-const fuel%vstd!seq.impl&%0.spec_index. FuelId)
(declare-const fuel%vstd!seq.impl&%0.spec_add. FuelId)
(declare-const fuel%vstd!seq.Seq.last. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.add_empty_left. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.add_empty_right. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.push_distributes_over_add. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.contains. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.drop_last. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.to_set. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.fold_left. FuelId)
(declare-const fuel%vstd!set.impl&%0.choose. FuelId)
(declare-const fuel%vstd!view.impl&%0.view. FuelId)
(declare-const fuel%vstd!view.impl&%2.view. FuelId)
(declare-const fuel%vstd!view.impl&%4.view. FuelId)
(declare-const fuel%vstd!view.impl&%6.view. FuelId)
(declare-const fuel%vstd!view.impl&%8.view. FuelId)
(declare-const fuel%vstd!view.impl&%10.view. FuelId)
(declare-const fuel%vstd!view.impl&%12.view. FuelId)
(declare-const fuel%vstd!view.impl&%18.view. FuelId)
(declare-const fuel%vstd!view.impl&%22.view. FuelId)
(declare-const fuel%vstd!view.impl&%38.view. FuelId)
(declare-const fuel%lib!cmessage_v.optional_value_view. FuelId)
(declare-const fuel%lib!cmessage_v.impl&%1.view. FuelId)
(declare-const fuel%lib!cmessage_v.impl&%2.view. FuelId)
(declare-const fuel%lib!cmessage_v.impl&%6.view_equal. FuelId)
(declare-const fuel%lib!cmessage_v.impl&%6.is_marshalable. FuelId)
(declare-const fuel%lib!cmessage_v.impl&%6.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%2.view_equal. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%2.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%2.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%3.view_equal. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%3.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%3.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%4.view_equal. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%4.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%4.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.
 FuelId
)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%6.view_equal. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%6.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%6.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%7.forward_bijection_for_view_equality_do_not_use_for_anything_else.
 FuelId
)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%8.view_equal. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%8.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%8.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.
 FuelId
)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%10.view_equal. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%10.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_ironsht_specific_v.impl&%10.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_v.impl&%0.view_equal. FuelId)
(declare-const fuel%lib!marshal_v.impl&%0.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_v.impl&%0.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_v.impl&%1.view_equal. FuelId)
(declare-const fuel%lib!marshal_v.impl&%1.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_v.impl&%1.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_v.impl&%2.view_equal. FuelId)
(declare-const fuel%lib!marshal_v.impl&%2.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_v.impl&%2.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_v.impl&%3.view_equal. FuelId)
(declare-const fuel%lib!marshal_v.impl&%3.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_v.impl&%3.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_v.impl&%4.view_equal. FuelId)
(declare-const fuel%lib!marshal_v.impl&%4.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_v.impl&%4.ghost_serialize. FuelId)
(declare-const fuel%lib!marshal_v.impl&%5.view_equal. FuelId)
(declare-const fuel%lib!marshal_v.impl&%5.is_marshalable. FuelId)
(declare-const fuel%lib!marshal_v.impl&%5.ghost_serialize. FuelId)
(declare-const fuel%lib!hashmap_t.impl&%1.view. FuelId)
(declare-const fuel%lib!hashmap_t.ckeykvlt. FuelId)
(declare-const fuel%lib!hashmap_t.spec_sorted_keys. FuelId)
(declare-const fuel%lib!io_t.impl&%5.view. FuelId)
(assert
 (distinct fuel%vstd!std_specs.vec.impl&%2.spec_len. fuel%vstd!std_specs.vec.impl&%2.spec_index.
  fuel%vstd!map.impl&%0.spec_index. fuel%vstd!map_lib.impl&%0.contains_pair. fuel%vstd!seq.impl&%0.spec_index.
  fuel%vstd!seq.impl&%0.spec_add. fuel%vstd!seq.Seq.last. fuel%vstd!seq_lib.impl&%0.add_empty_left.
  fuel%vstd!seq_lib.impl&%0.add_empty_right. fuel%vstd!seq_lib.impl&%0.push_distributes_over_add.
  fuel%vstd!seq_lib.impl&%0.contains. fuel%vstd!seq_lib.impl&%0.drop_last. fuel%vstd!seq_lib.impl&%0.to_set.
  fuel%vstd!seq_lib.impl&%0.fold_left. fuel%vstd!set.impl&%0.choose. fuel%vstd!view.impl&%0.view.
  fuel%vstd!view.impl&%2.view. fuel%vstd!view.impl&%4.view. fuel%vstd!view.impl&%6.view.
  fuel%vstd!view.impl&%8.view. fuel%vstd!view.impl&%10.view. fuel%vstd!view.impl&%12.view.
  fuel%vstd!view.impl&%18.view. fuel%vstd!view.impl&%22.view. fuel%vstd!view.impl&%38.view.
  fuel%lib!cmessage_v.optional_value_view. fuel%lib!cmessage_v.impl&%1.view. fuel%lib!cmessage_v.impl&%2.view.
  fuel%lib!cmessage_v.impl&%6.view_equal. fuel%lib!cmessage_v.impl&%6.is_marshalable.
  fuel%lib!cmessage_v.impl&%6.ghost_serialize. fuel%lib!marshal_ironsht_specific_v.impl&%2.view_equal.
  fuel%lib!marshal_ironsht_specific_v.impl&%2.is_marshalable. fuel%lib!marshal_ironsht_specific_v.impl&%2.ghost_serialize.
  fuel%lib!marshal_ironsht_specific_v.impl&%3.view_equal. fuel%lib!marshal_ironsht_specific_v.impl&%3.is_marshalable.
  fuel%lib!marshal_ironsht_specific_v.impl&%3.ghost_serialize. fuel%lib!marshal_ironsht_specific_v.impl&%4.view_equal.
  fuel%lib!marshal_ironsht_specific_v.impl&%4.is_marshalable. fuel%lib!marshal_ironsht_specific_v.impl&%4.ghost_serialize.
  fuel%lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.
  fuel%lib!marshal_ironsht_specific_v.impl&%6.view_equal. fuel%lib!marshal_ironsht_specific_v.impl&%6.is_marshalable.
  fuel%lib!marshal_ironsht_specific_v.impl&%6.ghost_serialize. fuel%lib!marshal_ironsht_specific_v.impl&%7.forward_bijection_for_view_equality_do_not_use_for_anything_else.
  fuel%lib!marshal_ironsht_specific_v.impl&%8.view_equal. fuel%lib!marshal_ironsht_specific_v.impl&%8.is_marshalable.
  fuel%lib!marshal_ironsht_specific_v.impl&%8.ghost_serialize. fuel%lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.
  fuel%lib!marshal_ironsht_specific_v.impl&%10.view_equal. fuel%lib!marshal_ironsht_specific_v.impl&%10.is_marshalable.
  fuel%lib!marshal_ironsht_specific_v.impl&%10.ghost_serialize. fuel%lib!marshal_v.impl&%0.view_equal.
  fuel%lib!marshal_v.impl&%0.is_marshalable. fuel%lib!marshal_v.impl&%0.ghost_serialize.
  fuel%lib!marshal_v.impl&%1.view_equal. fuel%lib!marshal_v.impl&%1.is_marshalable.
  fuel%lib!marshal_v.impl&%1.ghost_serialize. fuel%lib!marshal_v.impl&%2.view_equal.
  fuel%lib!marshal_v.impl&%2.is_marshalable. fuel%lib!marshal_v.impl&%2.ghost_serialize.
  fuel%lib!marshal_v.impl&%3.view_equal. fuel%lib!marshal_v.impl&%3.is_marshalable.
  fuel%lib!marshal_v.impl&%3.ghost_serialize. fuel%lib!marshal_v.impl&%4.view_equal.
  fuel%lib!marshal_v.impl&%4.is_marshalable. fuel%lib!marshal_v.impl&%4.ghost_serialize.
  fuel%lib!marshal_v.impl&%5.view_equal. fuel%lib!marshal_v.impl&%5.is_marshalable.
  fuel%lib!marshal_v.impl&%5.ghost_serialize. fuel%lib!hashmap_t.impl&%1.view. fuel%lib!hashmap_t.ckeykvlt.
  fuel%lib!hashmap_t.spec_sorted_keys. fuel%lib!io_t.impl&%5.view.
))

;; Associated-Type-Decls
(declare-fun proj%%vstd!view.View./V (Dcr Type) Dcr)
(declare-fun proj%vstd!view.View./V (Dcr Type) Type)

;; Datatypes
(declare-sort alloc!alloc.Global. 0)
(declare-sort alloc!vec.Vec<u8./alloc!alloc.Global.>. 0)
(declare-sort alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. 0)
(declare-sort lib!hashmap_t.CKeyHashMap. 0)
(declare-sort vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. 0)
(declare-sort vstd!seq.Seq<u8.>. 0)
(declare-sort vstd!seq.Seq<lib!hashmap_t.CKeyKV.>. 0)
(declare-sort vstd!set.Set<lib!keys_t.SHTKey.>. 0)
(declare-datatypes ((core!option.Option. 0) (lib!cmessage_v.CMessage. 0) (lib!cmessage_v.CPacket.
   0
  ) (lib!cmessage_v.CSingleMessage. 0) (lib!net_sht_v.ReceiveResult. 0) (lib!abstract_end_point_t.AbstractEndPoint.
   0
  ) (lib!hashmap_t.CKeyKV. 0) (lib!io_t.EndPoint. 0) (lib!keys_t.KeyIterator. 0) (lib!keys_t.KeyRange.
   0
  ) (lib!keys_t.SHTKey. 0) (lib!message_t.Message. 0) (lib!single_message_t.SingleMessage.
   0
  ) (tuple%0. 0) (tuple%2. 0)
 ) (((core!option.Option./None) (core!option.Option./Some (core!option.Option./Some/?0
     Poly
   ))
  ) ((lib!cmessage_v.CMessage./GetRequest (lib!cmessage_v.CMessage./GetRequest/?k lib!keys_t.SHTKey.))
   (lib!cmessage_v.CMessage./SetRequest (lib!cmessage_v.CMessage./SetRequest/?k lib!keys_t.SHTKey.)
    (lib!cmessage_v.CMessage./SetRequest/?v core!option.Option.)
   ) (lib!cmessage_v.CMessage./Reply (lib!cmessage_v.CMessage./Reply/?k lib!keys_t.SHTKey.)
    (lib!cmessage_v.CMessage./Reply/?v core!option.Option.)
   ) (lib!cmessage_v.CMessage./Redirect (lib!cmessage_v.CMessage./Redirect/?k lib!keys_t.SHTKey.)
    (lib!cmessage_v.CMessage./Redirect/?id lib!io_t.EndPoint.)
   ) (lib!cmessage_v.CMessage./Shard (lib!cmessage_v.CMessage./Shard/?kr lib!keys_t.KeyRange.)
    (lib!cmessage_v.CMessage./Shard/?recipient lib!io_t.EndPoint.)
   ) (lib!cmessage_v.CMessage./Delegate (lib!cmessage_v.CMessage./Delegate/?range lib!keys_t.KeyRange.)
    (lib!cmessage_v.CMessage./Delegate/?h lib!hashmap_t.CKeyHashMap.)
   )
  ) ((lib!cmessage_v.CPacket./CPacket (lib!cmessage_v.CPacket./CPacket/?dst lib!io_t.EndPoint.)
    (lib!cmessage_v.CPacket./CPacket/?src lib!io_t.EndPoint.) (lib!cmessage_v.CPacket./CPacket/?msg
     lib!cmessage_v.CSingleMessage.
   ))
  ) ((lib!cmessage_v.CSingleMessage./Message (lib!cmessage_v.CSingleMessage./Message/?seqno
     Int
    ) (lib!cmessage_v.CSingleMessage./Message/?dst lib!io_t.EndPoint.) (lib!cmessage_v.CSingleMessage./Message/?m
     lib!cmessage_v.CMessage.
    )
   ) (lib!cmessage_v.CSingleMessage./Ack (lib!cmessage_v.CSingleMessage./Ack/?ack_seqno
     Int
    )
   ) (lib!cmessage_v.CSingleMessage./InvalidMessage)
  ) ((lib!net_sht_v.ReceiveResult./Fail) (lib!net_sht_v.ReceiveResult./Timeout) (lib!net_sht_v.ReceiveResult./Packet
    (lib!net_sht_v.ReceiveResult./Packet/?cpacket lib!cmessage_v.CPacket.)
   )
  ) ((lib!abstract_end_point_t.AbstractEndPoint./AbstractEndPoint (lib!abstract_end_point_t.AbstractEndPoint./AbstractEndPoint/?id
     vstd!seq.Seq<u8.>.
   ))
  ) ((lib!hashmap_t.CKeyKV./CKeyKV (lib!hashmap_t.CKeyKV./CKeyKV/?k lib!keys_t.SHTKey.)
    (lib!hashmap_t.CKeyKV./CKeyKV/?v alloc!vec.Vec<u8./alloc!alloc.Global.>.)
   )
  ) ((lib!io_t.EndPoint./EndPoint (lib!io_t.EndPoint./EndPoint/?id alloc!vec.Vec<u8./alloc!alloc.Global.>.)))
  ((lib!keys_t.KeyIterator./KeyIterator (lib!keys_t.KeyIterator./KeyIterator/?k core!option.Option.)))
  ((lib!keys_t.KeyRange./KeyRange (lib!keys_t.KeyRange./KeyRange/?lo lib!keys_t.KeyIterator.)
    (lib!keys_t.KeyRange./KeyRange/?hi lib!keys_t.KeyIterator.)
   )
  ) ((lib!keys_t.SHTKey./SHTKey (lib!keys_t.SHTKey./SHTKey/?ukey Int))) ((lib!message_t.Message./GetRequest
    (lib!message_t.Message./GetRequest/?key lib!keys_t.SHTKey.)
   ) (lib!message_t.Message./SetRequest (lib!message_t.Message./SetRequest/?key lib!keys_t.SHTKey.)
    (lib!message_t.Message./SetRequest/?value core!option.Option.)
   ) (lib!message_t.Message./Reply (lib!message_t.Message./Reply/?key lib!keys_t.SHTKey.)
    (lib!message_t.Message./Reply/?value core!option.Option.)
   ) (lib!message_t.Message./Redirect (lib!message_t.Message./Redirect/?key lib!keys_t.SHTKey.)
    (lib!message_t.Message./Redirect/?id lib!abstract_end_point_t.AbstractEndPoint.)
   ) (lib!message_t.Message./Shard (lib!message_t.Message./Shard/?range lib!keys_t.KeyRange.)
    (lib!message_t.Message./Shard/?recipient lib!abstract_end_point_t.AbstractEndPoint.)
   ) (lib!message_t.Message./Delegate (lib!message_t.Message./Delegate/?range lib!keys_t.KeyRange.)
    (lib!message_t.Message./Delegate/?h vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.)
   )
  ) ((lib!single_message_t.SingleMessage./Message (lib!single_message_t.SingleMessage./Message/?seqno
     Int
    ) (lib!single_message_t.SingleMessage./Message/?dst lib!abstract_end_point_t.AbstractEndPoint.)
    (lib!single_message_t.SingleMessage./Message/?m Poly)
   ) (lib!single_message_t.SingleMessage./Ack (lib!single_message_t.SingleMessage./Ack/?ack_seqno
     Int
    )
   ) (lib!single_message_t.SingleMessage./InvalidMessage)
  ) ((tuple%0./tuple%0)) ((tuple%2./tuple%2 (tuple%2./tuple%2/?0 Poly) (tuple%2./tuple%2/?1
     Poly
)))))
(declare-fun core!option.Option./Some/0 (core!option.Option.) Poly)
(declare-fun lib!cmessage_v.CMessage./GetRequest/k (lib!cmessage_v.CMessage.) lib!keys_t.SHTKey.)
(declare-fun lib!cmessage_v.CMessage./SetRequest/k (lib!cmessage_v.CMessage.) lib!keys_t.SHTKey.)
(declare-fun lib!cmessage_v.CMessage./SetRequest/v (lib!cmessage_v.CMessage.) core!option.Option.)
(declare-fun lib!cmessage_v.CMessage./Reply/k (lib!cmessage_v.CMessage.) lib!keys_t.SHTKey.)
(declare-fun lib!cmessage_v.CMessage./Reply/v (lib!cmessage_v.CMessage.) core!option.Option.)
(declare-fun lib!cmessage_v.CMessage./Redirect/k (lib!cmessage_v.CMessage.) lib!keys_t.SHTKey.)
(declare-fun lib!cmessage_v.CMessage./Redirect/id (lib!cmessage_v.CMessage.) lib!io_t.EndPoint.)
(declare-fun lib!cmessage_v.CMessage./Shard/kr (lib!cmessage_v.CMessage.) lib!keys_t.KeyRange.)
(declare-fun lib!cmessage_v.CMessage./Shard/recipient (lib!cmessage_v.CMessage.) lib!io_t.EndPoint.)
(declare-fun lib!cmessage_v.CMessage./Delegate/range (lib!cmessage_v.CMessage.) lib!keys_t.KeyRange.)
(declare-fun lib!cmessage_v.CMessage./Delegate/h (lib!cmessage_v.CMessage.) lib!hashmap_t.CKeyHashMap.)
(declare-fun lib!cmessage_v.CPacket./CPacket/dst (lib!cmessage_v.CPacket.) lib!io_t.EndPoint.)
(declare-fun lib!cmessage_v.CPacket./CPacket/src (lib!cmessage_v.CPacket.) lib!io_t.EndPoint.)
(declare-fun lib!cmessage_v.CPacket./CPacket/msg (lib!cmessage_v.CPacket.) lib!cmessage_v.CSingleMessage.)
(declare-fun lib!cmessage_v.CSingleMessage./Message/seqno (lib!cmessage_v.CSingleMessage.)
 Int
)
(declare-fun lib!cmessage_v.CSingleMessage./Message/dst (lib!cmessage_v.CSingleMessage.)
 lib!io_t.EndPoint.
)
(declare-fun lib!cmessage_v.CSingleMessage./Message/m (lib!cmessage_v.CSingleMessage.)
 lib!cmessage_v.CMessage.
)
(declare-fun lib!cmessage_v.CSingleMessage./Ack/ack_seqno (lib!cmessage_v.CSingleMessage.)
 Int
)
(declare-fun lib!net_sht_v.ReceiveResult./Packet/cpacket (lib!net_sht_v.ReceiveResult.)
 lib!cmessage_v.CPacket.
)
(declare-fun lib!abstract_end_point_t.AbstractEndPoint./AbstractEndPoint/id (lib!abstract_end_point_t.AbstractEndPoint.)
 vstd!seq.Seq<u8.>.
)
(declare-fun lib!hashmap_t.CKeyKV./CKeyKV/k (lib!hashmap_t.CKeyKV.) lib!keys_t.SHTKey.)
(declare-fun lib!hashmap_t.CKeyKV./CKeyKV/v (lib!hashmap_t.CKeyKV.) alloc!vec.Vec<u8./alloc!alloc.Global.>.)
(declare-fun lib!io_t.EndPoint./EndPoint/id (lib!io_t.EndPoint.) alloc!vec.Vec<u8./alloc!alloc.Global.>.)
(declare-fun lib!keys_t.KeyIterator./KeyIterator/k (lib!keys_t.KeyIterator.) core!option.Option.)
(declare-fun lib!keys_t.KeyRange./KeyRange/lo (lib!keys_t.KeyRange.) lib!keys_t.KeyIterator.)
(declare-fun lib!keys_t.KeyRange./KeyRange/hi (lib!keys_t.KeyRange.) lib!keys_t.KeyIterator.)
(declare-fun lib!keys_t.SHTKey./SHTKey/ukey (lib!keys_t.SHTKey.) Int)
(declare-fun lib!message_t.Message./GetRequest/key (lib!message_t.Message.) lib!keys_t.SHTKey.)
(declare-fun lib!message_t.Message./SetRequest/key (lib!message_t.Message.) lib!keys_t.SHTKey.)
(declare-fun lib!message_t.Message./SetRequest/value (lib!message_t.Message.) core!option.Option.)
(declare-fun lib!message_t.Message./Reply/key (lib!message_t.Message.) lib!keys_t.SHTKey.)
(declare-fun lib!message_t.Message./Reply/value (lib!message_t.Message.) core!option.Option.)
(declare-fun lib!message_t.Message./Redirect/key (lib!message_t.Message.) lib!keys_t.SHTKey.)
(declare-fun lib!message_t.Message./Redirect/id (lib!message_t.Message.) lib!abstract_end_point_t.AbstractEndPoint.)
(declare-fun lib!message_t.Message./Shard/range (lib!message_t.Message.) lib!keys_t.KeyRange.)
(declare-fun lib!message_t.Message./Shard/recipient (lib!message_t.Message.) lib!abstract_end_point_t.AbstractEndPoint.)
(declare-fun lib!message_t.Message./Delegate/range (lib!message_t.Message.) lib!keys_t.KeyRange.)
(declare-fun lib!message_t.Message./Delegate/h (lib!message_t.Message.) vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.)
(declare-fun lib!single_message_t.SingleMessage./Message/seqno (lib!single_message_t.SingleMessage.)
 Int
)
(declare-fun lib!single_message_t.SingleMessage./Message/dst (lib!single_message_t.SingleMessage.)
 lib!abstract_end_point_t.AbstractEndPoint.
)
(declare-fun lib!single_message_t.SingleMessage./Message/m (lib!single_message_t.SingleMessage.)
 Poly
)
(declare-fun lib!single_message_t.SingleMessage./Ack/ack_seqno (lib!single_message_t.SingleMessage.)
 Int
)
(declare-fun tuple%2./tuple%2/0 (tuple%2.) Poly)
(declare-fun tuple%2./tuple%2/1 (tuple%2.) Poly)
(declare-fun TYPE%fun%1. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%fun%2. (Dcr Type Dcr Type Dcr Type) Type)
(declare-fun TYPE%core!option.Option. (Dcr Type) Type)
(declare-fun TYPE%alloc!vec.Vec. (Dcr Type Dcr Type) Type)
(declare-const TYPE%alloc!alloc.Global. Type)
(declare-fun TYPE%vstd!map.Map. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%vstd!seq.Seq. (Dcr Type) Type)
(declare-fun TYPE%vstd!set.Set. (Dcr Type) Type)
(declare-const TYPE%lib!cmessage_v.CMessage. Type)
(declare-const TYPE%lib!cmessage_v.CPacket. Type)
(declare-const TYPE%lib!cmessage_v.CSingleMessage. Type)
(declare-const TYPE%lib!net_sht_v.ReceiveResult. Type)
(declare-const TYPE%lib!abstract_end_point_t.AbstractEndPoint. Type)
(declare-const TYPE%lib!hashmap_t.CKeyHashMap. Type)
(declare-const TYPE%lib!hashmap_t.CKeyKV. Type)
(declare-const TYPE%lib!io_t.EndPoint. Type)
(declare-fun TYPE%lib!keys_t.KeyIterator. (Dcr Type) Type)
(declare-fun TYPE%lib!keys_t.KeyRange. (Dcr Type) Type)
(declare-const TYPE%lib!keys_t.SHTKey. Type)
(declare-const TYPE%lib!message_t.Message. Type)
(declare-fun TYPE%lib!single_message_t.SingleMessage. (Dcr Type) Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun TYPE%tuple%2. (Dcr Type Dcr Type) Type)
(declare-fun Poly%fun%1. (%%Function%%) Poly)
(declare-fun %Poly%fun%1. (Poly) %%Function%%)
(declare-fun Poly%fun%2. (%%Function%%) Poly)
(declare-fun %Poly%fun%2. (Poly) %%Function%%)
(declare-fun Poly%alloc!alloc.Global. (alloc!alloc.Global.) Poly)
(declare-fun %Poly%alloc!alloc.Global. (Poly) alloc!alloc.Global.)
(declare-fun Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (alloc!vec.Vec<u8./alloc!alloc.Global.>.)
 Poly
)
(declare-fun %Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (Poly) alloc!vec.Vec<u8./alloc!alloc.Global.>.)
(declare-fun Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.)
 Poly
)
(declare-fun %Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (Poly)
 alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
)
(declare-fun Poly%lib!hashmap_t.CKeyHashMap. (lib!hashmap_t.CKeyHashMap.) Poly)
(declare-fun %Poly%lib!hashmap_t.CKeyHashMap. (Poly) lib!hashmap_t.CKeyHashMap.)
(declare-fun Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. (vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.)
 Poly
)
(declare-fun %Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. (Poly) vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.)
(declare-fun Poly%vstd!seq.Seq<u8.>. (vstd!seq.Seq<u8.>.) Poly)
(declare-fun %Poly%vstd!seq.Seq<u8.>. (Poly) vstd!seq.Seq<u8.>.)
(declare-fun Poly%vstd!seq.Seq<lib!hashmap_t.CKeyKV.>. (vstd!seq.Seq<lib!hashmap_t.CKeyKV.>.)
 Poly
)
(declare-fun %Poly%vstd!seq.Seq<lib!hashmap_t.CKeyKV.>. (Poly) vstd!seq.Seq<lib!hashmap_t.CKeyKV.>.)
(declare-fun Poly%vstd!set.Set<lib!keys_t.SHTKey.>. (vstd!set.Set<lib!keys_t.SHTKey.>.)
 Poly
)
(declare-fun %Poly%vstd!set.Set<lib!keys_t.SHTKey.>. (Poly) vstd!set.Set<lib!keys_t.SHTKey.>.)
(declare-fun Poly%core!option.Option. (core!option.Option.) Poly)
(declare-fun %Poly%core!option.Option. (Poly) core!option.Option.)
(declare-fun Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage.) Poly)
(declare-fun %Poly%lib!cmessage_v.CMessage. (Poly) lib!cmessage_v.CMessage.)
(declare-fun Poly%lib!cmessage_v.CPacket. (lib!cmessage_v.CPacket.) Poly)
(declare-fun %Poly%lib!cmessage_v.CPacket. (Poly) lib!cmessage_v.CPacket.)
(declare-fun Poly%lib!cmessage_v.CSingleMessage. (lib!cmessage_v.CSingleMessage.)
 Poly
)
(declare-fun %Poly%lib!cmessage_v.CSingleMessage. (Poly) lib!cmessage_v.CSingleMessage.)
(declare-fun Poly%lib!net_sht_v.ReceiveResult. (lib!net_sht_v.ReceiveResult.) Poly)
(declare-fun %Poly%lib!net_sht_v.ReceiveResult. (Poly) lib!net_sht_v.ReceiveResult.)
(declare-fun Poly%lib!abstract_end_point_t.AbstractEndPoint. (lib!abstract_end_point_t.AbstractEndPoint.)
 Poly
)
(declare-fun %Poly%lib!abstract_end_point_t.AbstractEndPoint. (Poly) lib!abstract_end_point_t.AbstractEndPoint.)
(declare-fun Poly%lib!hashmap_t.CKeyKV. (lib!hashmap_t.CKeyKV.) Poly)
(declare-fun %Poly%lib!hashmap_t.CKeyKV. (Poly) lib!hashmap_t.CKeyKV.)
(declare-fun Poly%lib!io_t.EndPoint. (lib!io_t.EndPoint.) Poly)
(declare-fun %Poly%lib!io_t.EndPoint. (Poly) lib!io_t.EndPoint.)
(declare-fun Poly%lib!keys_t.KeyIterator. (lib!keys_t.KeyIterator.) Poly)
(declare-fun %Poly%lib!keys_t.KeyIterator. (Poly) lib!keys_t.KeyIterator.)
(declare-fun Poly%lib!keys_t.KeyRange. (lib!keys_t.KeyRange.) Poly)
(declare-fun %Poly%lib!keys_t.KeyRange. (Poly) lib!keys_t.KeyRange.)
(declare-fun Poly%lib!keys_t.SHTKey. (lib!keys_t.SHTKey.) Poly)
(declare-fun %Poly%lib!keys_t.SHTKey. (Poly) lib!keys_t.SHTKey.)
(declare-fun Poly%lib!message_t.Message. (lib!message_t.Message.) Poly)
(declare-fun %Poly%lib!message_t.Message. (Poly) lib!message_t.Message.)
(declare-fun Poly%lib!single_message_t.SingleMessage. (lib!single_message_t.SingleMessage.)
 Poly
)
(declare-fun %Poly%lib!single_message_t.SingleMessage. (Poly) lib!single_message_t.SingleMessage.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(declare-fun Poly%tuple%2. (tuple%2.) Poly)
(declare-fun %Poly%tuple%2. (Poly) tuple%2.)
(assert
 (forall ((x %%Function%%)) (!
   (= x (%Poly%fun%1. (Poly%fun%1. x)))
   :pattern ((Poly%fun%1. x))
   :qid internal_crate__fun__1_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
    (= x (Poly%fun%1. (%Poly%fun%1. x)))
   )
   :pattern ((has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__fun__1_unbox_axiom_definition
)))
(declare-fun %%apply%%0 (%%Function%% Poly) Poly)
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x %%Function%%)) (!
   (=>
    (forall ((T%0 Poly)) (!
      (=>
       (has_type T%0 T%0&)
       (has_type (%%apply%%0 x T%0) T%1&)
      )
      :pattern ((has_type (%%apply%%0 x T%0) T%1&))
      :qid internal_crate__fun__1_constructor_inner_definition
    ))
    (has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
   )
   :pattern ((has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__fun__1_constructor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%0 Poly) (x %%Function%%))
  (!
   (=>
    (and
     (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type T%0 T%0&)
    )
    (has_type (%%apply%%0 x T%0) T%1&)
   )
   :pattern ((%%apply%%0 x T%0) (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&.
      T%1&
   )))
   :qid internal_crate__fun__1_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%0 Poly) (x %%Function%%))
  (!
   (=>
    (and
     (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type T%0 T%0&)
    )
    (height_lt (height (%%apply%%0 x T%0)) (height (fun_from_recursive_field (Poly%fun%1.
        (mk_fun x)
   )))))
   :pattern ((height (%%apply%%0 x T%0)) (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_crate__fun__1_height_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (deep Bool) (x Poly) (y Poly))
  (!
   (=>
    (and
     (has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type y (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (forall ((T%0 Poly)) (!
       (=>
        (has_type T%0 T%0&)
        (ext_eq deep T%1& (%%apply%%0 (%Poly%fun%1. x) T%0) (%%apply%%0 (%Poly%fun%1. y) T%0))
       )
       :pattern ((ext_eq deep T%1& (%%apply%%0 (%Poly%fun%1. x) T%0) (%%apply%%0 (%Poly%fun%1.
           y
          ) T%0
       )))
       :qid internal_crate__fun__1_inner_ext_equal_definition
    )))
    (ext_eq deep (TYPE%fun%1. T%0&. T%0& T%1&. T%1&) x y)
   )
   :pattern ((ext_eq deep (TYPE%fun%1. T%0&. T%0& T%1&. T%1&) x y))
   :qid internal_crate__fun__1_ext_equal_definition
)))
(assert
 (forall ((x %%Function%%)) (!
   (= x (%Poly%fun%2. (Poly%fun%2. x)))
   :pattern ((Poly%fun%2. x))
   :qid internal_crate__fun__2_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (x
    Poly
   )
  ) (!
   (=>
    (has_type x (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
    (= x (Poly%fun%2. (%Poly%fun%2. x)))
   )
   :pattern ((has_type x (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&)))
   :qid internal_crate__fun__2_unbox_axiom_definition
)))
(declare-fun %%apply%%1 (%%Function%% Poly Poly) Poly)
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (x
    %%Function%%
   )
  ) (!
   (=>
    (forall ((T%0 Poly) (T%1 Poly)) (!
      (=>
       (and
        (has_type T%0 T%0&)
        (has_type T%1 T%1&)
       )
       (has_type (%%apply%%1 x T%0 T%1) T%2&)
      )
      :pattern ((has_type (%%apply%%1 x T%0 T%1) T%2&))
      :qid internal_crate__fun__2_constructor_inner_definition
    ))
    (has_type (Poly%fun%2. (mk_fun x)) (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
   )
   :pattern ((has_type (Poly%fun%2. (mk_fun x)) (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&.
      T%2&
   )))
   :qid internal_crate__fun__2_constructor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%0
    Poly
   ) (T%1 Poly) (x %%Function%%)
  ) (!
   (=>
    (and
     (has_type (Poly%fun%2. x) (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (has_type T%0 T%0&)
     (has_type T%1 T%1&)
    )
    (has_type (%%apply%%1 x T%0 T%1) T%2&)
   )
   :pattern ((%%apply%%1 x T%0 T%1) (has_type (Poly%fun%2. x) (TYPE%fun%2. T%0&. T%0& T%1&.
      T%1& T%2&. T%2&
   )))
   :qid internal_crate__fun__2_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%0
    Poly
   ) (T%1 Poly) (x %%Function%%)
  ) (!
   (=>
    (and
     (has_type (Poly%fun%2. x) (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (has_type T%0 T%0&)
     (has_type T%1 T%1&)
    )
    (height_lt (height (%%apply%%1 x T%0 T%1)) (height (fun_from_recursive_field (Poly%fun%2.
        (mk_fun x)
   )))))
   :pattern ((height (%%apply%%1 x T%0 T%1)) (has_type (Poly%fun%2. x) (TYPE%fun%2. T%0&.
      T%0& T%1&. T%1& T%2&. T%2&
   )))
   :qid internal_crate__fun__2_height_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (deep
    Bool
   ) (x Poly) (y Poly)
  ) (!
   (=>
    (and
     (has_type x (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (has_type y (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (forall ((T%0 Poly) (T%1 Poly)) (!
       (=>
        (and
         (has_type T%0 T%0&)
         (has_type T%1 T%1&)
        )
        (ext_eq deep T%2& (%%apply%%1 (%Poly%fun%2. x) T%0 T%1) (%%apply%%1 (%Poly%fun%2. y)
          T%0 T%1
       )))
       :pattern ((ext_eq deep T%2& (%%apply%%1 (%Poly%fun%2. x) T%0 T%1) (%%apply%%1 (%Poly%fun%2.
           y
          ) T%0 T%1
       )))
       :qid internal_crate__fun__2_inner_ext_equal_definition
    )))
    (ext_eq deep (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&) x y)
   )
   :pattern ((ext_eq deep (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&) x y))
   :qid internal_crate__fun__2_ext_equal_definition
)))
(assert
 (forall ((x alloc!alloc.Global.)) (!
   (= x (%Poly%alloc!alloc.Global. (Poly%alloc!alloc.Global. x)))
   :pattern ((Poly%alloc!alloc.Global. x))
   :qid internal_alloc__alloc__Global_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%alloc!alloc.Global.)
    (= x (Poly%alloc!alloc.Global. (%Poly%alloc!alloc.Global. x)))
   )
   :pattern ((has_type x TYPE%alloc!alloc.Global.))
   :qid internal_alloc__alloc__Global_unbox_axiom_definition
)))
(assert
 (forall ((x alloc!alloc.Global.)) (!
   (has_type (Poly%alloc!alloc.Global. x) TYPE%alloc!alloc.Global.)
   :pattern ((has_type (Poly%alloc!alloc.Global. x) TYPE%alloc!alloc.Global.))
   :qid internal_alloc__alloc__Global_has_type_always_definition
)))
(assert
 (forall ((x alloc!vec.Vec<u8./alloc!alloc.Global.>.)) (!
   (= x (%Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>.
      x
   )))
   :pattern ((Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. x))
   :qid internal_alloc__vec__Vec<u8./alloc!alloc.Global.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.))
    (= x (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (%Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>.
       x
   ))))
   :pattern ((has_type x (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)))
   :qid internal_alloc__vec__Vec<u8./alloc!alloc.Global.>_unbox_axiom_definition
)))
(assert
 (forall ((x alloc!vec.Vec<u8./alloc!alloc.Global.>.)) (!
   (has_type (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. x) (TYPE%alloc!vec.Vec. $ (
      UINT 8
     ) $ TYPE%alloc!alloc.Global.
   ))
   :pattern ((has_type (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. x) (TYPE%alloc!vec.Vec.
      $ (UINT 8) $ TYPE%alloc!alloc.Global.
   )))
   :qid internal_alloc__vec__Vec<u8./alloc!alloc.Global.>_has_type_always_definition
)))
(assert
 (forall ((x alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.)) (!
   (= x (%Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
      x
   )))
   :pattern ((Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. x))
   :qid internal_alloc__vec__Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.))
    (= x (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (%Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
       x
   ))))
   :pattern ((has_type x (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.)))
   :qid internal_alloc__vec__Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>_unbox_axiom_definition
)))
(assert
 (forall ((x alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.)) (!
   (has_type (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. x) (TYPE%alloc!vec.Vec.
     $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.
   ))
   :pattern ((has_type (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
      x
     ) (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.)
   ))
   :qid internal_alloc__vec__Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>_has_type_always_definition
)))
(assert
 (forall ((x lib!hashmap_t.CKeyHashMap.)) (!
   (= x (%Poly%lib!hashmap_t.CKeyHashMap. (Poly%lib!hashmap_t.CKeyHashMap. x)))
   :pattern ((Poly%lib!hashmap_t.CKeyHashMap. x))
   :qid internal_lib__hashmap_t__CKeyHashMap_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!hashmap_t.CKeyHashMap.)
    (= x (Poly%lib!hashmap_t.CKeyHashMap. (%Poly%lib!hashmap_t.CKeyHashMap. x)))
   )
   :pattern ((has_type x TYPE%lib!hashmap_t.CKeyHashMap.))
   :qid internal_lib__hashmap_t__CKeyHashMap_unbox_axiom_definition
)))
(assert
 (forall ((x lib!hashmap_t.CKeyHashMap.)) (!
   (has_type (Poly%lib!hashmap_t.CKeyHashMap. x) TYPE%lib!hashmap_t.CKeyHashMap.)
   :pattern ((has_type (Poly%lib!hashmap_t.CKeyHashMap. x) TYPE%lib!hashmap_t.CKeyHashMap.))
   :qid internal_lib__hashmap_t__CKeyHashMap_has_type_always_definition
)))
(assert
 (forall ((x vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.)) (!
   (= x (%Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. (Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.
      x
   )))
   :pattern ((Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. x))
   :qid internal_vstd__map__Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!map.Map. $ TYPE%lib!keys_t.SHTKey. $ (TYPE%vstd!seq.Seq. $ (UINT
        8
    ))))
    (= x (Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. (%Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!map.Map. $ TYPE%lib!keys_t.SHTKey. $ (TYPE%vstd!seq.Seq.
       $ (UINT 8)
   ))))
   :qid internal_vstd__map__Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.)) (!
   (has_type (Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. x) (TYPE%vstd!map.Map.
     $ TYPE%lib!keys_t.SHTKey. $ (TYPE%vstd!seq.Seq. $ (UINT 8))
   ))
   :pattern ((has_type (Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. x) (
      TYPE%vstd!map.Map. $ TYPE%lib!keys_t.SHTKey. $ (TYPE%vstd!seq.Seq. $ (UINT 8))
   )))
   :qid internal_vstd__map__Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!seq.Seq<u8.>.)) (!
   (= x (%Poly%vstd!seq.Seq<u8.>. (Poly%vstd!seq.Seq<u8.>. x)))
   :pattern ((Poly%vstd!seq.Seq<u8.>. x))
   :qid internal_vstd__seq__Seq<u8.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!seq.Seq. $ (UINT 8)))
    (= x (Poly%vstd!seq.Seq<u8.>. (%Poly%vstd!seq.Seq<u8.>. x)))
   )
   :pattern ((has_type x (TYPE%vstd!seq.Seq. $ (UINT 8))))
   :qid internal_vstd__seq__Seq<u8.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!seq.Seq<u8.>.)) (!
   (has_type (Poly%vstd!seq.Seq<u8.>. x) (TYPE%vstd!seq.Seq. $ (UINT 8)))
   :pattern ((has_type (Poly%vstd!seq.Seq<u8.>. x) (TYPE%vstd!seq.Seq. $ (UINT 8))))
   :qid internal_vstd__seq__Seq<u8.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!seq.Seq<lib!hashmap_t.CKeyKV.>.)) (!
   (= x (%Poly%vstd!seq.Seq<lib!hashmap_t.CKeyKV.>. (Poly%vstd!seq.Seq<lib!hashmap_t.CKeyKV.>.
      x
   )))
   :pattern ((Poly%vstd!seq.Seq<lib!hashmap_t.CKeyKV.>. x))
   :qid internal_vstd__seq__Seq<lib!hashmap_t.CKeyKV.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!seq.Seq. $ TYPE%lib!hashmap_t.CKeyKV.))
    (= x (Poly%vstd!seq.Seq<lib!hashmap_t.CKeyKV.>. (%Poly%vstd!seq.Seq<lib!hashmap_t.CKeyKV.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!seq.Seq. $ TYPE%lib!hashmap_t.CKeyKV.)))
   :qid internal_vstd__seq__Seq<lib!hashmap_t.CKeyKV.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!seq.Seq<lib!hashmap_t.CKeyKV.>.)) (!
   (has_type (Poly%vstd!seq.Seq<lib!hashmap_t.CKeyKV.>. x) (TYPE%vstd!seq.Seq. $ TYPE%lib!hashmap_t.CKeyKV.))
   :pattern ((has_type (Poly%vstd!seq.Seq<lib!hashmap_t.CKeyKV.>. x) (TYPE%vstd!seq.Seq.
      $ TYPE%lib!hashmap_t.CKeyKV.
   )))
   :qid internal_vstd__seq__Seq<lib!hashmap_t.CKeyKV.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!set.Set<lib!keys_t.SHTKey.>.)) (!
   (= x (%Poly%vstd!set.Set<lib!keys_t.SHTKey.>. (Poly%vstd!set.Set<lib!keys_t.SHTKey.>.
      x
   )))
   :pattern ((Poly%vstd!set.Set<lib!keys_t.SHTKey.>. x))
   :qid internal_vstd__set__Set<lib!keys_t.SHTKey.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!set.Set. $ TYPE%lib!keys_t.SHTKey.))
    (= x (Poly%vstd!set.Set<lib!keys_t.SHTKey.>. (%Poly%vstd!set.Set<lib!keys_t.SHTKey.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!set.Set. $ TYPE%lib!keys_t.SHTKey.)))
   :qid internal_vstd__set__Set<lib!keys_t.SHTKey.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!set.Set<lib!keys_t.SHTKey.>.)) (!
   (has_type (Poly%vstd!set.Set<lib!keys_t.SHTKey.>. x) (TYPE%vstd!set.Set. $ TYPE%lib!keys_t.SHTKey.))
   :pattern ((has_type (Poly%vstd!set.Set<lib!keys_t.SHTKey.>. x) (TYPE%vstd!set.Set. $
      TYPE%lib!keys_t.SHTKey.
   )))
   :qid internal_vstd__set__Set<lib!keys_t.SHTKey.>_has_type_always_definition
)))
(assert
 (forall ((x core!option.Option.)) (!
   (= x (%Poly%core!option.Option. (Poly%core!option.Option. x)))
   :pattern ((Poly%core!option.Option. x))
   :qid internal_core__option__Option_box_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!option.Option. V&. V&))
    (= x (Poly%core!option.Option. (%Poly%core!option.Option. x)))
   )
   :pattern ((has_type x (TYPE%core!option.Option. V&. V&)))
   :qid internal_core__option__Option_unbox_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type)) (!
   (has_type (Poly%core!option.Option. core!option.Option./None) (TYPE%core!option.Option.
     V&. V&
   ))
   :pattern ((has_type (Poly%core!option.Option. core!option.Option./None) (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./None_constructor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (_0! Poly)) (!
   (=>
    (has_type _0! V&)
    (has_type (Poly%core!option.Option. (core!option.Option./Some _0!)) (TYPE%core!option.Option.
      V&. V&
   )))
   :pattern ((has_type (Poly%core!option.Option. (core!option.Option./Some _0!)) (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./Some_constructor_definition
)))
(assert
 (forall ((x core!option.Option.)) (!
   (= (core!option.Option./Some/0 x) (core!option.Option./Some/?0 x))
   :pattern ((core!option.Option./Some/0 x))
   :qid internal_core!option.Option./Some/0_accessor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!option.Option. V&. V&))
    (has_type (core!option.Option./Some/0 (%Poly%core!option.Option. x)) V&)
   )
   :pattern ((core!option.Option./Some/0 (%Poly%core!option.Option. x)) (has_type x (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./Some/0_invariant_definition
)))
(assert
 (forall ((x core!option.Option.)) (!
   (=>
    (is-core!option.Option./Some x)
    (height_lt (height (core!option.Option./Some/0 x)) (height (Poly%core!option.Option.
       x
   ))))
   :pattern ((height (core!option.Option./Some/0 x)))
   :qid prelude_datatype_height_core!option.Option./Some/0
)))
(assert
 (forall ((V&. Dcr) (V& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%core!option.Option. V&. V&))
     (has_type y (TYPE%core!option.Option. V&. V&))
     (is-core!option.Option./None (%Poly%core!option.Option. x))
     (is-core!option.Option./None (%Poly%core!option.Option. y))
    )
    (ext_eq deep (TYPE%core!option.Option. V&. V&) x y)
   )
   :pattern ((ext_eq deep (TYPE%core!option.Option. V&. V&) x y))
   :qid internal_core!option.Option./None_ext_equal_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%core!option.Option. V&. V&))
     (has_type y (TYPE%core!option.Option. V&. V&))
     (is-core!option.Option./Some (%Poly%core!option.Option. x))
     (is-core!option.Option./Some (%Poly%core!option.Option. y))
     (ext_eq deep V& (core!option.Option./Some/0 (%Poly%core!option.Option. x)) (core!option.Option./Some/0
       (%Poly%core!option.Option. y)
    )))
    (ext_eq deep (TYPE%core!option.Option. V&. V&) x y)
   )
   :pattern ((ext_eq deep (TYPE%core!option.Option. V&. V&) x y))
   :qid internal_core!option.Option./Some_ext_equal_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= x (%Poly%lib!cmessage_v.CMessage. (Poly%lib!cmessage_v.CMessage. x)))
   :pattern ((Poly%lib!cmessage_v.CMessage. x))
   :qid internal_lib__cmessage_v__CMessage_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CMessage.)
    (= x (Poly%lib!cmessage_v.CMessage. (%Poly%lib!cmessage_v.CMessage. x)))
   )
   :pattern ((has_type x TYPE%lib!cmessage_v.CMessage.))
   :qid internal_lib__cmessage_v__CMessage_unbox_axiom_definition
)))
(assert
 (forall ((_k! lib!keys_t.SHTKey.)) (!
   (=>
    (has_type (Poly%lib!keys_t.SHTKey. _k!) TYPE%lib!keys_t.SHTKey.)
    (has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./GetRequest _k!))
     TYPE%lib!cmessage_v.CMessage.
   ))
   :pattern ((has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./GetRequest
       _k!
      )
     ) TYPE%lib!cmessage_v.CMessage.
   ))
   :qid internal_lib!cmessage_v.CMessage./GetRequest_constructor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./GetRequest/k x) (lib!cmessage_v.CMessage./GetRequest/?k
     x
   ))
   :pattern ((lib!cmessage_v.CMessage./GetRequest/k x))
   :qid internal_lib!cmessage_v.CMessage./GetRequest/k_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CMessage.)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!cmessage_v.CMessage./GetRequest/k (%Poly%lib!cmessage_v.CMessage.
        x
      ))
     ) TYPE%lib!keys_t.SHTKey.
   ))
   :pattern ((lib!cmessage_v.CMessage./GetRequest/k (%Poly%lib!cmessage_v.CMessage. x))
    (has_type x TYPE%lib!cmessage_v.CMessage.)
   )
   :qid internal_lib!cmessage_v.CMessage./GetRequest/k_invariant_definition
)))
(assert
 (forall ((_k! lib!keys_t.SHTKey.) (_v! core!option.Option.)) (!
   (=>
    (and
     (has_type (Poly%lib!keys_t.SHTKey. _k!) TYPE%lib!keys_t.SHTKey.)
     (has_type (Poly%core!option.Option. _v!) (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec.
        $ (UINT 8) $ TYPE%alloc!alloc.Global.
    ))))
    (has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./SetRequest _k! _v!))
     TYPE%lib!cmessage_v.CMessage.
   ))
   :pattern ((has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./SetRequest
       _k! _v!
      )
     ) TYPE%lib!cmessage_v.CMessage.
   ))
   :qid internal_lib!cmessage_v.CMessage./SetRequest_constructor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./SetRequest/k x) (lib!cmessage_v.CMessage./SetRequest/?k
     x
   ))
   :pattern ((lib!cmessage_v.CMessage./SetRequest/k x))
   :qid internal_lib!cmessage_v.CMessage./SetRequest/k_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CMessage.)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!cmessage_v.CMessage./SetRequest/k (%Poly%lib!cmessage_v.CMessage.
        x
      ))
     ) TYPE%lib!keys_t.SHTKey.
   ))
   :pattern ((lib!cmessage_v.CMessage./SetRequest/k (%Poly%lib!cmessage_v.CMessage. x))
    (has_type x TYPE%lib!cmessage_v.CMessage.)
   )
   :qid internal_lib!cmessage_v.CMessage./SetRequest/k_invariant_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./SetRequest/v x) (lib!cmessage_v.CMessage./SetRequest/?v
     x
   ))
   :pattern ((lib!cmessage_v.CMessage./SetRequest/v x))
   :qid internal_lib!cmessage_v.CMessage./SetRequest/v_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CMessage.)
    (has_type (Poly%core!option.Option. (lib!cmessage_v.CMessage./SetRequest/v (%Poly%lib!cmessage_v.CMessage.
        x
      ))
     ) (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.))
   ))
   :pattern ((lib!cmessage_v.CMessage./SetRequest/v (%Poly%lib!cmessage_v.CMessage. x))
    (has_type x TYPE%lib!cmessage_v.CMessage.)
   )
   :qid internal_lib!cmessage_v.CMessage./SetRequest/v_invariant_definition
)))
(assert
 (forall ((_k! lib!keys_t.SHTKey.) (_v! core!option.Option.)) (!
   (=>
    (and
     (has_type (Poly%lib!keys_t.SHTKey. _k!) TYPE%lib!keys_t.SHTKey.)
     (has_type (Poly%core!option.Option. _v!) (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec.
        $ (UINT 8) $ TYPE%alloc!alloc.Global.
    ))))
    (has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./Reply _k! _v!))
     TYPE%lib!cmessage_v.CMessage.
   ))
   :pattern ((has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./Reply _k!
       _v!
      )
     ) TYPE%lib!cmessage_v.CMessage.
   ))
   :qid internal_lib!cmessage_v.CMessage./Reply_constructor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./Reply/k x) (lib!cmessage_v.CMessage./Reply/?k x))
   :pattern ((lib!cmessage_v.CMessage./Reply/k x))
   :qid internal_lib!cmessage_v.CMessage./Reply/k_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CMessage.)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!cmessage_v.CMessage./Reply/k (%Poly%lib!cmessage_v.CMessage.
        x
      ))
     ) TYPE%lib!keys_t.SHTKey.
   ))
   :pattern ((lib!cmessage_v.CMessage./Reply/k (%Poly%lib!cmessage_v.CMessage. x)) (has_type
     x TYPE%lib!cmessage_v.CMessage.
   ))
   :qid internal_lib!cmessage_v.CMessage./Reply/k_invariant_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./Reply/v x) (lib!cmessage_v.CMessage./Reply/?v x))
   :pattern ((lib!cmessage_v.CMessage./Reply/v x))
   :qid internal_lib!cmessage_v.CMessage./Reply/v_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CMessage.)
    (has_type (Poly%core!option.Option. (lib!cmessage_v.CMessage./Reply/v (%Poly%lib!cmessage_v.CMessage.
        x
      ))
     ) (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.))
   ))
   :pattern ((lib!cmessage_v.CMessage./Reply/v (%Poly%lib!cmessage_v.CMessage. x)) (has_type
     x TYPE%lib!cmessage_v.CMessage.
   ))
   :qid internal_lib!cmessage_v.CMessage./Reply/v_invariant_definition
)))
(assert
 (forall ((_k! lib!keys_t.SHTKey.) (_id! lib!io_t.EndPoint.)) (!
   (=>
    (has_type (Poly%lib!keys_t.SHTKey. _k!) TYPE%lib!keys_t.SHTKey.)
    (has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./Redirect _k! _id!))
     TYPE%lib!cmessage_v.CMessage.
   ))
   :pattern ((has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./Redirect
       _k! _id!
      )
     ) TYPE%lib!cmessage_v.CMessage.
   ))
   :qid internal_lib!cmessage_v.CMessage./Redirect_constructor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./Redirect/k x) (lib!cmessage_v.CMessage./Redirect/?k x))
   :pattern ((lib!cmessage_v.CMessage./Redirect/k x))
   :qid internal_lib!cmessage_v.CMessage./Redirect/k_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CMessage.)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!cmessage_v.CMessage./Redirect/k (%Poly%lib!cmessage_v.CMessage.
        x
      ))
     ) TYPE%lib!keys_t.SHTKey.
   ))
   :pattern ((lib!cmessage_v.CMessage./Redirect/k (%Poly%lib!cmessage_v.CMessage. x))
    (has_type x TYPE%lib!cmessage_v.CMessage.)
   )
   :qid internal_lib!cmessage_v.CMessage./Redirect/k_invariant_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./Redirect/id x) (lib!cmessage_v.CMessage./Redirect/?id
     x
   ))
   :pattern ((lib!cmessage_v.CMessage./Redirect/id x))
   :qid internal_lib!cmessage_v.CMessage./Redirect/id_accessor_definition
)))
(assert
 (forall ((_kr! lib!keys_t.KeyRange.) (_recipient! lib!io_t.EndPoint.)) (!
   (=>
    (has_type (Poly%lib!keys_t.KeyRange. _kr!) (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.))
    (has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./Shard _kr! _recipient!))
     TYPE%lib!cmessage_v.CMessage.
   ))
   :pattern ((has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./Shard _kr!
       _recipient!
      )
     ) TYPE%lib!cmessage_v.CMessage.
   ))
   :qid internal_lib!cmessage_v.CMessage./Shard_constructor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./Shard/kr x) (lib!cmessage_v.CMessage./Shard/?kr x))
   :pattern ((lib!cmessage_v.CMessage./Shard/kr x))
   :qid internal_lib!cmessage_v.CMessage./Shard/kr_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CMessage.)
    (has_type (Poly%lib!keys_t.KeyRange. (lib!cmessage_v.CMessage./Shard/kr (%Poly%lib!cmessage_v.CMessage.
        x
      ))
     ) (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
   ))
   :pattern ((lib!cmessage_v.CMessage./Shard/kr (%Poly%lib!cmessage_v.CMessage. x)) (
     has_type x TYPE%lib!cmessage_v.CMessage.
   ))
   :qid internal_lib!cmessage_v.CMessage./Shard/kr_invariant_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./Shard/recipient x) (lib!cmessage_v.CMessage./Shard/?recipient
     x
   ))
   :pattern ((lib!cmessage_v.CMessage./Shard/recipient x))
   :qid internal_lib!cmessage_v.CMessage./Shard/recipient_accessor_definition
)))
(assert
 (forall ((_range! lib!keys_t.KeyRange.) (_h! lib!hashmap_t.CKeyHashMap.)) (!
   (=>
    (has_type (Poly%lib!keys_t.KeyRange. _range!) (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.))
    (has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./Delegate _range!
       _h!
      )
     ) TYPE%lib!cmessage_v.CMessage.
   ))
   :pattern ((has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CMessage./Delegate
       _range! _h!
      )
     ) TYPE%lib!cmessage_v.CMessage.
   ))
   :qid internal_lib!cmessage_v.CMessage./Delegate_constructor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./Delegate/range x) (lib!cmessage_v.CMessage./Delegate/?range
     x
   ))
   :pattern ((lib!cmessage_v.CMessage./Delegate/range x))
   :qid internal_lib!cmessage_v.CMessage./Delegate/range_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CMessage.)
    (has_type (Poly%lib!keys_t.KeyRange. (lib!cmessage_v.CMessage./Delegate/range (%Poly%lib!cmessage_v.CMessage.
        x
      ))
     ) (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
   ))
   :pattern ((lib!cmessage_v.CMessage./Delegate/range (%Poly%lib!cmessage_v.CMessage. x))
    (has_type x TYPE%lib!cmessage_v.CMessage.)
   )
   :qid internal_lib!cmessage_v.CMessage./Delegate/range_invariant_definition
)))
(assert
 (forall ((x lib!cmessage_v.CMessage.)) (!
   (= (lib!cmessage_v.CMessage./Delegate/h x) (lib!cmessage_v.CMessage./Delegate/?h x))
   :pattern ((lib!cmessage_v.CMessage./Delegate/h x))
   :qid internal_lib!cmessage_v.CMessage./Delegate/h_accessor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CPacket.)) (!
   (= x (%Poly%lib!cmessage_v.CPacket. (Poly%lib!cmessage_v.CPacket. x)))
   :pattern ((Poly%lib!cmessage_v.CPacket. x))
   :qid internal_lib__cmessage_v__CPacket_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CPacket.)
    (= x (Poly%lib!cmessage_v.CPacket. (%Poly%lib!cmessage_v.CPacket. x)))
   )
   :pattern ((has_type x TYPE%lib!cmessage_v.CPacket.))
   :qid internal_lib__cmessage_v__CPacket_unbox_axiom_definition
)))
(assert
 (forall ((_dst! lib!io_t.EndPoint.) (_src! lib!io_t.EndPoint.) (_msg! lib!cmessage_v.CSingleMessage.))
  (!
   (=>
    (has_type (Poly%lib!cmessage_v.CSingleMessage. _msg!) TYPE%lib!cmessage_v.CSingleMessage.)
    (has_type (Poly%lib!cmessage_v.CPacket. (lib!cmessage_v.CPacket./CPacket _dst! _src!
       _msg!
      )
     ) TYPE%lib!cmessage_v.CPacket.
   ))
   :pattern ((has_type (Poly%lib!cmessage_v.CPacket. (lib!cmessage_v.CPacket./CPacket _dst!
       _src! _msg!
      )
     ) TYPE%lib!cmessage_v.CPacket.
   ))
   :qid internal_lib!cmessage_v.CPacket./CPacket_constructor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CPacket.)) (!
   (= (lib!cmessage_v.CPacket./CPacket/dst x) (lib!cmessage_v.CPacket./CPacket/?dst x))
   :pattern ((lib!cmessage_v.CPacket./CPacket/dst x))
   :qid internal_lib!cmessage_v.CPacket./CPacket/dst_accessor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CPacket.)) (!
   (= (lib!cmessage_v.CPacket./CPacket/src x) (lib!cmessage_v.CPacket./CPacket/?src x))
   :pattern ((lib!cmessage_v.CPacket./CPacket/src x))
   :qid internal_lib!cmessage_v.CPacket./CPacket/src_accessor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CPacket.)) (!
   (= (lib!cmessage_v.CPacket./CPacket/msg x) (lib!cmessage_v.CPacket./CPacket/?msg x))
   :pattern ((lib!cmessage_v.CPacket./CPacket/msg x))
   :qid internal_lib!cmessage_v.CPacket./CPacket/msg_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CPacket.)
    (has_type (Poly%lib!cmessage_v.CSingleMessage. (lib!cmessage_v.CPacket./CPacket/msg
       (%Poly%lib!cmessage_v.CPacket. x)
      )
     ) TYPE%lib!cmessage_v.CSingleMessage.
   ))
   :pattern ((lib!cmessage_v.CPacket./CPacket/msg (%Poly%lib!cmessage_v.CPacket. x))
    (has_type x TYPE%lib!cmessage_v.CPacket.)
   )
   :qid internal_lib!cmessage_v.CPacket./CPacket/msg_invariant_definition
)))
(assert
 (forall ((x lib!cmessage_v.CSingleMessage.)) (!
   (= x (%Poly%lib!cmessage_v.CSingleMessage. (Poly%lib!cmessage_v.CSingleMessage. x)))
   :pattern ((Poly%lib!cmessage_v.CSingleMessage. x))
   :qid internal_lib__cmessage_v__CSingleMessage_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CSingleMessage.)
    (= x (Poly%lib!cmessage_v.CSingleMessage. (%Poly%lib!cmessage_v.CSingleMessage. x)))
   )
   :pattern ((has_type x TYPE%lib!cmessage_v.CSingleMessage.))
   :qid internal_lib__cmessage_v__CSingleMessage_unbox_axiom_definition
)))
(assert
 (forall ((_seqno! Int) (_dst! lib!io_t.EndPoint.) (_m! lib!cmessage_v.CMessage.))
  (!
   (=>
    (and
     (uInv 64 _seqno!)
     (has_type (Poly%lib!cmessage_v.CMessage. _m!) TYPE%lib!cmessage_v.CMessage.)
    )
    (has_type (Poly%lib!cmessage_v.CSingleMessage. (lib!cmessage_v.CSingleMessage./Message
       _seqno! _dst! _m!
      )
     ) TYPE%lib!cmessage_v.CSingleMessage.
   ))
   :pattern ((has_type (Poly%lib!cmessage_v.CSingleMessage. (lib!cmessage_v.CSingleMessage./Message
       _seqno! _dst! _m!
      )
     ) TYPE%lib!cmessage_v.CSingleMessage.
   ))
   :qid internal_lib!cmessage_v.CSingleMessage./Message_constructor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CSingleMessage.)) (!
   (= (lib!cmessage_v.CSingleMessage./Message/seqno x) (lib!cmessage_v.CSingleMessage./Message/?seqno
     x
   ))
   :pattern ((lib!cmessage_v.CSingleMessage./Message/seqno x))
   :qid internal_lib!cmessage_v.CSingleMessage./Message/seqno_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CSingleMessage.)
    (uInv 64 (lib!cmessage_v.CSingleMessage./Message/seqno (%Poly%lib!cmessage_v.CSingleMessage.
       x
   ))))
   :pattern ((lib!cmessage_v.CSingleMessage./Message/seqno (%Poly%lib!cmessage_v.CSingleMessage.
      x
     )
    ) (has_type x TYPE%lib!cmessage_v.CSingleMessage.)
   )
   :qid internal_lib!cmessage_v.CSingleMessage./Message/seqno_invariant_definition
)))
(assert
 (forall ((x lib!cmessage_v.CSingleMessage.)) (!
   (= (lib!cmessage_v.CSingleMessage./Message/dst x) (lib!cmessage_v.CSingleMessage./Message/?dst
     x
   ))
   :pattern ((lib!cmessage_v.CSingleMessage./Message/dst x))
   :qid internal_lib!cmessage_v.CSingleMessage./Message/dst_accessor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CSingleMessage.)) (!
   (= (lib!cmessage_v.CSingleMessage./Message/m x) (lib!cmessage_v.CSingleMessage./Message/?m
     x
   ))
   :pattern ((lib!cmessage_v.CSingleMessage./Message/m x))
   :qid internal_lib!cmessage_v.CSingleMessage./Message/m_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CSingleMessage.)
    (has_type (Poly%lib!cmessage_v.CMessage. (lib!cmessage_v.CSingleMessage./Message/m (
        %Poly%lib!cmessage_v.CSingleMessage. x
      ))
     ) TYPE%lib!cmessage_v.CMessage.
   ))
   :pattern ((lib!cmessage_v.CSingleMessage./Message/m (%Poly%lib!cmessage_v.CSingleMessage.
      x
     )
    ) (has_type x TYPE%lib!cmessage_v.CSingleMessage.)
   )
   :qid internal_lib!cmessage_v.CSingleMessage./Message/m_invariant_definition
)))
(assert
 (forall ((_ack_seqno! Int)) (!
   (=>
    (uInv 64 _ack_seqno!)
    (has_type (Poly%lib!cmessage_v.CSingleMessage. (lib!cmessage_v.CSingleMessage./Ack _ack_seqno!))
     TYPE%lib!cmessage_v.CSingleMessage.
   ))
   :pattern ((has_type (Poly%lib!cmessage_v.CSingleMessage. (lib!cmessage_v.CSingleMessage./Ack
       _ack_seqno!
      )
     ) TYPE%lib!cmessage_v.CSingleMessage.
   ))
   :qid internal_lib!cmessage_v.CSingleMessage./Ack_constructor_definition
)))
(assert
 (forall ((x lib!cmessage_v.CSingleMessage.)) (!
   (= (lib!cmessage_v.CSingleMessage./Ack/ack_seqno x) (lib!cmessage_v.CSingleMessage./Ack/?ack_seqno
     x
   ))
   :pattern ((lib!cmessage_v.CSingleMessage./Ack/ack_seqno x))
   :qid internal_lib!cmessage_v.CSingleMessage./Ack/ack_seqno_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!cmessage_v.CSingleMessage.)
    (uInv 64 (lib!cmessage_v.CSingleMessage./Ack/ack_seqno (%Poly%lib!cmessage_v.CSingleMessage.
       x
   ))))
   :pattern ((lib!cmessage_v.CSingleMessage./Ack/ack_seqno (%Poly%lib!cmessage_v.CSingleMessage.
      x
     )
    ) (has_type x TYPE%lib!cmessage_v.CSingleMessage.)
   )
   :qid internal_lib!cmessage_v.CSingleMessage./Ack/ack_seqno_invariant_definition
)))
(assert
 (has_type (Poly%lib!cmessage_v.CSingleMessage. lib!cmessage_v.CSingleMessage./InvalidMessage)
  TYPE%lib!cmessage_v.CSingleMessage.
))
(assert
 (forall ((x lib!net_sht_v.ReceiveResult.)) (!
   (= x (%Poly%lib!net_sht_v.ReceiveResult. (Poly%lib!net_sht_v.ReceiveResult. x)))
   :pattern ((Poly%lib!net_sht_v.ReceiveResult. x))
   :qid internal_lib__net_sht_v__ReceiveResult_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!net_sht_v.ReceiveResult.)
    (= x (Poly%lib!net_sht_v.ReceiveResult. (%Poly%lib!net_sht_v.ReceiveResult. x)))
   )
   :pattern ((has_type x TYPE%lib!net_sht_v.ReceiveResult.))
   :qid internal_lib__net_sht_v__ReceiveResult_unbox_axiom_definition
)))
(assert
 (has_type (Poly%lib!net_sht_v.ReceiveResult. lib!net_sht_v.ReceiveResult./Fail) TYPE%lib!net_sht_v.ReceiveResult.)
)
(assert
 (has_type (Poly%lib!net_sht_v.ReceiveResult. lib!net_sht_v.ReceiveResult./Timeout)
  TYPE%lib!net_sht_v.ReceiveResult.
))
(assert
 (forall ((_cpacket! lib!cmessage_v.CPacket.)) (!
   (=>
    (has_type (Poly%lib!cmessage_v.CPacket. _cpacket!) TYPE%lib!cmessage_v.CPacket.)
    (has_type (Poly%lib!net_sht_v.ReceiveResult. (lib!net_sht_v.ReceiveResult./Packet _cpacket!))
     TYPE%lib!net_sht_v.ReceiveResult.
   ))
   :pattern ((has_type (Poly%lib!net_sht_v.ReceiveResult. (lib!net_sht_v.ReceiveResult./Packet
       _cpacket!
      )
     ) TYPE%lib!net_sht_v.ReceiveResult.
   ))
   :qid internal_lib!net_sht_v.ReceiveResult./Packet_constructor_definition
)))
(assert
 (forall ((x lib!net_sht_v.ReceiveResult.)) (!
   (= (lib!net_sht_v.ReceiveResult./Packet/cpacket x) (lib!net_sht_v.ReceiveResult./Packet/?cpacket
     x
   ))
   :pattern ((lib!net_sht_v.ReceiveResult./Packet/cpacket x))
   :qid internal_lib!net_sht_v.ReceiveResult./Packet/cpacket_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!net_sht_v.ReceiveResult.)
    (has_type (Poly%lib!cmessage_v.CPacket. (lib!net_sht_v.ReceiveResult./Packet/cpacket
       (%Poly%lib!net_sht_v.ReceiveResult. x)
      )
     ) TYPE%lib!cmessage_v.CPacket.
   ))
   :pattern ((lib!net_sht_v.ReceiveResult./Packet/cpacket (%Poly%lib!net_sht_v.ReceiveResult.
      x
     )
    ) (has_type x TYPE%lib!net_sht_v.ReceiveResult.)
   )
   :qid internal_lib!net_sht_v.ReceiveResult./Packet/cpacket_invariant_definition
)))
(assert
 (forall ((x lib!abstract_end_point_t.AbstractEndPoint.)) (!
   (= x (%Poly%lib!abstract_end_point_t.AbstractEndPoint. (Poly%lib!abstract_end_point_t.AbstractEndPoint.
      x
   )))
   :pattern ((Poly%lib!abstract_end_point_t.AbstractEndPoint. x))
   :qid internal_lib__abstract_end_point_t__AbstractEndPoint_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!abstract_end_point_t.AbstractEndPoint.)
    (= x (Poly%lib!abstract_end_point_t.AbstractEndPoint. (%Poly%lib!abstract_end_point_t.AbstractEndPoint.
       x
   ))))
   :pattern ((has_type x TYPE%lib!abstract_end_point_t.AbstractEndPoint.))
   :qid internal_lib__abstract_end_point_t__AbstractEndPoint_unbox_axiom_definition
)))
(assert
 (forall ((x lib!abstract_end_point_t.AbstractEndPoint.)) (!
   (= (lib!abstract_end_point_t.AbstractEndPoint./AbstractEndPoint/id x) (lib!abstract_end_point_t.AbstractEndPoint./AbstractEndPoint/?id
     x
   ))
   :pattern ((lib!abstract_end_point_t.AbstractEndPoint./AbstractEndPoint/id x))
   :qid internal_lib!abstract_end_point_t.AbstractEndPoint./AbstractEndPoint/id_accessor_definition
)))
(assert
 (forall ((x lib!abstract_end_point_t.AbstractEndPoint.)) (!
   (has_type (Poly%lib!abstract_end_point_t.AbstractEndPoint. x) TYPE%lib!abstract_end_point_t.AbstractEndPoint.)
   :pattern ((has_type (Poly%lib!abstract_end_point_t.AbstractEndPoint. x) TYPE%lib!abstract_end_point_t.AbstractEndPoint.))
   :qid internal_lib__abstract_end_point_t__AbstractEndPoint_has_type_always_definition
)))
(assert
 (forall ((x lib!hashmap_t.CKeyKV.)) (!
   (= x (%Poly%lib!hashmap_t.CKeyKV. (Poly%lib!hashmap_t.CKeyKV. x)))
   :pattern ((Poly%lib!hashmap_t.CKeyKV. x))
   :qid internal_lib__hashmap_t__CKeyKV_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!hashmap_t.CKeyKV.)
    (= x (Poly%lib!hashmap_t.CKeyKV. (%Poly%lib!hashmap_t.CKeyKV. x)))
   )
   :pattern ((has_type x TYPE%lib!hashmap_t.CKeyKV.))
   :qid internal_lib__hashmap_t__CKeyKV_unbox_axiom_definition
)))
(assert
 (forall ((_k! lib!keys_t.SHTKey.) (_v! alloc!vec.Vec<u8./alloc!alloc.Global.>.)) (
   !
   (=>
    (has_type (Poly%lib!keys_t.SHTKey. _k!) TYPE%lib!keys_t.SHTKey.)
    (has_type (Poly%lib!hashmap_t.CKeyKV. (lib!hashmap_t.CKeyKV./CKeyKV _k! _v!)) TYPE%lib!hashmap_t.CKeyKV.)
   )
   :pattern ((has_type (Poly%lib!hashmap_t.CKeyKV. (lib!hashmap_t.CKeyKV./CKeyKV _k! _v!))
     TYPE%lib!hashmap_t.CKeyKV.
   ))
   :qid internal_lib!hashmap_t.CKeyKV./CKeyKV_constructor_definition
)))
(assert
 (forall ((x lib!hashmap_t.CKeyKV.)) (!
   (= (lib!hashmap_t.CKeyKV./CKeyKV/k x) (lib!hashmap_t.CKeyKV./CKeyKV/?k x))
   :pattern ((lib!hashmap_t.CKeyKV./CKeyKV/k x))
   :qid internal_lib!hashmap_t.CKeyKV./CKeyKV/k_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!hashmap_t.CKeyKV.)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!hashmap_t.CKeyKV./CKeyKV/k (%Poly%lib!hashmap_t.CKeyKV.
        x
      ))
     ) TYPE%lib!keys_t.SHTKey.
   ))
   :pattern ((lib!hashmap_t.CKeyKV./CKeyKV/k (%Poly%lib!hashmap_t.CKeyKV. x)) (has_type
     x TYPE%lib!hashmap_t.CKeyKV.
   ))
   :qid internal_lib!hashmap_t.CKeyKV./CKeyKV/k_invariant_definition
)))
(assert
 (forall ((x lib!hashmap_t.CKeyKV.)) (!
   (= (lib!hashmap_t.CKeyKV./CKeyKV/v x) (lib!hashmap_t.CKeyKV./CKeyKV/?v x))
   :pattern ((lib!hashmap_t.CKeyKV./CKeyKV/v x))
   :qid internal_lib!hashmap_t.CKeyKV./CKeyKV/v_accessor_definition
)))
(assert
 (forall ((x lib!io_t.EndPoint.)) (!
   (= x (%Poly%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint. x)))
   :pattern ((Poly%lib!io_t.EndPoint. x))
   :qid internal_lib__io_t__EndPoint_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!io_t.EndPoint.)
    (= x (Poly%lib!io_t.EndPoint. (%Poly%lib!io_t.EndPoint. x)))
   )
   :pattern ((has_type x TYPE%lib!io_t.EndPoint.))
   :qid internal_lib__io_t__EndPoint_unbox_axiom_definition
)))
(assert
 (forall ((x lib!io_t.EndPoint.)) (!
   (= (lib!io_t.EndPoint./EndPoint/id x) (lib!io_t.EndPoint./EndPoint/?id x))
   :pattern ((lib!io_t.EndPoint./EndPoint/id x))
   :qid internal_lib!io_t.EndPoint./EndPoint/id_accessor_definition
)))
(assert
 (forall ((x lib!io_t.EndPoint.)) (!
   (has_type (Poly%lib!io_t.EndPoint. x) TYPE%lib!io_t.EndPoint.)
   :pattern ((has_type (Poly%lib!io_t.EndPoint. x) TYPE%lib!io_t.EndPoint.))
   :qid internal_lib__io_t__EndPoint_has_type_always_definition
)))
(assert
 (forall ((x lib!keys_t.KeyIterator.)) (!
   (= x (%Poly%lib!keys_t.KeyIterator. (Poly%lib!keys_t.KeyIterator. x)))
   :pattern ((Poly%lib!keys_t.KeyIterator. x))
   :qid internal_lib__keys_t__KeyIterator_box_axiom_definition
)))
(assert
 (forall ((K&. Dcr) (K& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!keys_t.KeyIterator. K&. K&))
    (= x (Poly%lib!keys_t.KeyIterator. (%Poly%lib!keys_t.KeyIterator. x)))
   )
   :pattern ((has_type x (TYPE%lib!keys_t.KeyIterator. K&. K&)))
   :qid internal_lib__keys_t__KeyIterator_unbox_axiom_definition
)))
(assert
 (forall ((K&. Dcr) (K& Type) (_k! core!option.Option.)) (!
   (=>
    (has_type (Poly%core!option.Option. _k!) (TYPE%core!option.Option. K&. K&))
    (has_type (Poly%lib!keys_t.KeyIterator. (lib!keys_t.KeyIterator./KeyIterator _k!))
     (TYPE%lib!keys_t.KeyIterator. K&. K&)
   ))
   :pattern ((has_type (Poly%lib!keys_t.KeyIterator. (lib!keys_t.KeyIterator./KeyIterator
       _k!
      )
     ) (TYPE%lib!keys_t.KeyIterator. K&. K&)
   ))
   :qid internal_lib!keys_t.KeyIterator./KeyIterator_constructor_definition
)))
(assert
 (forall ((x lib!keys_t.KeyIterator.)) (!
   (= (lib!keys_t.KeyIterator./KeyIterator/k x) (lib!keys_t.KeyIterator./KeyIterator/?k
     x
   ))
   :pattern ((lib!keys_t.KeyIterator./KeyIterator/k x))
   :qid internal_lib!keys_t.KeyIterator./KeyIterator/k_accessor_definition
)))
(assert
 (forall ((K&. Dcr) (K& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!keys_t.KeyIterator. K&. K&))
    (has_type (Poly%core!option.Option. (lib!keys_t.KeyIterator./KeyIterator/k (%Poly%lib!keys_t.KeyIterator.
        x
      ))
     ) (TYPE%core!option.Option. K&. K&)
   ))
   :pattern ((lib!keys_t.KeyIterator./KeyIterator/k (%Poly%lib!keys_t.KeyIterator. x))
    (has_type x (TYPE%lib!keys_t.KeyIterator. K&. K&))
   )
   :qid internal_lib!keys_t.KeyIterator./KeyIterator/k_invariant_definition
)))
(assert
 (forall ((x lib!keys_t.KeyIterator.)) (!
   (=>
    (is-lib!keys_t.KeyIterator./KeyIterator x)
    (height_lt (height (Poly%core!option.Option. (lib!keys_t.KeyIterator./KeyIterator/k x)))
     (height (Poly%lib!keys_t.KeyIterator. x))
   ))
   :pattern ((height (Poly%core!option.Option. (lib!keys_t.KeyIterator./KeyIterator/k x))))
   :qid prelude_datatype_height_lib!keys_t.KeyIterator./KeyIterator/k
)))
(assert
 (forall ((x lib!keys_t.KeyRange.)) (!
   (= x (%Poly%lib!keys_t.KeyRange. (Poly%lib!keys_t.KeyRange. x)))
   :pattern ((Poly%lib!keys_t.KeyRange. x))
   :qid internal_lib__keys_t__KeyRange_box_axiom_definition
)))
(assert
 (forall ((K&. Dcr) (K& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!keys_t.KeyRange. K&. K&))
    (= x (Poly%lib!keys_t.KeyRange. (%Poly%lib!keys_t.KeyRange. x)))
   )
   :pattern ((has_type x (TYPE%lib!keys_t.KeyRange. K&. K&)))
   :qid internal_lib__keys_t__KeyRange_unbox_axiom_definition
)))
(assert
 (forall ((K&. Dcr) (K& Type) (_lo! lib!keys_t.KeyIterator.) (_hi! lib!keys_t.KeyIterator.))
  (!
   (=>
    (and
     (has_type (Poly%lib!keys_t.KeyIterator. _lo!) (TYPE%lib!keys_t.KeyIterator. K&. K&))
     (has_type (Poly%lib!keys_t.KeyIterator. _hi!) (TYPE%lib!keys_t.KeyIterator. K&. K&))
    )
    (has_type (Poly%lib!keys_t.KeyRange. (lib!keys_t.KeyRange./KeyRange _lo! _hi!)) (TYPE%lib!keys_t.KeyRange.
      K&. K&
   )))
   :pattern ((has_type (Poly%lib!keys_t.KeyRange. (lib!keys_t.KeyRange./KeyRange _lo! _hi!))
     (TYPE%lib!keys_t.KeyRange. K&. K&)
   ))
   :qid internal_lib!keys_t.KeyRange./KeyRange_constructor_definition
)))
(assert
 (forall ((x lib!keys_t.KeyRange.)) (!
   (= (lib!keys_t.KeyRange./KeyRange/lo x) (lib!keys_t.KeyRange./KeyRange/?lo x))
   :pattern ((lib!keys_t.KeyRange./KeyRange/lo x))
   :qid internal_lib!keys_t.KeyRange./KeyRange/lo_accessor_definition
)))
(assert
 (forall ((K&. Dcr) (K& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!keys_t.KeyRange. K&. K&))
    (has_type (Poly%lib!keys_t.KeyIterator. (lib!keys_t.KeyRange./KeyRange/lo (%Poly%lib!keys_t.KeyRange.
        x
      ))
     ) (TYPE%lib!keys_t.KeyIterator. K&. K&)
   ))
   :pattern ((lib!keys_t.KeyRange./KeyRange/lo (%Poly%lib!keys_t.KeyRange. x)) (has_type
     x (TYPE%lib!keys_t.KeyRange. K&. K&)
   ))
   :qid internal_lib!keys_t.KeyRange./KeyRange/lo_invariant_definition
)))
(assert
 (forall ((x lib!keys_t.KeyRange.)) (!
   (= (lib!keys_t.KeyRange./KeyRange/hi x) (lib!keys_t.KeyRange./KeyRange/?hi x))
   :pattern ((lib!keys_t.KeyRange./KeyRange/hi x))
   :qid internal_lib!keys_t.KeyRange./KeyRange/hi_accessor_definition
)))
(assert
 (forall ((K&. Dcr) (K& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!keys_t.KeyRange. K&. K&))
    (has_type (Poly%lib!keys_t.KeyIterator. (lib!keys_t.KeyRange./KeyRange/hi (%Poly%lib!keys_t.KeyRange.
        x
      ))
     ) (TYPE%lib!keys_t.KeyIterator. K&. K&)
   ))
   :pattern ((lib!keys_t.KeyRange./KeyRange/hi (%Poly%lib!keys_t.KeyRange. x)) (has_type
     x (TYPE%lib!keys_t.KeyRange. K&. K&)
   ))
   :qid internal_lib!keys_t.KeyRange./KeyRange/hi_invariant_definition
)))
(assert
 (forall ((x lib!keys_t.KeyRange.)) (!
   (=>
    (is-lib!keys_t.KeyRange./KeyRange x)
    (height_lt (height (Poly%lib!keys_t.KeyIterator. (lib!keys_t.KeyRange./KeyRange/lo x)))
     (height (Poly%lib!keys_t.KeyRange. x))
   ))
   :pattern ((height (Poly%lib!keys_t.KeyIterator. (lib!keys_t.KeyRange./KeyRange/lo x))))
   :qid prelude_datatype_height_lib!keys_t.KeyRange./KeyRange/lo
)))
(assert
 (forall ((x lib!keys_t.KeyRange.)) (!
   (=>
    (is-lib!keys_t.KeyRange./KeyRange x)
    (height_lt (height (Poly%lib!keys_t.KeyIterator. (lib!keys_t.KeyRange./KeyRange/hi x)))
     (height (Poly%lib!keys_t.KeyRange. x))
   ))
   :pattern ((height (Poly%lib!keys_t.KeyIterator. (lib!keys_t.KeyRange./KeyRange/hi x))))
   :qid prelude_datatype_height_lib!keys_t.KeyRange./KeyRange/hi
)))
(assert
 (forall ((x lib!keys_t.SHTKey.)) (!
   (= x (%Poly%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey. x)))
   :pattern ((Poly%lib!keys_t.SHTKey. x))
   :qid internal_lib__keys_t__SHTKey_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!keys_t.SHTKey.)
    (= x (Poly%lib!keys_t.SHTKey. (%Poly%lib!keys_t.SHTKey. x)))
   )
   :pattern ((has_type x TYPE%lib!keys_t.SHTKey.))
   :qid internal_lib__keys_t__SHTKey_unbox_axiom_definition
)))
(assert
 (forall ((_ukey! Int)) (!
   (=>
    (uInv 64 _ukey!)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!keys_t.SHTKey./SHTKey _ukey!)) TYPE%lib!keys_t.SHTKey.)
   )
   :pattern ((has_type (Poly%lib!keys_t.SHTKey. (lib!keys_t.SHTKey./SHTKey _ukey!)) TYPE%lib!keys_t.SHTKey.))
   :qid internal_lib!keys_t.SHTKey./SHTKey_constructor_definition
)))
(assert
 (forall ((x lib!keys_t.SHTKey.)) (!
   (= (lib!keys_t.SHTKey./SHTKey/ukey x) (lib!keys_t.SHTKey./SHTKey/?ukey x))
   :pattern ((lib!keys_t.SHTKey./SHTKey/ukey x))
   :qid internal_lib!keys_t.SHTKey./SHTKey/ukey_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!keys_t.SHTKey.)
    (uInv 64 (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey. x)))
   )
   :pattern ((lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey. x)) (has_type x
     TYPE%lib!keys_t.SHTKey.
   ))
   :qid internal_lib!keys_t.SHTKey./SHTKey/ukey_invariant_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= x (%Poly%lib!message_t.Message. (Poly%lib!message_t.Message. x)))
   :pattern ((Poly%lib!message_t.Message. x))
   :qid internal_lib__message_t__Message_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!message_t.Message.)
    (= x (Poly%lib!message_t.Message. (%Poly%lib!message_t.Message. x)))
   )
   :pattern ((has_type x TYPE%lib!message_t.Message.))
   :qid internal_lib__message_t__Message_unbox_axiom_definition
)))
(assert
 (forall ((_key! lib!keys_t.SHTKey.)) (!
   (=>
    (has_type (Poly%lib!keys_t.SHTKey. _key!) TYPE%lib!keys_t.SHTKey.)
    (has_type (Poly%lib!message_t.Message. (lib!message_t.Message./GetRequest _key!))
     TYPE%lib!message_t.Message.
   ))
   :pattern ((has_type (Poly%lib!message_t.Message. (lib!message_t.Message./GetRequest _key!))
     TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./GetRequest_constructor_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./GetRequest/key x) (lib!message_t.Message./GetRequest/?key
     x
   ))
   :pattern ((lib!message_t.Message./GetRequest/key x))
   :qid internal_lib!message_t.Message./GetRequest/key_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!message_t.Message.)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!message_t.Message./GetRequest/key (%Poly%lib!message_t.Message.
        x
      ))
     ) TYPE%lib!keys_t.SHTKey.
   ))
   :pattern ((lib!message_t.Message./GetRequest/key (%Poly%lib!message_t.Message. x))
    (has_type x TYPE%lib!message_t.Message.)
   )
   :qid internal_lib!message_t.Message./GetRequest/key_invariant_definition
)))
(assert
 (forall ((_key! lib!keys_t.SHTKey.) (_value! core!option.Option.)) (!
   (=>
    (and
     (has_type (Poly%lib!keys_t.SHTKey. _key!) TYPE%lib!keys_t.SHTKey.)
     (has_type (Poly%core!option.Option. _value!) (TYPE%core!option.Option. $ (TYPE%vstd!seq.Seq.
        $ (UINT 8)
    ))))
    (has_type (Poly%lib!message_t.Message. (lib!message_t.Message./SetRequest _key! _value!))
     TYPE%lib!message_t.Message.
   ))
   :pattern ((has_type (Poly%lib!message_t.Message. (lib!message_t.Message./SetRequest _key!
       _value!
      )
     ) TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./SetRequest_constructor_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./SetRequest/key x) (lib!message_t.Message./SetRequest/?key
     x
   ))
   :pattern ((lib!message_t.Message./SetRequest/key x))
   :qid internal_lib!message_t.Message./SetRequest/key_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!message_t.Message.)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!message_t.Message./SetRequest/key (%Poly%lib!message_t.Message.
        x
      ))
     ) TYPE%lib!keys_t.SHTKey.
   ))
   :pattern ((lib!message_t.Message./SetRequest/key (%Poly%lib!message_t.Message. x))
    (has_type x TYPE%lib!message_t.Message.)
   )
   :qid internal_lib!message_t.Message./SetRequest/key_invariant_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./SetRequest/value x) (lib!message_t.Message./SetRequest/?value
     x
   ))
   :pattern ((lib!message_t.Message./SetRequest/value x))
   :qid internal_lib!message_t.Message./SetRequest/value_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!message_t.Message.)
    (has_type (Poly%core!option.Option. (lib!message_t.Message./SetRequest/value (%Poly%lib!message_t.Message.
        x
      ))
     ) (TYPE%core!option.Option. $ (TYPE%vstd!seq.Seq. $ (UINT 8)))
   ))
   :pattern ((lib!message_t.Message./SetRequest/value (%Poly%lib!message_t.Message. x))
    (has_type x TYPE%lib!message_t.Message.)
   )
   :qid internal_lib!message_t.Message./SetRequest/value_invariant_definition
)))
(assert
 (forall ((_key! lib!keys_t.SHTKey.) (_value! core!option.Option.)) (!
   (=>
    (and
     (has_type (Poly%lib!keys_t.SHTKey. _key!) TYPE%lib!keys_t.SHTKey.)
     (has_type (Poly%core!option.Option. _value!) (TYPE%core!option.Option. $ (TYPE%vstd!seq.Seq.
        $ (UINT 8)
    ))))
    (has_type (Poly%lib!message_t.Message. (lib!message_t.Message./Reply _key! _value!))
     TYPE%lib!message_t.Message.
   ))
   :pattern ((has_type (Poly%lib!message_t.Message. (lib!message_t.Message./Reply _key!
       _value!
      )
     ) TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./Reply_constructor_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./Reply/key x) (lib!message_t.Message./Reply/?key x))
   :pattern ((lib!message_t.Message./Reply/key x))
   :qid internal_lib!message_t.Message./Reply/key_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!message_t.Message.)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!message_t.Message./Reply/key (%Poly%lib!message_t.Message.
        x
      ))
     ) TYPE%lib!keys_t.SHTKey.
   ))
   :pattern ((lib!message_t.Message./Reply/key (%Poly%lib!message_t.Message. x)) (has_type
     x TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./Reply/key_invariant_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./Reply/value x) (lib!message_t.Message./Reply/?value x))
   :pattern ((lib!message_t.Message./Reply/value x))
   :qid internal_lib!message_t.Message./Reply/value_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!message_t.Message.)
    (has_type (Poly%core!option.Option. (lib!message_t.Message./Reply/value (%Poly%lib!message_t.Message.
        x
      ))
     ) (TYPE%core!option.Option. $ (TYPE%vstd!seq.Seq. $ (UINT 8)))
   ))
   :pattern ((lib!message_t.Message./Reply/value (%Poly%lib!message_t.Message. x)) (has_type
     x TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./Reply/value_invariant_definition
)))
(assert
 (forall ((_key! lib!keys_t.SHTKey.) (_id! lib!abstract_end_point_t.AbstractEndPoint.))
  (!
   (=>
    (has_type (Poly%lib!keys_t.SHTKey. _key!) TYPE%lib!keys_t.SHTKey.)
    (has_type (Poly%lib!message_t.Message. (lib!message_t.Message./Redirect _key! _id!))
     TYPE%lib!message_t.Message.
   ))
   :pattern ((has_type (Poly%lib!message_t.Message. (lib!message_t.Message./Redirect _key!
       _id!
      )
     ) TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./Redirect_constructor_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./Redirect/key x) (lib!message_t.Message./Redirect/?key x))
   :pattern ((lib!message_t.Message./Redirect/key x))
   :qid internal_lib!message_t.Message./Redirect/key_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!message_t.Message.)
    (has_type (Poly%lib!keys_t.SHTKey. (lib!message_t.Message./Redirect/key (%Poly%lib!message_t.Message.
        x
      ))
     ) TYPE%lib!keys_t.SHTKey.
   ))
   :pattern ((lib!message_t.Message./Redirect/key (%Poly%lib!message_t.Message. x)) (
     has_type x TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./Redirect/key_invariant_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./Redirect/id x) (lib!message_t.Message./Redirect/?id x))
   :pattern ((lib!message_t.Message./Redirect/id x))
   :qid internal_lib!message_t.Message./Redirect/id_accessor_definition
)))
(assert
 (forall ((_range! lib!keys_t.KeyRange.) (_recipient! lib!abstract_end_point_t.AbstractEndPoint.))
  (!
   (=>
    (has_type (Poly%lib!keys_t.KeyRange. _range!) (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.))
    (has_type (Poly%lib!message_t.Message. (lib!message_t.Message./Shard _range! _recipient!))
     TYPE%lib!message_t.Message.
   ))
   :pattern ((has_type (Poly%lib!message_t.Message. (lib!message_t.Message./Shard _range!
       _recipient!
      )
     ) TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./Shard_constructor_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./Shard/range x) (lib!message_t.Message./Shard/?range x))
   :pattern ((lib!message_t.Message./Shard/range x))
   :qid internal_lib!message_t.Message./Shard/range_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!message_t.Message.)
    (has_type (Poly%lib!keys_t.KeyRange. (lib!message_t.Message./Shard/range (%Poly%lib!message_t.Message.
        x
      ))
     ) (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
   ))
   :pattern ((lib!message_t.Message./Shard/range (%Poly%lib!message_t.Message. x)) (has_type
     x TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./Shard/range_invariant_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./Shard/recipient x) (lib!message_t.Message./Shard/?recipient
     x
   ))
   :pattern ((lib!message_t.Message./Shard/recipient x))
   :qid internal_lib!message_t.Message./Shard/recipient_accessor_definition
)))
(assert
 (forall ((_range! lib!keys_t.KeyRange.) (_h! vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.))
  (!
   (=>
    (has_type (Poly%lib!keys_t.KeyRange. _range!) (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.))
    (has_type (Poly%lib!message_t.Message. (lib!message_t.Message./Delegate _range! _h!))
     TYPE%lib!message_t.Message.
   ))
   :pattern ((has_type (Poly%lib!message_t.Message. (lib!message_t.Message./Delegate _range!
       _h!
      )
     ) TYPE%lib!message_t.Message.
   ))
   :qid internal_lib!message_t.Message./Delegate_constructor_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./Delegate/range x) (lib!message_t.Message./Delegate/?range
     x
   ))
   :pattern ((lib!message_t.Message./Delegate/range x))
   :qid internal_lib!message_t.Message./Delegate/range_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!message_t.Message.)
    (has_type (Poly%lib!keys_t.KeyRange. (lib!message_t.Message./Delegate/range (%Poly%lib!message_t.Message.
        x
      ))
     ) (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
   ))
   :pattern ((lib!message_t.Message./Delegate/range (%Poly%lib!message_t.Message. x))
    (has_type x TYPE%lib!message_t.Message.)
   )
   :qid internal_lib!message_t.Message./Delegate/range_invariant_definition
)))
(assert
 (forall ((x lib!message_t.Message.)) (!
   (= (lib!message_t.Message./Delegate/h x) (lib!message_t.Message./Delegate/?h x))
   :pattern ((lib!message_t.Message./Delegate/h x))
   :qid internal_lib!message_t.Message./Delegate/h_accessor_definition
)))
(assert
 (forall ((x lib!single_message_t.SingleMessage.)) (!
   (= x (%Poly%lib!single_message_t.SingleMessage. (Poly%lib!single_message_t.SingleMessage.
      x
   )))
   :pattern ((Poly%lib!single_message_t.SingleMessage. x))
   :qid internal_lib__single_message_t__SingleMessage_box_axiom_definition
)))
(assert
 (forall ((MT&. Dcr) (MT& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!single_message_t.SingleMessage. MT&. MT&))
    (= x (Poly%lib!single_message_t.SingleMessage. (%Poly%lib!single_message_t.SingleMessage.
       x
   ))))
   :pattern ((has_type x (TYPE%lib!single_message_t.SingleMessage. MT&. MT&)))
   :qid internal_lib__single_message_t__SingleMessage_unbox_axiom_definition
)))
(assert
 (forall ((MT&. Dcr) (MT& Type) (_seqno! Int) (_dst! lib!abstract_end_point_t.AbstractEndPoint.)
   (_m! Poly)
  ) (!
   (=>
    (and
     (<= 0 _seqno!)
     (has_type _m! MT&)
    )
    (has_type (Poly%lib!single_message_t.SingleMessage. (lib!single_message_t.SingleMessage./Message
       _seqno! _dst! _m!
      )
     ) (TYPE%lib!single_message_t.SingleMessage. MT&. MT&)
   ))
   :pattern ((has_type (Poly%lib!single_message_t.SingleMessage. (lib!single_message_t.SingleMessage./Message
       _seqno! _dst! _m!
      )
     ) (TYPE%lib!single_message_t.SingleMessage. MT&. MT&)
   ))
   :qid internal_lib!single_message_t.SingleMessage./Message_constructor_definition
)))
(assert
 (forall ((x lib!single_message_t.SingleMessage.)) (!
   (= (lib!single_message_t.SingleMessage./Message/seqno x) (lib!single_message_t.SingleMessage./Message/?seqno
     x
   ))
   :pattern ((lib!single_message_t.SingleMessage./Message/seqno x))
   :qid internal_lib!single_message_t.SingleMessage./Message/seqno_accessor_definition
)))
(assert
 (forall ((MT&. Dcr) (MT& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!single_message_t.SingleMessage. MT&. MT&))
    (<= 0 (lib!single_message_t.SingleMessage./Message/seqno (%Poly%lib!single_message_t.SingleMessage.
       x
   ))))
   :pattern ((lib!single_message_t.SingleMessage./Message/seqno (%Poly%lib!single_message_t.SingleMessage.
      x
     )
    ) (has_type x (TYPE%lib!single_message_t.SingleMessage. MT&. MT&))
   )
   :qid internal_lib!single_message_t.SingleMessage./Message/seqno_invariant_definition
)))
(assert
 (forall ((x lib!single_message_t.SingleMessage.)) (!
   (= (lib!single_message_t.SingleMessage./Message/dst x) (lib!single_message_t.SingleMessage./Message/?dst
     x
   ))
   :pattern ((lib!single_message_t.SingleMessage./Message/dst x))
   :qid internal_lib!single_message_t.SingleMessage./Message/dst_accessor_definition
)))
(assert
 (forall ((x lib!single_message_t.SingleMessage.)) (!
   (= (lib!single_message_t.SingleMessage./Message/m x) (lib!single_message_t.SingleMessage./Message/?m
     x
   ))
   :pattern ((lib!single_message_t.SingleMessage./Message/m x))
   :qid internal_lib!single_message_t.SingleMessage./Message/m_accessor_definition
)))
(assert
 (forall ((MT&. Dcr) (MT& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!single_message_t.SingleMessage. MT&. MT&))
    (has_type (lib!single_message_t.SingleMessage./Message/m (%Poly%lib!single_message_t.SingleMessage.
       x
      )
     ) MT&
   ))
   :pattern ((lib!single_message_t.SingleMessage./Message/m (%Poly%lib!single_message_t.SingleMessage.
      x
     )
    ) (has_type x (TYPE%lib!single_message_t.SingleMessage. MT&. MT&))
   )
   :qid internal_lib!single_message_t.SingleMessage./Message/m_invariant_definition
)))
(assert
 (forall ((MT&. Dcr) (MT& Type) (_ack_seqno! Int)) (!
   (=>
    (<= 0 _ack_seqno!)
    (has_type (Poly%lib!single_message_t.SingleMessage. (lib!single_message_t.SingleMessage./Ack
       _ack_seqno!
      )
     ) (TYPE%lib!single_message_t.SingleMessage. MT&. MT&)
   ))
   :pattern ((has_type (Poly%lib!single_message_t.SingleMessage. (lib!single_message_t.SingleMessage./Ack
       _ack_seqno!
      )
     ) (TYPE%lib!single_message_t.SingleMessage. MT&. MT&)
   ))
   :qid internal_lib!single_message_t.SingleMessage./Ack_constructor_definition
)))
(assert
 (forall ((x lib!single_message_t.SingleMessage.)) (!
   (= (lib!single_message_t.SingleMessage./Ack/ack_seqno x) (lib!single_message_t.SingleMessage./Ack/?ack_seqno
     x
   ))
   :pattern ((lib!single_message_t.SingleMessage./Ack/ack_seqno x))
   :qid internal_lib!single_message_t.SingleMessage./Ack/ack_seqno_accessor_definition
)))
(assert
 (forall ((MT&. Dcr) (MT& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!single_message_t.SingleMessage. MT&. MT&))
    (<= 0 (lib!single_message_t.SingleMessage./Ack/ack_seqno (%Poly%lib!single_message_t.SingleMessage.
       x
   ))))
   :pattern ((lib!single_message_t.SingleMessage./Ack/ack_seqno (%Poly%lib!single_message_t.SingleMessage.
      x
     )
    ) (has_type x (TYPE%lib!single_message_t.SingleMessage. MT&. MT&))
   )
   :qid internal_lib!single_message_t.SingleMessage./Ack/ack_seqno_invariant_definition
)))
(assert
 (forall ((MT&. Dcr) (MT& Type)) (!
   (has_type (Poly%lib!single_message_t.SingleMessage. lib!single_message_t.SingleMessage./InvalidMessage)
    (TYPE%lib!single_message_t.SingleMessage. MT&. MT&)
   )
   :pattern ((has_type (Poly%lib!single_message_t.SingleMessage. lib!single_message_t.SingleMessage./InvalidMessage)
     (TYPE%lib!single_message_t.SingleMessage. MT&. MT&)
   ))
   :qid internal_lib!single_message_t.SingleMessage./InvalidMessage_constructor_definition
)))
(assert
 (forall ((x lib!single_message_t.SingleMessage.)) (!
   (=>
    (is-lib!single_message_t.SingleMessage./Message x)
    (height_lt (height (lib!single_message_t.SingleMessage./Message/m x)) (height (Poly%lib!single_message_t.SingleMessage.
       x
   ))))
   :pattern ((height (lib!single_message_t.SingleMessage./Message/m x)))
   :qid prelude_datatype_height_lib!single_message_t.SingleMessage./Message/m
)))
(assert
 (forall ((x tuple%0.)) (!
   (= x (%Poly%tuple%0. (Poly%tuple%0. x)))
   :pattern ((Poly%tuple%0. x))
   :qid internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%tuple%0.)
    (= x (Poly%tuple%0. (%Poly%tuple%0. x)))
   )
   :pattern ((has_type x TYPE%tuple%0.))
   :qid internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (has_type (Poly%tuple%0. x) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x) TYPE%tuple%0.))
   :qid internal_crate__tuple__0_has_type_always_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= x (%Poly%tuple%2. (Poly%tuple%2. x)))
   :pattern ((Poly%tuple%2. x))
   :qid internal_crate__tuple__2_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (= x (Poly%tuple%2. (%Poly%tuple%2. x)))
   )
   :pattern ((has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__tuple__2_unbox_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (_0! Poly) (_1! Poly)) (!
   (=>
    (and
     (has_type _0! T%0&)
     (has_type _1! T%1&)
    )
    (has_type (Poly%tuple%2. (tuple%2./tuple%2 _0! _1!)) (TYPE%tuple%2. T%0&. T%0& T%1&.
      T%1&
   )))
   :pattern ((has_type (Poly%tuple%2. (tuple%2./tuple%2 _0! _1!)) (TYPE%tuple%2. T%0&.
      T%0& T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2_constructor_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= (tuple%2./tuple%2/0 x) (tuple%2./tuple%2/?0 x))
   :pattern ((tuple%2./tuple%2/0 x))
   :qid internal_tuple__2./tuple__2/0_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (has_type (tuple%2./tuple%2/0 (%Poly%tuple%2. x)) T%0&)
   )
   :pattern ((tuple%2./tuple%2/0 (%Poly%tuple%2. x)) (has_type x (TYPE%tuple%2. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2/0_invariant_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= (tuple%2./tuple%2/1 x) (tuple%2./tuple%2/?1 x))
   :pattern ((tuple%2./tuple%2/1 x))
   :qid internal_tuple__2./tuple__2/1_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (has_type (tuple%2./tuple%2/1 (%Poly%tuple%2. x)) T%1&)
   )
   :pattern ((tuple%2./tuple%2/1 (%Poly%tuple%2. x)) (has_type x (TYPE%tuple%2. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2/1_invariant_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    (is-tuple%2./tuple%2 x)
    (height_lt (height (tuple%2./tuple%2/0 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/0 x)))
   :qid prelude_datatype_height_tuple%2./tuple%2/0
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    (is-tuple%2./tuple%2 x)
    (height_lt (height (tuple%2./tuple%2/1 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/1 x)))
   :qid prelude_datatype_height_tuple%2./tuple%2/1
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (deep Bool) (x Poly) (y Poly))
  (!
   (=>
    (and
     (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
     (has_type y (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
     (ext_eq deep T%0& (tuple%2./tuple%2/0 (%Poly%tuple%2. x)) (tuple%2./tuple%2/0 (%Poly%tuple%2.
        y
     )))
     (ext_eq deep T%1& (tuple%2./tuple%2/1 (%Poly%tuple%2. x)) (tuple%2./tuple%2/1 (%Poly%tuple%2.
        y
    ))))
    (ext_eq deep (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&) x y)
   )
   :pattern ((ext_eq deep (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&) x y))
   :qid internal_tuple__2./tuple__2_ext_equal_definition
)))

;; Traits
(declare-fun tr_bound%vstd!view.View. (Dcr Type) Bool)
(declare-fun tr_bound%vstd!std_specs.vec.VecAdditionalSpecFns. (Dcr Type Dcr Type)
 Bool
)
(declare-fun tr_bound%lib!marshal_v.Marshalable. (Dcr Type) Bool)

;; Associated-Type-Impls
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (REF A&.) A&) (proj%%vstd!view.View./V A&. A&))
   :pattern ((proj%%vstd!view.View./V (REF A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (REF A&.) A&) (proj%vstd!view.View./V A&. A&))
   :pattern ((proj%vstd!view.View./V (REF A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (BOX A&.) A&) (proj%%vstd!view.View./V A&. A&))
   :pattern ((proj%%vstd!view.View./V (BOX A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (BOX A&.) A&) (proj%vstd!view.View./V A&. A&))
   :pattern ((proj%vstd!view.View./V (BOX A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (RC A&.) A&) (proj%%vstd!view.View./V A&. A&))
   :pattern ((proj%%vstd!view.View./V (RC A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (RC A&.) A&) (proj%vstd!view.View./V A&. A&))
   :pattern ((proj%vstd!view.View./V (RC A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (ARC A&.) A&) (proj%%vstd!view.View./V A&. A&))
   :pattern ((proj%%vstd!view.View./V (ARC A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (ARC A&.) A&) (proj%vstd!view.View./V A&. A&))
   :pattern ((proj%vstd!view.View./V (ARC A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (= (proj%%vstd!view.View./V $ TYPE%tuple%0.) $)
)
(assert
 (= (proj%vstd!view.View./V $ TYPE%tuple%0.) TYPE%tuple%0.)
)
(assert
 (= (proj%%vstd!view.View./V $ BOOL) $)
)
(assert
 (= (proj%vstd!view.View./V $ BOOL) BOOL)
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT 8)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT 8)) (UINT 8))
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT 64)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT 64)) (UINT 64))
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT SZ)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT SZ)) (UINT SZ))
)
(assert
 (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type)) (!
   (= (proj%%vstd!view.View./V $ (TYPE%tuple%2. A0&. A0& A1&. A1&)) $)
   :pattern ((proj%%vstd!view.View./V $ (TYPE%tuple%2. A0&. A0& A1&. A1&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type)) (!
   (= (proj%vstd!view.View./V $ (TYPE%tuple%2. A0&. A0& A1&. A1&)) (TYPE%tuple%2. (proj%%vstd!view.View./V
      A0&. A0&
     ) (proj%vstd!view.View./V A0&. A0&) (proj%%vstd!view.View./V A1&. A1&) (proj%vstd!view.View./V
      A1&. A1&
   )))
   :pattern ((proj%vstd!view.View./V $ (TYPE%tuple%2. A0&. A0& A1&. A1&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)) $)
   :pattern ((proj%%vstd!view.View./V $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)) (TYPE%vstd!seq.Seq.
     T&. T&
   ))
   :pattern ((proj%vstd!view.View./V $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))

;; Function-Decl vstd::std_specs::vec::VecAdditionalSpecFns::spec_len
(declare-fun vstd!std_specs.vec.VecAdditionalSpecFns.spec_len.? (Dcr Type Dcr Type
  Poly
 ) Poly
)
(declare-fun vstd!std_specs.vec.VecAdditionalSpecFns.spec_len%default%.? (Dcr Type
  Dcr Type Poly
 ) Poly
)

;; Function-Decl vstd::std_specs::vec::VecAdditionalSpecFns::spec_index
(declare-fun vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? (Dcr Type Dcr Type
  Poly Poly
 ) Poly
)
(declare-fun vstd!std_specs.vec.VecAdditionalSpecFns.spec_index%default%.? (Dcr Type
  Dcr Type Poly Poly
 ) Poly
)

;; Function-Decl vstd::std_specs::vec::spec_vec_len
(declare-fun vstd!std_specs.vec.spec_vec_len.? (Dcr Type Dcr Type Poly) Int)

;; Function-Decl vstd::bytes::spec_u64_to_le_bytes
(declare-fun vstd!bytes.spec_u64_to_le_bytes.? (Poly) vstd!seq.Seq<u8.>.)

;; Function-Decl vstd::map::impl&%0::empty
(declare-fun vstd!map.impl&%0.empty.? (Dcr Type Dcr Type) Poly)

;; Function-Decl vstd::map::impl&%0::dom
(declare-fun vstd!map.impl&%0.dom.? (Dcr Type Dcr Type Poly) Poly)

;; Function-Decl vstd::map::impl&%0::index
(declare-fun vstd!map.impl&%0.index.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::spec_index
(declare-fun vstd!map.impl&%0.spec_index.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::insert
(declare-fun vstd!map.impl&%0.insert.? (Dcr Type Dcr Type Poly Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::remove
(declare-fun vstd!map.impl&%0.remove.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::map_lib::impl&%0::contains_pair
(declare-fun vstd!map_lib.impl&%0.contains_pair.? (Dcr Type Dcr Type Poly Poly Poly)
 Bool
)

;; Function-Decl vstd::seq::Seq::empty
(declare-fun vstd!seq.Seq.empty.? (Dcr Type) Poly)

;; Function-Decl vstd::seq::Seq::new
(declare-fun vstd!seq.Seq.new.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::len
(declare-fun vstd!seq.Seq.len.? (Dcr Type Poly) Int)

;; Function-Decl vstd::seq::Seq::index
(declare-fun vstd!seq.Seq.index.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::impl&%0::spec_index
(declare-fun vstd!seq.impl&%0.spec_index.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::push
(declare-fun vstd!seq.Seq.push.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::update
(declare-fun vstd!seq.Seq.update.? (Dcr Type Poly Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::subrange
(declare-fun vstd!seq.Seq.subrange.? (Dcr Type Poly Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::add
(declare-fun vstd!seq.Seq.add.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::impl&%0::spec_add
(declare-fun vstd!seq.impl&%0.spec_add.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::last
(declare-fun vstd!seq.Seq.last.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::seq_lib::impl&%0::filter
(declare-fun vstd!seq_lib.impl&%0.filter.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq_lib::impl&%0::contains
(declare-fun vstd!seq_lib.impl&%0.contains.? (Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::seq_lib::impl&%0::drop_last
(declare-fun vstd!seq_lib.impl&%0.drop_last.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::seq_lib::impl&%0::to_set
(declare-fun vstd!seq_lib.impl&%0.to_set.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::seq_lib::impl&%0::fold_left
(declare-fun vstd!seq_lib.impl&%0.fold_left.? (Dcr Type Dcr Type Poly Poly Poly) Poly)
(declare-fun vstd!seq_lib.impl&%0.rec%fold_left.? (Dcr Type Dcr Type Poly Poly Poly
  Fuel
 ) Poly
)

;; Function-Decl vstd::set::impl&%0::empty
(declare-fun vstd!set.impl&%0.empty.? (Dcr Type) Poly)

;; Function-Decl vstd::set::impl&%0::new
(declare-fun vstd!set.impl&%0.new.? (Dcr Type Dcr Type Poly) Poly)

;; Function-Decl vstd::set::impl&%0::contains
(declare-fun vstd!set.impl&%0.contains.? (Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::set::impl&%0::insert
(declare-fun vstd!set.impl&%0.insert.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::remove
(declare-fun vstd!set.impl&%0.remove.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::union
(declare-fun vstd!set.impl&%0.union.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::intersect
(declare-fun vstd!set.impl&%0.intersect.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::difference
(declare-fun vstd!set.impl&%0.difference.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::complement
(declare-fun vstd!set.impl&%0.complement.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::set::impl&%0::finite
(declare-fun vstd!set.impl&%0.finite.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::set::impl&%0::len
(declare-fun vstd!set.impl&%0.len.? (Dcr Type Poly) Int)

;; Function-Decl vstd::set::impl&%0::choose
(declare-fun vstd!set.impl&%0.choose.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::set::impl&%0::mk_map
(declare-fun vstd!set.impl&%0.mk_map.? (Dcr Type Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::view::View::view
(declare-fun vstd!view.View.view.? (Dcr Type Poly) Poly)
(declare-fun vstd!view.View.view%default%.? (Dcr Type Poly) Poly)

;; Function-Decl lib::cmessage_v::optional_value_view
(declare-fun lib!cmessage_v.optional_value_view.? (Poly) core!option.Option.)

;; Function-Decl lib::cmessage_v::CMessage::view
(declare-fun lib!cmessage_v.impl&%1.view.? (Poly) lib!message_t.Message.)

;; Function-Decl lib::cmessage_v::CSingleMessage::view
(declare-fun lib!cmessage_v.impl&%2.view.? (Poly) lib!single_message_t.SingleMessage.)

;; Function-Decl lib::marshal_ironsht_specific_v::ckeyhashmap_max_serialized_size
(declare-fun lib!marshal_ironsht_specific_v.ckeyhashmap_max_serialized_size.? (Poly)
 Int
)

;; Function-Decl lib::keys_t::KeyRange::forward_bijection_for_view_equality_do_not_use_for_anything_else
(declare-fun lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
 (Poly) tuple%2.
)

;; Function-Decl lib::io_t::EndPoint::forward_bijection_for_view_equality_do_not_use_for_anything_else
(declare-fun lib!marshal_ironsht_specific_v.impl&%7.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
 (Poly) alloc!vec.Vec<u8./alloc!alloc.Global.>.
)

;; Function-Decl lib::keys_t::SHTKey::forward_bijection_for_view_equality_do_not_use_for_anything_else
(declare-fun lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
 (Poly) Int
)

;; Function-Decl lib::marshal_v::Marshalable::is_marshalable
(declare-fun lib!marshal_v.Marshalable.is_marshalable.? (Dcr Type Poly) Poly)
(declare-fun lib!marshal_v.Marshalable.is_marshalable%default%.? (Dcr Type Poly) Poly)

;; Function-Decl lib::marshal_v::Marshalable::ghost_serialize
(declare-fun lib!marshal_v.Marshalable.ghost_serialize.? (Dcr Type Poly) Poly)
(declare-fun lib!marshal_v.Marshalable.ghost_serialize%default%.? (Dcr Type Poly)
 Poly
)

;; Function-Decl lib::marshal_v::Marshalable::view_equal
(declare-fun lib!marshal_v.Marshalable.view_equal.? (Dcr Type Poly Poly) Poly)
(declare-fun lib!marshal_v.Marshalable.view_equal%default%.? (Dcr Type Poly Poly)
 Poly
)

;; Function-Decl lib::hashmap_t::CKeyHashMap::view
(declare-fun lib!hashmap_t.impl&%0.view.? (Poly) vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.)

;; Function-Decl lib::hashmap_t::CKeyHashMap::spec_to_vec
(declare-fun lib!hashmap_t.impl&%0.spec_to_vec.? (Poly) alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.)

;; Function-Decl lib::hashmap_t::CKeyHashMap::spec_from_vec
(declare-fun lib!hashmap_t.impl&%0.spec_from_vec.? (Poly) lib!hashmap_t.CKeyHashMap.)

;; Function-Decl lib::hashmap_t::CKeyKV::view
(declare-fun lib!hashmap_t.impl&%1.view.? (Poly) tuple%2.)

;; Function-Decl lib::hashmap_t::ckeykvlt
(declare-fun lib!hashmap_t.ckeykvlt.? (Poly Poly) Bool)

;; Function-Decl lib::hashmap_t::spec_sorted_keys
(declare-fun lib!hashmap_t.spec_sorted_keys.? (Poly) Bool)

;; Function-Decl lib::io_t::EndPoint::view
(declare-fun lib!io_t.impl&%5.view.? (Poly) lib!abstract_end_point_t.AbstractEndPoint.)

;; Function-Axioms vstd::std_specs::vec::VecAdditionalSpecFns::spec_len
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!std_specs.vec.VecAdditionalSpecFns.spec_len.? Self%&. Self%& T&. T&
      self!
     ) NAT
   ))
   :pattern ((vstd!std_specs.vec.VecAdditionalSpecFns.spec_len.? Self%&. Self%& T&. T&
     self!
   ))
   :qid internal_vstd!std_specs.vec.VecAdditionalSpecFns.spec_len.?_pre_post_definition
)))

;; Function-Specs vstd::std_specs::vec::VecAdditionalSpecFns::spec_index
(declare-fun req%vstd!std_specs.vec.VecAdditionalSpecFns.spec_index. (Dcr Type Dcr
  Type Poly Poly
 ) Bool
)
(declare-const %%global_location_label%%0 Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (
   !
   (= (req%vstd!std_specs.vec.VecAdditionalSpecFns.spec_index. Self%&. Self%& T&. T& self!
     i!
    ) (=>
     %%global_location_label%%0
     (and
      (<= 0 (%I i!))
      (< (%I i!) (%I (vstd!std_specs.vec.VecAdditionalSpecFns.spec_len.? Self%&. Self%& T&.
         T& self!
   ))))))
   :pattern ((req%vstd!std_specs.vec.VecAdditionalSpecFns.spec_index. Self%&. Self%& T&.
     T& self! i!
   ))
   :qid internal_req__vstd!std_specs.vec.VecAdditionalSpecFns.spec_index._definition
)))

;; Function-Axioms vstd::std_specs::vec::VecAdditionalSpecFns::spec_index
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (
   !
   (=>
    (and
     (has_type self! Self%&)
     (has_type i! INT)
    )
    (has_type (vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? Self%&. Self%& T&.
      T& self! i!
     ) T&
   ))
   :pattern ((vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? Self%&. Self%& T&.
     T& self! i!
   ))
   :qid internal_vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.?_pre_post_definition
)))

;; Function-Axioms vstd::view::View::view
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!view.View.view.? Self%&. Self%& self!) (proj%vstd!view.View./V Self%&.
      Self%&
   )))
   :pattern ((vstd!view.View.view.? Self%&. Self%& self!))
   :qid internal_vstd!view.View.view.?_pre_post_definition
)))

;; Function-Axioms vstd::seq::Seq::len
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
    (<= 0 (vstd!seq.Seq.len.? A&. A& self!))
   )
   :pattern ((vstd!seq.Seq.len.? A&. A& self!))
   :qid internal_vstd!seq.Seq.len.?_pre_post_definition
)))

;; Function-Specs vstd::seq::Seq::index
(declare-fun req%vstd!seq.Seq.index. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%1 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (= (req%vstd!seq.Seq.index. A&. A& self! i!) (=>
     %%global_location_label%%1
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.Seq.index. A&. A& self! i!))
   :qid internal_req__vstd!seq.Seq.index._definition
)))

;; Function-Axioms vstd::seq::Seq::index
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (has_type (vstd!seq.Seq.index.? A&. A& self! i!) A&)
   )
   :pattern ((vstd!seq.Seq.index.? A&. A& self! i!))
   :qid internal_vstd!seq.Seq.index.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::vec::spec_vec_len
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type) (v! Poly)) (!
   (=>
    (has_type v! (TYPE%alloc!vec.Vec. T&. T& A&. A&))
    (uInv SZ (vstd!std_specs.vec.spec_vec_len.? T&. T& A&. A& v!))
   )
   :pattern ((vstd!std_specs.vec.spec_vec_len.? T&. T& A&. A& v!))
   :qid internal_vstd!std_specs.vec.spec_vec_len.?_pre_post_definition
)))

;; Function-Specs vstd::std_specs::vec::axiom_spec_len
(declare-fun ens%vstd!std_specs.vec.axiom_spec_len. (Dcr Type Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (v! Poly)) (!
   (= (ens%vstd!std_specs.vec.axiom_spec_len. A&. A& v!) (= (vstd!std_specs.vec.spec_vec_len.?
      A&. A& $ TYPE%alloc!alloc.Global. v!
     ) (vstd!seq.Seq.len.? A&. A& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. A&. A& $
        TYPE%alloc!alloc.Global.
       ) v!
   ))))
   :pattern ((ens%vstd!std_specs.vec.axiom_spec_len. A&. A& v!))
   :qid internal_ens__vstd!std_specs.vec.axiom_spec_len._definition
)))

;; Broadcast vstd::std_specs::vec::axiom_spec_len
(assert
 (forall ((A&. Dcr) (A& Type) (v! Poly)) (!
   (=>
    (has_type v! (TYPE%alloc!vec.Vec. A&. A& $ TYPE%alloc!alloc.Global.))
    (= (vstd!std_specs.vec.spec_vec_len.? A&. A& $ TYPE%alloc!alloc.Global. v!) (vstd!seq.Seq.len.?
      A&. A& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. A&. A& $ TYPE%alloc!alloc.Global.)
       v!
   ))))
   :pattern ((vstd!std_specs.vec.spec_vec_len.? A&. A& $ TYPE%alloc!alloc.Global. v!))
   :qid user_vstd__std_specs__vec__axiom_spec_len_0
)))

;; Function-Axioms vstd::seq::Seq::empty
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (has_type (vstd!seq.Seq.empty.? A&. A&) (TYPE%vstd!seq.Seq. A&. A&))
   :pattern ((vstd!seq.Seq.empty.? A&. A&))
   :qid internal_vstd!seq.Seq.empty.?_pre_post_definition
)))

;; Function-Axioms vstd::seq::Seq::push
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!seq.Seq.push.? A&. A& self! a!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.Seq.push.? A&. A& self! a!))
   :qid internal_vstd!seq.Seq.push.?_pre_post_definition
)))

;; Function-Specs vstd::seq::impl&%0::spec_index
(declare-fun req%vstd!seq.impl&%0.spec_index. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%2 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (= (req%vstd!seq.impl&%0.spec_index. A&. A& self! i!) (=>
     %%global_location_label%%2
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.impl&%0.spec_index. A&. A& self! i!))
   :qid internal_req__vstd!seq.impl&__0.spec_index._definition
)))

;; Function-Axioms vstd::seq::impl&%0::spec_index
(assert
 (fuel_bool_default fuel%vstd!seq.impl&%0.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq.impl&%0.spec_index.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
    (= (vstd!seq.impl&%0.spec_index.? A&. A& self! i!) (vstd!seq.Seq.index.? A&. A& self!
      i!
    ))
    :pattern ((vstd!seq.impl&%0.spec_index.? A&. A& self! i!))
    :qid internal_vstd!seq.impl&__0.spec_index.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (has_type (vstd!seq.impl&%0.spec_index.? A&. A& self! i!) A&)
   )
   :pattern ((vstd!seq.impl&%0.spec_index.? A&. A& self! i!))
   :qid internal_vstd!seq.impl&__0.spec_index.?_pre_post_definition
)))

;; Function-Specs vstd::seq::Seq::subrange
(declare-fun req%vstd!seq.Seq.subrange. (Dcr Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%3 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (start_inclusive! Poly) (end_exclusive! Poly))
  (!
   (= (req%vstd!seq.Seq.subrange. A&. A& self! start_inclusive! end_exclusive!) (=>
     %%global_location_label%%3
     (and
      (and
       (<= 0 (%I start_inclusive!))
       (<= (%I start_inclusive!) (%I end_exclusive!))
      )
      (<= (%I end_exclusive!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.Seq.subrange. A&. A& self! start_inclusive! end_exclusive!))
   :qid internal_req__vstd!seq.Seq.subrange._definition
)))

;; Function-Axioms vstd::seq::Seq::subrange
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (start_inclusive! Poly) (end_exclusive! Poly))
  (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type start_inclusive! INT)
     (has_type end_exclusive! INT)
    )
    (has_type (vstd!seq.Seq.subrange.? A&. A& self! start_inclusive! end_exclusive!) (
      TYPE%vstd!seq.Seq. A&. A&
   )))
   :pattern ((vstd!seq.Seq.subrange.? A&. A& self! start_inclusive! end_exclusive!))
   :qid internal_vstd!seq.Seq.subrange.?_pre_post_definition
)))

;; Function-Axioms vstd::seq::Seq::add
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (rhs! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type rhs! (TYPE%vstd!seq.Seq. A&. A&))
    )
    (has_type (vstd!seq.Seq.add.? A&. A& self! rhs!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.Seq.add.? A&. A& self! rhs!))
   :qid internal_vstd!seq.Seq.add.?_pre_post_definition
)))

;; Function-Axioms vstd::seq::impl&%0::spec_add
(assert
 (fuel_bool_default fuel%vstd!seq.impl&%0.spec_add.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq.impl&%0.spec_add.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (rhs! Poly)) (!
    (= (vstd!seq.impl&%0.spec_add.? A&. A& self! rhs!) (vstd!seq.Seq.add.? A&. A& self!
      rhs!
    ))
    :pattern ((vstd!seq.impl&%0.spec_add.? A&. A& self! rhs!))
    :qid internal_vstd!seq.impl&__0.spec_add.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (rhs! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type rhs! (TYPE%vstd!seq.Seq. A&. A&))
    )
    (has_type (vstd!seq.impl&%0.spec_add.? A&. A& self! rhs!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.impl&%0.spec_add.? A&. A& self! rhs!))
   :qid internal_vstd!seq.impl&__0.spec_add.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::vec::impl&%2::spec_index
(assert
 (fuel_bool_default fuel%vstd!std_specs.vec.impl&%2.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.vec.impl&%2.spec_index.)
  (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
    (= (vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? $ (TYPE%alloc!vec.Vec. T&.
       T& A&. A&
      ) T&. T& self! i!
     ) (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T&
        A&. A&
       ) self!
      ) i!
    ))
    :pattern ((vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? $ (TYPE%alloc!vec.Vec.
       T&. T& A&. A&
      ) T&. T& self! i!
    ))
    :qid internal_vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.?_definition
))))

;; Function-Specs vstd::seq::Seq::update
(declare-fun req%vstd!seq.Seq.update. (Dcr Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%4 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly) (a! Poly)) (!
   (= (req%vstd!seq.Seq.update. A&. A& self! i! a!) (=>
     %%global_location_label%%4
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.Seq.update. A&. A& self! i! a!))
   :qid internal_req__vstd!seq.Seq.update._definition
)))

;; Function-Axioms vstd::seq::Seq::update
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
     (has_type a! A&)
    )
    (has_type (vstd!seq.Seq.update.? A&. A& self! i! a!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.Seq.update.? A&. A& self! i! a!))
   :qid internal_vstd!seq.Seq.update.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::empty
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type)) (!
   (has_type (vstd!map.impl&%0.empty.? K&. K& V&. V&) (TYPE%vstd!map.Map. K&. K& V&. V&))
   :pattern ((vstd!map.impl&%0.empty.? K&. K& V&. V&))
   :qid internal_vstd!map.impl&__0.empty.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::dom
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
    (has_type (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) (TYPE%vstd!set.Set. K&. K&))
   )
   :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& self!))
   :qid internal_vstd!map.impl&__0.dom.?_pre_post_definition
)))

;; Function-Specs vstd::map::impl&%0::index
(declare-fun req%vstd!map.impl&%0.index. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%5 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (= (req%vstd!map.impl&%0.index. K&. K& V&. V& self! key!) (=>
     %%global_location_label%%5
     (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) key!)
   ))
   :pattern ((req%vstd!map.impl&%0.index. K&. K& V&. V& self! key!))
   :qid internal_req__vstd!map.impl&__0.index._definition
)))

;; Function-Axioms vstd::map::impl&%0::index
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (has_type (vstd!map.impl&%0.index.? K&. K& V&. V& self! key!) V&)
   )
   :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& self! key!))
   :qid internal_vstd!map.impl&__0.index.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::insert
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly) (value! Poly))
  (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
     (has_type value! V&)
    )
    (has_type (vstd!map.impl&%0.insert.? K&. K& V&. V& self! key! value!) (TYPE%vstd!map.Map.
      K&. K& V&. V&
   )))
   :pattern ((vstd!map.impl&%0.insert.? K&. K& V&. V& self! key! value!))
   :qid internal_vstd!map.impl&__0.insert.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::remove
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (has_type (vstd!map.impl&%0.remove.? K&. K& V&. V& self! key!) (TYPE%vstd!map.Map.
      K&. K& V&. V&
   )))
   :pattern ((vstd!map.impl&%0.remove.? K&. K& V&. V& self! key!))
   :qid internal_vstd!map.impl&__0.remove.?_pre_post_definition
)))

;; Function-Specs vstd::map::impl&%0::spec_index
(declare-fun req%vstd!map.impl&%0.spec_index. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%6 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (= (req%vstd!map.impl&%0.spec_index. K&. K& V&. V& self! key!) (=>
     %%global_location_label%%6
     (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) key!)
   ))
   :pattern ((req%vstd!map.impl&%0.spec_index. K&. K& V&. V& self! key!))
   :qid internal_req__vstd!map.impl&__0.spec_index._definition
)))

;; Function-Axioms vstd::map::impl&%0::spec_index
(assert
 (fuel_bool_default fuel%vstd!map.impl&%0.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map.impl&%0.spec_index.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
    (= (vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!) (vstd!map.impl&%0.index.?
      K&. K& V&. V& self! key!
    ))
    :pattern ((vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!))
    :qid internal_vstd!map.impl&__0.spec_index.?_definition
))))
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (has_type (vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!) V&)
   )
   :pattern ((vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!))
   :qid internal_vstd!map.impl&__0.spec_index.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::mk_map
(assert
 (forall ((A&. Dcr) (A& Type) (V&. Dcr) (V& Type) (F&. Dcr) (F& Type) (self! Poly) (
    f! Poly
   )
  ) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type f! F&)
    )
    (has_type (vstd!set.impl&%0.mk_map.? A&. A& V&. V& F&. F& self! f!) (TYPE%vstd!map.Map.
      A&. A& V&. V&
   )))
   :pattern ((vstd!set.impl&%0.mk_map.? A&. A& V&. V& F&. F& self! f!))
   :qid internal_vstd!set.impl&__0.mk_map.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::new
(assert
 (forall ((A&. Dcr) (A& Type) (F&. Dcr) (F& Type) (f! Poly)) (!
   (=>
    (has_type f! F&)
    (has_type (vstd!set.impl&%0.new.? A&. A& F&. F& f!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.impl&%0.new.? A&. A& F&. F& f!))
   :qid internal_vstd!set.impl&__0.new.?_pre_post_definition
)))

;; Function-Specs vstd::map::axiom_map_index_decreases_finite
(declare-fun req%vstd!map.axiom_map_index_decreases_finite. (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%7 Bool)
(declare-const %%global_location_label%%8 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
   (= (req%vstd!map.axiom_map_index_decreases_finite. K&. K& V&. V& m! key!) (and
     (=>
      %%global_location_label%%7
      (vstd!set.impl&%0.finite.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!))
     )
     (=>
      %%global_location_label%%8
      (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
   )))
   :pattern ((req%vstd!map.axiom_map_index_decreases_finite. K&. K& V&. V& m! key!))
   :qid internal_req__vstd!map.axiom_map_index_decreases_finite._definition
)))
(declare-fun ens%vstd!map.axiom_map_index_decreases_finite. (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
   (= (ens%vstd!map.axiom_map_index_decreases_finite. K&. K& V&. V& m! key!) (height_lt
     (height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)) (height m!)
   ))
   :pattern ((ens%vstd!map.axiom_map_index_decreases_finite. K&. K& V&. V& m! key!))
   :qid internal_ens__vstd!map.axiom_map_index_decreases_finite._definition
)))

;; Broadcast vstd::map::axiom_map_index_decreases_finite
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (=>
     (and
      (vstd!set.impl&%0.finite.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!))
      (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
     )
     (height_lt (height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)) (height m!))
   ))
   :pattern ((height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)))
   :qid user_vstd__map__axiom_map_index_decreases_finite_1
)))

;; Function-Specs vstd::map::axiom_map_index_decreases_infinite
(declare-fun req%vstd!map.axiom_map_index_decreases_infinite. (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%9 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
   (= (req%vstd!map.axiom_map_index_decreases_infinite. K&. K& V&. V& m! key!) (=>
     %%global_location_label%%9
     (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
   ))
   :pattern ((req%vstd!map.axiom_map_index_decreases_infinite. K&. K& V&. V& m! key!))
   :qid internal_req__vstd!map.axiom_map_index_decreases_infinite._definition
)))
(declare-fun ens%vstd!map.axiom_map_index_decreases_infinite. (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
   (= (ens%vstd!map.axiom_map_index_decreases_infinite. K&. K& V&. V& m! key!) (height_lt
     (height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)) (height (fun_from_recursive_field
       m!
   ))))
   :pattern ((ens%vstd!map.axiom_map_index_decreases_infinite. K&. K& V&. V& m! key!))
   :qid internal_ens__vstd!map.axiom_map_index_decreases_infinite._definition
)))

;; Broadcast vstd::map::axiom_map_index_decreases_infinite
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (=>
     (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
     (height_lt (height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)) (height (fun_from_recursive_field
        m!
   )))))
   :pattern ((height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)))
   :qid user_vstd__map__axiom_map_index_decreases_infinite_2
)))

;; Function-Axioms vstd::set::impl&%0::empty
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (has_type (vstd!set.impl&%0.empty.? A&. A&) (TYPE%vstd!set.Set. A&. A&))
   :pattern ((vstd!set.impl&%0.empty.? A&. A&))
   :qid internal_vstd!set.impl&__0.empty.?_pre_post_definition
)))

;; Function-Specs vstd::map::axiom_map_empty
(declare-fun ens%vstd!map.axiom_map_empty. (Dcr Type Dcr Type) Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type)) (!
   (= (ens%vstd!map.axiom_map_empty. K&. K& V&. V&) (= (vstd!map.impl&%0.dom.? K&. K& V&.
      V& (vstd!map.impl&%0.empty.? K&. K& V&. V&)
     ) (vstd!set.impl&%0.empty.? K&. K&)
   ))
   :pattern ((ens%vstd!map.axiom_map_empty. K&. K& V&. V&))
   :qid internal_ens__vstd!map.axiom_map_empty._definition
)))

;; Broadcast vstd::map::axiom_map_empty
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type)) (!
   (= (vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.empty.? K&. K& V&. V&))
    (vstd!set.impl&%0.empty.? K&. K&)
   )
   :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.empty.? K&. K& V&.
      V&
   )))
   :qid user_vstd__map__axiom_map_empty_3
)))

;; Function-Axioms vstd::set::impl&%0::insert
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!set.impl&%0.insert.? A&. A& self! a!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.impl&%0.insert.? A&. A& self! a!))
   :qid internal_vstd!set.impl&__0.insert.?_pre_post_definition
)))

;; Function-Specs vstd::map::axiom_map_insert_domain
(declare-fun ens%vstd!map.axiom_map_insert_domain. (Dcr Type Dcr Type Poly Poly Poly)
 Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly) (value! Poly))
  (!
   (= (ens%vstd!map.axiom_map_insert_domain. K&. K& V&. V& m! key! value!) (= (vstd!map.impl&%0.dom.?
      K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V& m! key! value!)
     ) (vstd!set.impl&%0.insert.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
   ))
   :pattern ((ens%vstd!map.axiom_map_insert_domain. K&. K& V&. V& m! key! value!))
   :qid internal_ens__vstd!map.axiom_map_insert_domain._definition
)))

;; Broadcast vstd::map::axiom_map_insert_domain
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly) (value! Poly))
  (!
   (=>
    (and
     (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
     (has_type value! V&)
    )
    (= (vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V& m!
       key! value!
      )
     ) (vstd!set.impl&%0.insert.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
   ))
   :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&.
      V& m! key! value!
   )))
   :qid user_vstd__map__axiom_map_insert_domain_4
)))

;; Function-Specs vstd::map::axiom_map_insert_same
(declare-fun ens%vstd!map.axiom_map_insert_same. (Dcr Type Dcr Type Poly Poly Poly)
 Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly) (value! Poly))
  (!
   (= (ens%vstd!map.axiom_map_insert_same. K&. K& V&. V& m! key! value!) (= (vstd!map.impl&%0.index.?
      K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V& m! key! value!) key!
     ) value!
   ))
   :pattern ((ens%vstd!map.axiom_map_insert_same. K&. K& V&. V& m! key! value!))
   :qid internal_ens__vstd!map.axiom_map_insert_same._definition
)))

;; Broadcast vstd::map::axiom_map_insert_same
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly) (value! Poly))
  (!
   (=>
    (and
     (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
     (has_type value! V&)
    )
    (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V&
       m! key! value!
      ) key!
     ) value!
   ))
   :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K&
      V&. V& m! key! value!
     ) key!
   ))
   :qid user_vstd__map__axiom_map_insert_same_5
)))

;; Function-Specs vstd::map::axiom_map_insert_different
(declare-fun req%vstd!map.axiom_map_insert_different. (Dcr Type Dcr Type Poly Poly
  Poly Poly
 ) Bool
)
(declare-const %%global_location_label%%10 Bool)
(declare-const %%global_location_label%%11 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly)
   (value! Poly)
  ) (!
   (= (req%vstd!map.axiom_map_insert_different. K&. K& V&. V& m! key1! key2! value!)
    (and
     (=>
      %%global_location_label%%10
      (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key1!)
     )
     (=>
      %%global_location_label%%11
      (not (= key1! key2!))
   )))
   :pattern ((req%vstd!map.axiom_map_insert_different. K&. K& V&. V& m! key1! key2! value!))
   :qid internal_req__vstd!map.axiom_map_insert_different._definition
)))
(declare-fun ens%vstd!map.axiom_map_insert_different. (Dcr Type Dcr Type Poly Poly
  Poly Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly)
   (value! Poly)
  ) (!
   (= (ens%vstd!map.axiom_map_insert_different. K&. K& V&. V& m! key1! key2! value!)
    (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V&
       m! key2! value!
      ) key1!
     ) (vstd!map.impl&%0.index.? K&. K& V&. V& m! key1!)
   ))
   :pattern ((ens%vstd!map.axiom_map_insert_different. K&. K& V&. V& m! key1! key2! value!))
   :qid internal_ens__vstd!map.axiom_map_insert_different._definition
)))

;; Broadcast vstd::map::axiom_map_insert_different
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly)
   (value! Poly)
  ) (!
   (=>
    (and
     (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key1! K&)
     (has_type key2! K&)
     (has_type value! V&)
    )
    (=>
     (and
      (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key1!)
      (not (= key1! key2!))
     )
     (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V&
        m! key2! value!
       ) key1!
      ) (vstd!map.impl&%0.index.? K&. K& V&. V& m! key1!)
   )))
   :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K&
      V&. V& m! key2! value!
     ) key1!
   ))
   :qid user_vstd__map__axiom_map_insert_different_6
)))

;; Function-Axioms vstd::set::impl&%0::remove
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!set.impl&%0.remove.? A&. A& self! a!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.impl&%0.remove.? A&. A& self! a!))
   :qid internal_vstd!set.impl&__0.remove.?_pre_post_definition
)))

;; Function-Specs vstd::map::axiom_map_remove_domain
(declare-fun ens%vstd!map.axiom_map_remove_domain. (Dcr Type Dcr Type Poly Poly) Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
   (= (ens%vstd!map.axiom_map_remove_domain. K&. K& V&. V& m! key!) (= (vstd!map.impl&%0.dom.?
      K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&. V& m! key!)
     ) (vstd!set.impl&%0.remove.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
   ))
   :pattern ((ens%vstd!map.axiom_map_remove_domain. K&. K& V&. V& m! key!))
   :qid internal_ens__vstd!map.axiom_map_remove_domain._definition
)))

;; Broadcast vstd::map::axiom_map_remove_domain
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (= (vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&. V& m!
       key!
      )
     ) (vstd!set.impl&%0.remove.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
   ))
   :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&.
      V& m! key!
   )))
   :qid user_vstd__map__axiom_map_remove_domain_7
)))

;; Function-Specs vstd::map::axiom_map_remove_different
(declare-fun req%vstd!map.axiom_map_remove_different. (Dcr Type Dcr Type Poly Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%12 Bool)
(declare-const %%global_location_label%%13 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly))
  (!
   (= (req%vstd!map.axiom_map_remove_different. K&. K& V&. V& m! key1! key2!) (and
     (=>
      %%global_location_label%%12
      (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key1!)
     )
     (=>
      %%global_location_label%%13
      (not (= key1! key2!))
   )))
   :pattern ((req%vstd!map.axiom_map_remove_different. K&. K& V&. V& m! key1! key2!))
   :qid internal_req__vstd!map.axiom_map_remove_different._definition
)))
(declare-fun ens%vstd!map.axiom_map_remove_different. (Dcr Type Dcr Type Poly Poly
  Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly))
  (!
   (= (ens%vstd!map.axiom_map_remove_different. K&. K& V&. V& m! key1! key2!) (= (vstd!map.impl&%0.index.?
      K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&. V& m! key2!) key1!
     ) (vstd!map.impl&%0.index.? K&. K& V&. V& m! key1!)
   ))
   :pattern ((ens%vstd!map.axiom_map_remove_different. K&. K& V&. V& m! key1! key2!))
   :qid internal_ens__vstd!map.axiom_map_remove_different._definition
)))

;; Broadcast vstd::map::axiom_map_remove_different
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly))
  (!
   (=>
    (and
     (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key1! K&)
     (has_type key2! K&)
    )
    (=>
     (and
      (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key1!)
      (not (= key1! key2!))
     )
     (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&. V&
        m! key2!
       ) key1!
      ) (vstd!map.impl&%0.index.? K&. K& V&. V& m! key1!)
   )))
   :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K&
      V&. V& m! key2!
     ) key1!
   ))
   :qid user_vstd__map__axiom_map_remove_different_8
)))

;; Function-Specs vstd::map::axiom_map_ext_equal
(declare-fun ens%vstd!map.axiom_map_ext_equal. (Dcr Type Dcr Type Poly Poly) Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m1! Poly) (m2! Poly)) (!
   (= (ens%vstd!map.axiom_map_ext_equal. K&. K& V&. V& m1! m2!) (= (ext_eq false (TYPE%vstd!map.Map.
       K&. K& V&. V&
      ) m1! m2!
     ) (and
      (ext_eq false (TYPE%vstd!set.Set. K&. K&) (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!)
       (vstd!map.impl&%0.dom.? K&. K& V&. V& m2!)
      )
      (forall ((k$ Poly)) (!
        (=>
         (has_type k$ K&)
         (=>
          (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!) k$)
          (= (vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$) (vstd!map.impl&%0.index.? K&. K&
            V&. V& m2! k$
        ))))
        :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$))
        :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m2! k$))
        :qid user_vstd__map__axiom_map_ext_equal_9
   )))))
   :pattern ((ens%vstd!map.axiom_map_ext_equal. K&. K& V&. V& m1! m2!))
   :qid internal_ens__vstd!map.axiom_map_ext_equal._definition
)))

;; Broadcast vstd::map::axiom_map_ext_equal
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m1! Poly) (m2! Poly)) (!
   (=>
    (and
     (has_type m1! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type m2! (TYPE%vstd!map.Map. K&. K& V&. V&))
    )
    (= (ext_eq false (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!) (and
      (ext_eq false (TYPE%vstd!set.Set. K&. K&) (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!)
       (vstd!map.impl&%0.dom.? K&. K& V&. V& m2!)
      )
      (forall ((k$ Poly)) (!
        (=>
         (has_type k$ K&)
         (=>
          (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!) k$)
          (= (vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$) (vstd!map.impl&%0.index.? K&. K&
            V&. V& m2! k$
        ))))
        :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$))
        :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m2! k$))
        :qid user_vstd__map__axiom_map_ext_equal_10
   )))))
   :pattern ((ext_eq false (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!))
   :qid user_vstd__map__axiom_map_ext_equal_11
)))

;; Function-Specs vstd::map::axiom_map_ext_equal_deep
(declare-fun ens%vstd!map.axiom_map_ext_equal_deep. (Dcr Type Dcr Type Poly Poly)
 Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m1! Poly) (m2! Poly)) (!
   (= (ens%vstd!map.axiom_map_ext_equal_deep. K&. K& V&. V& m1! m2!) (= (ext_eq true (TYPE%vstd!map.Map.
       K&. K& V&. V&
      ) m1! m2!
     ) (and
      (ext_eq true (TYPE%vstd!set.Set. K&. K&) (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!)
       (vstd!map.impl&%0.dom.? K&. K& V&. V& m2!)
      )
      (forall ((k$ Poly)) (!
        (=>
         (has_type k$ K&)
         (=>
          (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!) k$)
          (ext_eq true V& (vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$) (vstd!map.impl&%0.index.?
            K&. K& V&. V& m2! k$
        ))))
        :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$))
        :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m2! k$))
        :qid user_vstd__map__axiom_map_ext_equal_deep_12
   )))))
   :pattern ((ens%vstd!map.axiom_map_ext_equal_deep. K&. K& V&. V& m1! m2!))
   :qid internal_ens__vstd!map.axiom_map_ext_equal_deep._definition
)))

;; Broadcast vstd::map::axiom_map_ext_equal_deep
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m1! Poly) (m2! Poly)) (!
   (=>
    (and
     (has_type m1! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type m2! (TYPE%vstd!map.Map. K&. K& V&. V&))
    )
    (= (ext_eq true (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!) (and
      (ext_eq true (TYPE%vstd!set.Set. K&. K&) (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!)
       (vstd!map.impl&%0.dom.? K&. K& V&. V& m2!)
      )
      (forall ((k$ Poly)) (!
        (=>
         (has_type k$ K&)
         (=>
          (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!) k$)
          (ext_eq true V& (vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$) (vstd!map.impl&%0.index.?
            K&. K& V&. V& m2! k$
        ))))
        :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$))
        :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m2! k$))
        :qid user_vstd__map__axiom_map_ext_equal_deep_13
   )))))
   :pattern ((ext_eq true (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!))
   :qid user_vstd__map__axiom_map_ext_equal_deep_14
)))

;; Function-Axioms vstd::seq::Seq::new
(assert
 (forall ((A&. Dcr) (A& Type) (impl%1&. Dcr) (impl%1& Type) (len! Poly) (f! Poly))
  (!
   (=>
    (and
     (has_type len! NAT)
     (has_type f! impl%1&)
    )
    (has_type (vstd!seq.Seq.new.? A&. A& impl%1&. impl%1& len! f!) (TYPE%vstd!seq.Seq.
      A&. A&
   )))
   :pattern ((vstd!seq.Seq.new.? A&. A& impl%1&. impl%1& len! f!))
   :qid internal_vstd!seq.Seq.new.?_pre_post_definition
)))

;; Function-Specs vstd::seq::axiom_seq_index_decreases
(declare-fun req%vstd!seq.axiom_seq_index_decreases. (Dcr Type Poly Int) Bool)
(declare-const %%global_location_label%%14 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_index_decreases. A&. A& s! i!) (=>
     %%global_location_label%%14
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_index_decreases. A&. A& s! i!))
   :qid internal_req__vstd!seq.axiom_seq_index_decreases._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_index_decreases. (Dcr Type Poly Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_index_decreases. A&. A& s! i!) (height_lt (height (vstd!seq.Seq.index.?
       A&. A& s! (I i!)
      )
     ) (height s!)
   ))
   :pattern ((ens%vstd!seq.axiom_seq_index_decreases. A&. A& s! i!))
   :qid internal_ens__vstd!seq.axiom_seq_index_decreases._definition
)))

;; Broadcast vstd::seq::axiom_seq_index_decreases
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (=>
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
     )
     (height_lt (height (vstd!seq.Seq.index.? A&. A& s! i!)) (height s!))
   ))
   :pattern ((height (vstd!seq.Seq.index.? A&. A& s! i!)))
   :qid user_vstd__seq__axiom_seq_index_decreases_15
)))

;; Function-Specs vstd::seq::axiom_seq_empty
(declare-fun ens%vstd!seq.axiom_seq_empty. (Dcr Type) Bool)
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (ens%vstd!seq.axiom_seq_empty. A&. A&) (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.empty.?
       A&. A&
      )
     ) 0
   ))
   :pattern ((ens%vstd!seq.axiom_seq_empty. A&. A&))
   :qid internal_ens__vstd!seq.axiom_seq_empty._definition
)))

;; Broadcast vstd::seq::axiom_seq_empty
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.empty.? A&. A&)) 0)
   :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.empty.? A&. A&)))
   :qid user_vstd__seq__axiom_seq_empty_16
)))

;; Function-Specs vstd::seq::axiom_seq_new_len
(declare-fun ens%vstd!seq.axiom_seq_new_len. (Dcr Type Int %%Function%%) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (len! Int) (f! %%Function%%)) (!
   (= (ens%vstd!seq.axiom_seq_new_len. A&. A& len! f!) (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.new.?
       A&. A& $ (TYPE%fun%1. $ INT A&. A&) (I len!) (Poly%fun%1. f!)
      )
     ) len!
   ))
   :pattern ((ens%vstd!seq.axiom_seq_new_len. A&. A& len! f!))
   :qid internal_ens__vstd!seq.axiom_seq_new_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_new_len
(assert
 (forall ((A&. Dcr) (A& Type) (len! Poly) (f! Poly)) (!
   (=>
    (and
     (has_type len! NAT)
     (has_type f! (TYPE%fun%1. $ INT A&. A&))
    )
    (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT A&. A&)
       len! f!
      )
     ) (%I len!)
   ))
   :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT
       A&. A&
      ) len! f!
   )))
   :qid user_vstd__seq__axiom_seq_new_len_17
)))

;; Function-Specs vstd::seq::axiom_seq_new_index
(declare-fun req%vstd!seq.axiom_seq_new_index. (Dcr Type Int %%Function%% Int) Bool)
(declare-const %%global_location_label%%15 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (len! Int) (f! %%Function%%) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_new_index. A&. A& len! f! i!) (=>
     %%global_location_label%%15
     (and
      (<= 0 i!)
      (< i! len!)
   )))
   :pattern ((req%vstd!seq.axiom_seq_new_index. A&. A& len! f! i!))
   :qid internal_req__vstd!seq.axiom_seq_new_index._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_new_index. (Dcr Type Int %%Function%% Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (len! Int) (f! %%Function%%) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_new_index. A&. A& len! f! i!) (= (vstd!seq.Seq.index.? A&.
      A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT A&. A&) (I len!) (Poly%fun%1. f!))
      (I i!)
     ) (%%apply%%0 f! (I i!))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_new_index. A&. A& len! f! i!))
   :qid internal_ens__vstd!seq.axiom_seq_new_index._definition
)))

;; Broadcast vstd::seq::axiom_seq_new_index
(assert
 (forall ((A&. Dcr) (A& Type) (len! Poly) (f! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type len! NAT)
     (has_type f! (TYPE%fun%1. $ INT A&. A&))
     (has_type i! INT)
    )
    (=>
     (and
      (<= 0 (%I i!))
      (< (%I i!) (%I len!))
     )
     (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT A&. A&)
        len! f!
       ) i!
      ) (%%apply%%0 (%Poly%fun%1. f!) i!)
   )))
   :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT
       A&. A&
      ) len! f!
     ) i!
   ))
   :qid user_vstd__seq__axiom_seq_new_index_18
)))

;; Function-Specs vstd::seq::axiom_seq_push_len
(declare-fun ens%vstd!seq.axiom_seq_push_len. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_push_len. A&. A& s! a!) (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.push.?
       A&. A& s! a!
      )
     ) (nClip (Add (vstd!seq.Seq.len.? A&. A& s!) 1))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_push_len. A&. A& s! a!))
   :qid internal_ens__vstd!seq.axiom_seq_push_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_push_len
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type a! A&)
    )
    (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!)) (nClip (Add (vstd!seq.Seq.len.?
        A&. A& s!
       ) 1
   ))))
   :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!)))
   :qid user_vstd__seq__axiom_seq_push_len_19
)))

;; Function-Specs vstd::seq::axiom_seq_push_index_same
(declare-fun req%vstd!seq.axiom_seq_push_index_same. (Dcr Type Poly Poly Int) Bool)
(declare-const %%global_location_label%%16 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_push_index_same. A&. A& s! a! i!) (=>
     %%global_location_label%%16
     (= i! (vstd!seq.Seq.len.? A&. A& s!))
   ))
   :pattern ((req%vstd!seq.axiom_seq_push_index_same. A&. A& s! a! i!))
   :qid internal_req__vstd!seq.axiom_seq_push_index_same._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_push_index_same. (Dcr Type Poly Poly Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_push_index_same. A&. A& s! a! i!) (= (vstd!seq.Seq.index.?
      A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) (I i!)
     ) a!
   ))
   :pattern ((ens%vstd!seq.axiom_seq_push_index_same. A&. A& s! a! i!))
   :qid internal_ens__vstd!seq.axiom_seq_push_index_same._definition
)))

;; Broadcast vstd::seq::axiom_seq_push_index_same
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type a! A&)
     (has_type i! INT)
    )
    (=>
     (= (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
     (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!) a!)
   ))
   :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!))
   :qid user_vstd__seq__axiom_seq_push_index_same_20
)))

;; Function-Specs vstd::seq::axiom_seq_push_index_different
(declare-fun req%vstd!seq.axiom_seq_push_index_different. (Dcr Type Poly Poly Int)
 Bool
)
(declare-const %%global_location_label%%17 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_push_index_different. A&. A& s! a! i!) (=>
     %%global_location_label%%17
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_push_index_different. A&. A& s! a! i!))
   :qid internal_req__vstd!seq.axiom_seq_push_index_different._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_push_index_different. (Dcr Type Poly Poly Int)
 Bool
)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_push_index_different. A&. A& s! a! i!) (= (vstd!seq.Seq.index.?
      A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) (I i!)
     ) (vstd!seq.Seq.index.? A&. A& s! (I i!))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_push_index_different. A&. A& s! a! i!))
   :qid internal_ens__vstd!seq.axiom_seq_push_index_different._definition
)))

;; Broadcast vstd::seq::axiom_seq_push_index_different
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type a! A&)
     (has_type i! INT)
    )
    (=>
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
     )
     (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!) (vstd!seq.Seq.index.?
       A&. A& s! i!
   ))))
   :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!))
   :qid user_vstd__seq__axiom_seq_push_index_different_21
)))

;; Function-Specs vstd::seq::axiom_seq_update_len
(declare-fun req%vstd!seq.axiom_seq_update_len. (Dcr Type Poly Int Poly) Bool)
(declare-const %%global_location_label%%18 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int) (a! Poly)) (!
   (= (req%vstd!seq.axiom_seq_update_len. A&. A& s! i! a!) (=>
     %%global_location_label%%18
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_update_len. A&. A& s! i! a!))
   :qid internal_req__vstd!seq.axiom_seq_update_len._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_update_len. (Dcr Type Poly Int Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int) (a! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_update_len. A&. A& s! i! a!) (= (vstd!seq.Seq.len.? A&. A&
      (vstd!seq.Seq.update.? A&. A& s! (I i!) a!)
     ) (vstd!seq.Seq.len.? A&. A& s!)
   ))
   :pattern ((ens%vstd!seq.axiom_seq_update_len. A&. A& s! i! a!))
   :qid internal_ens__vstd!seq.axiom_seq_update_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_update_len
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
     (has_type a! A&)
    )
    (=>
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
     )
     (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i! a!)) (vstd!seq.Seq.len.?
       A&. A& s!
   ))))
   :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i! a!)))
   :qid user_vstd__seq__axiom_seq_update_len_22
)))

;; Function-Specs vstd::seq::axiom_seq_update_same
(declare-fun req%vstd!seq.axiom_seq_update_same. (Dcr Type Poly Int Poly) Bool)
(declare-const %%global_location_label%%19 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int) (a! Poly)) (!
   (= (req%vstd!seq.axiom_seq_update_same. A&. A& s! i! a!) (=>
     %%global_location_label%%19
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_update_same. A&. A& s! i! a!))
   :qid internal_req__vstd!seq.axiom_seq_update_same._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_update_same. (Dcr Type Poly Int Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int) (a! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_update_same. A&. A& s! i! a!) (= (vstd!seq.Seq.index.? A&.
      A& (vstd!seq.Seq.update.? A&. A& s! (I i!) a!) (I i!)
     ) a!
   ))
   :pattern ((ens%vstd!seq.axiom_seq_update_same. A&. A& s! i! a!))
   :qid internal_ens__vstd!seq.axiom_seq_update_same._definition
)))

;; Broadcast vstd::seq::axiom_seq_update_same
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
     (has_type a! A&)
    )
    (=>
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
     )
     (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i! a!) i!) a!)
   ))
   :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i! a!) i!))
   :qid user_vstd__seq__axiom_seq_update_same_23
)))

;; Function-Specs vstd::seq::axiom_seq_update_different
(declare-fun req%vstd!seq.axiom_seq_update_different. (Dcr Type Poly Int Int Poly)
 Bool
)
(declare-const %%global_location_label%%20 Bool)
(declare-const %%global_location_label%%21 Bool)
(declare-const %%global_location_label%%22 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i1! Int) (i2! Int) (a! Poly)) (!
   (= (req%vstd!seq.axiom_seq_update_different. A&. A& s! i1! i2! a!) (and
     (=>
      %%global_location_label%%20
      (and
       (<= 0 i1!)
       (< i1! (vstd!seq.Seq.len.? A&. A& s!))
     ))
     (=>
      %%global_location_label%%21
      (and
       (<= 0 i2!)
       (< i2! (vstd!seq.Seq.len.? A&. A& s!))
     ))
     (=>
      %%global_location_label%%22
      (not (= i1! i2!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_update_different. A&. A& s! i1! i2! a!))
   :qid internal_req__vstd!seq.axiom_seq_update_different._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_update_different. (Dcr Type Poly Int Int Poly)
 Bool
)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i1! Int) (i2! Int) (a! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_update_different. A&. A& s! i1! i2! a!) (= (vstd!seq.Seq.index.?
      A&. A& (vstd!seq.Seq.update.? A&. A& s! (I i2!) a!) (I i1!)
     ) (vstd!seq.Seq.index.? A&. A& s! (I i1!))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_update_different. A&. A& s! i1! i2! a!))
   :qid internal_ens__vstd!seq.axiom_seq_update_different._definition
)))

;; Broadcast vstd::seq::axiom_seq_update_different
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i1! Poly) (i2! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i1! INT)
     (has_type i2! INT)
     (has_type a! A&)
    )
    (=>
     (and
      (and
       (and
        (<= 0 (%I i1!))
        (< (%I i1!) (vstd!seq.Seq.len.? A&. A& s!))
       )
       (and
        (<= 0 (%I i2!))
        (< (%I i2!) (vstd!seq.Seq.len.? A&. A& s!))
      ))
      (not (= i1! i2!))
     )
     (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i2! a!) i1!) (vstd!seq.Seq.index.?
       A&. A& s! i1!
   ))))
   :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i2! a!) i1!))
   :qid user_vstd__seq__axiom_seq_update_different_24
)))

;; Function-Specs vstd::seq::axiom_seq_ext_equal
(declare-fun ens%vstd!seq.axiom_seq_ext_equal. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_ext_equal. A&. A& s1! s2!) (= (ext_eq false (TYPE%vstd!seq.Seq.
       A&. A&
      ) s1! s2!
     ) (and
      (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
          )
          (= (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2! i$))
        ))
        :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
        :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
        :qid user_vstd__seq__axiom_seq_ext_equal_25
   )))))
   :pattern ((ens%vstd!seq.axiom_seq_ext_equal. A&. A& s1! s2!))
   :qid internal_ens__vstd!seq.axiom_seq_ext_equal._definition
)))

;; Broadcast vstd::seq::axiom_seq_ext_equal
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
    )
    (= (ext_eq false (TYPE%vstd!seq.Seq. A&. A&) s1! s2!) (and
      (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
          )
          (= (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2! i$))
        ))
        :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
        :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
        :qid user_vstd__seq__axiom_seq_ext_equal_26
   )))))
   :pattern ((ext_eq false (TYPE%vstd!seq.Seq. A&. A&) s1! s2!))
   :qid user_vstd__seq__axiom_seq_ext_equal_27
)))

;; Function-Specs vstd::seq::axiom_seq_ext_equal_deep
(declare-fun ens%vstd!seq.axiom_seq_ext_equal_deep. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_ext_equal_deep. A&. A& s1! s2!) (= (ext_eq true (TYPE%vstd!seq.Seq.
       A&. A&
      ) s1! s2!
     ) (and
      (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
          )
          (ext_eq true A& (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2!
            i$
        ))))
        :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
        :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
        :qid user_vstd__seq__axiom_seq_ext_equal_deep_28
   )))))
   :pattern ((ens%vstd!seq.axiom_seq_ext_equal_deep. A&. A& s1! s2!))
   :qid internal_ens__vstd!seq.axiom_seq_ext_equal_deep._definition
)))

;; Broadcast vstd::seq::axiom_seq_ext_equal_deep
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
    )
    (= (ext_eq true (TYPE%vstd!seq.Seq. A&. A&) s1! s2!) (and
      (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
          )
          (ext_eq true A& (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2!
            i$
        ))))
        :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
        :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
        :qid user_vstd__seq__axiom_seq_ext_equal_deep_29
   )))))
   :pattern ((ext_eq true (TYPE%vstd!seq.Seq. A&. A&) s1! s2!))
   :qid user_vstd__seq__axiom_seq_ext_equal_deep_30
)))

;; Function-Specs vstd::seq::axiom_seq_subrange_len
(declare-fun req%vstd!seq.axiom_seq_subrange_len. (Dcr Type Poly Int Int) Bool)
(declare-const %%global_location_label%%23 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Int) (k! Int)) (!
   (= (req%vstd!seq.axiom_seq_subrange_len. A&. A& s! j! k!) (=>
     %%global_location_label%%23
     (and
      (and
       (<= 0 j!)
       (<= j! k!)
      )
      (<= k! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_subrange_len. A&. A& s! j! k!))
   :qid internal_req__vstd!seq.axiom_seq_subrange_len._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_subrange_len. (Dcr Type Poly Int Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Int) (k! Int)) (!
   (= (ens%vstd!seq.axiom_seq_subrange_len. A&. A& s! j! k!) (= (vstd!seq.Seq.len.? A&.
      A& (vstd!seq.Seq.subrange.? A&. A& s! (I j!) (I k!))
     ) (Sub k! j!)
   ))
   :pattern ((ens%vstd!seq.axiom_seq_subrange_len. A&. A& s! j! k!))
   :qid internal_ens__vstd!seq.axiom_seq_subrange_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_subrange_len
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Poly) (k! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type j! INT)
     (has_type k! INT)
    )
    (=>
     (and
      (and
       (<= 0 (%I j!))
       (<= (%I j!) (%I k!))
      )
      (<= (%I k!) (vstd!seq.Seq.len.? A&. A& s!))
     )
     (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!)) (Sub (%I k!)
       (%I j!)
   ))))
   :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!)))
   :qid user_vstd__seq__axiom_seq_subrange_len_31
)))

;; Function-Specs vstd::seq::axiom_seq_subrange_index
(declare-fun req%vstd!seq.axiom_seq_subrange_index. (Dcr Type Poly Int Int Int) Bool)
(declare-const %%global_location_label%%24 Bool)
(declare-const %%global_location_label%%25 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Int) (k! Int) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_subrange_index. A&. A& s! j! k! i!) (and
     (=>
      %%global_location_label%%24
      (and
       (and
        (<= 0 j!)
        (<= j! k!)
       )
       (<= k! (vstd!seq.Seq.len.? A&. A& s!))
     ))
     (=>
      %%global_location_label%%25
      (and
       (<= 0 i!)
       (< i! (Sub k! j!))
   ))))
   :pattern ((req%vstd!seq.axiom_seq_subrange_index. A&. A& s! j! k! i!))
   :qid internal_req__vstd!seq.axiom_seq_subrange_index._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_subrange_index. (Dcr Type Poly Int Int Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Int) (k! Int) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_subrange_index. A&. A& s! j! k! i!) (= (vstd!seq.Seq.index.?
      A&. A& (vstd!seq.Seq.subrange.? A&. A& s! (I j!) (I k!)) (I i!)
     ) (vstd!seq.Seq.index.? A&. A& s! (I (Add i! j!)))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_subrange_index. A&. A& s! j! k! i!))
   :qid internal_ens__vstd!seq.axiom_seq_subrange_index._definition
)))

;; Broadcast vstd::seq::axiom_seq_subrange_index
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Poly) (k! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type j! INT)
     (has_type k! INT)
     (has_type i! INT)
    )
    (=>
     (and
      (and
       (and
        (<= 0 (%I j!))
        (<= (%I j!) (%I k!))
       )
       (<= (%I k!) (vstd!seq.Seq.len.? A&. A& s!))
      )
      (and
       (<= 0 (%I i!))
       (< (%I i!) (Sub (%I k!) (%I j!)))
     ))
     (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!) i!) (vstd!seq.Seq.index.?
       A&. A& s! (I (Add (%I i!) (%I j!)))
   ))))
   :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!) i!))
   :qid user_vstd__seq__axiom_seq_subrange_index_32
)))

;; Function-Specs vstd::seq::axiom_seq_add_len
(declare-fun ens%vstd!seq.axiom_seq_add_len. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_add_len. A&. A& s1! s2!) (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.add.?
       A&. A& s1! s2!
      )
     ) (nClip (Add (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!)))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_add_len. A&. A& s1! s2!))
   :qid internal_ens__vstd!seq.axiom_seq_add_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_add_len
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
    )
    (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!)) (nClip (Add (vstd!seq.Seq.len.?
        A&. A& s1!
       ) (vstd!seq.Seq.len.? A&. A& s2!)
   ))))
   :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!)))
   :qid user_vstd__seq__axiom_seq_add_len_33
)))

;; Function-Specs vstd::seq::axiom_seq_add_index1
(declare-fun req%vstd!seq.axiom_seq_add_index1. (Dcr Type Poly Poly Int) Bool)
(declare-const %%global_location_label%%26 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_add_index1. A&. A& s1! s2! i!) (=>
     %%global_location_label%%26
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s1!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_add_index1. A&. A& s1! s2! i!))
   :qid internal_req__vstd!seq.axiom_seq_add_index1._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_add_index1. (Dcr Type Poly Poly Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_add_index1. A&. A& s1! s2! i!) (= (vstd!seq.Seq.index.? A&.
      A& (vstd!seq.Seq.add.? A&. A& s1! s2!) (I i!)
     ) (vstd!seq.Seq.index.? A&. A& s1! (I i!))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_add_index1. A&. A& s1! s2! i!))
   :qid internal_ens__vstd!seq.axiom_seq_add_index1._definition
)))

;; Broadcast vstd::seq::axiom_seq_add_index1
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (=>
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& s1!))
     )
     (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!) (vstd!seq.Seq.index.?
       A&. A& s1! i!
   ))))
   :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!))
   :qid user_vstd__seq__axiom_seq_add_index1_34
)))

;; Function-Specs vstd::seq::axiom_seq_add_index2
(declare-fun req%vstd!seq.axiom_seq_add_index2. (Dcr Type Poly Poly Int) Bool)
(declare-const %%global_location_label%%27 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_add_index2. A&. A& s1! s2! i!) (=>
     %%global_location_label%%27
     (and
      (<= (vstd!seq.Seq.len.? A&. A& s1!) i!)
      (< i! (nClip (Add (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))))
   )))
   :pattern ((req%vstd!seq.axiom_seq_add_index2. A&. A& s1! s2! i!))
   :qid internal_req__vstd!seq.axiom_seq_add_index2._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_add_index2. (Dcr Type Poly Poly Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_add_index2. A&. A& s1! s2! i!) (= (vstd!seq.Seq.index.? A&.
      A& (vstd!seq.Seq.add.? A&. A& s1! s2!) (I i!)
     ) (vstd!seq.Seq.index.? A&. A& s2! (I (Sub i! (vstd!seq.Seq.len.? A&. A& s1!))))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_add_index2. A&. A& s1! s2! i!))
   :qid internal_ens__vstd!seq.axiom_seq_add_index2._definition
)))

;; Broadcast vstd::seq::axiom_seq_add_index2
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (=>
     (and
      (<= (vstd!seq.Seq.len.? A&. A& s1!) (%I i!))
      (< (%I i!) (nClip (Add (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))))
     )
     (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!) (vstd!seq.Seq.index.?
       A&. A& s2! (I (Sub (%I i!) (vstd!seq.Seq.len.? A&. A& s1!)))
   ))))
   :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!))
   :qid user_vstd__seq__axiom_seq_add_index2_35
)))

;; Function-Specs vstd::seq_lib::impl&%0::drop_last
(declare-fun req%vstd!seq_lib.impl&%0.drop_last. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%28 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (= (req%vstd!seq_lib.impl&%0.drop_last. A&. A& self!) (=>
     %%global_location_label%%28
     (>= (vstd!seq.Seq.len.? A&. A& self!) 1)
   ))
   :pattern ((req%vstd!seq_lib.impl&%0.drop_last. A&. A& self!))
   :qid internal_req__vstd!seq_lib.impl&__0.drop_last._definition
)))

;; Function-Axioms vstd::seq_lib::impl&%0::drop_last
(assert
 (fuel_bool_default fuel%vstd!seq_lib.impl&%0.drop_last.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.drop_last.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!seq_lib.impl&%0.drop_last.? A&. A& self!) (vstd!seq.Seq.subrange.? A&. A&
      self! (I 0) (I (Sub (vstd!seq.Seq.len.? A&. A& self!) 1))
    ))
    :pattern ((vstd!seq_lib.impl&%0.drop_last.? A&. A& self!))
    :qid internal_vstd!seq_lib.impl&__0.drop_last.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
    (has_type (vstd!seq_lib.impl&%0.drop_last.? A&. A& self!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq_lib.impl&%0.drop_last.? A&. A& self!))
   :qid internal_vstd!seq_lib.impl&__0.drop_last.?_pre_post_definition
)))

;; Function-Specs vstd::seq::Seq::last
(declare-fun req%vstd!seq.Seq.last. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%29 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (= (req%vstd!seq.Seq.last. A&. A& self!) (=>
     %%global_location_label%%29
     (< 0 (vstd!seq.Seq.len.? A&. A& self!))
   ))
   :pattern ((req%vstd!seq.Seq.last. A&. A& self!))
   :qid internal_req__vstd!seq.Seq.last._definition
)))

;; Function-Axioms vstd::seq::Seq::last
(assert
 (fuel_bool_default fuel%vstd!seq.Seq.last.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq.Seq.last.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!seq.Seq.last.? A&. A& self!) (vstd!seq.Seq.index.? A&. A& self! (I (Sub (vstd!seq.Seq.len.?
         A&. A& self!
        ) 1
    ))))
    :pattern ((vstd!seq.Seq.last.? A&. A& self!))
    :qid internal_vstd!seq.Seq.last.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
    (has_type (vstd!seq.Seq.last.? A&. A& self!) A&)
   )
   :pattern ((vstd!seq.Seq.last.? A&. A& self!))
   :qid internal_vstd!seq.Seq.last.?_pre_post_definition
)))

;; Function-Axioms vstd::seq_lib::impl&%0::filter
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (pred! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type pred! (TYPE%fun%1. A&. A& $ BOOL))
    )
    (has_type (vstd!seq_lib.impl&%0.filter.? A&. A& self! pred!) (TYPE%vstd!seq.Seq. A&.
      A&
   )))
   :pattern ((vstd!seq_lib.impl&%0.filter.? A&. A& self! pred!))
   :qid internal_vstd!seq_lib.impl&__0.filter.?_pre_post_definition
)))

;; Function-Axioms vstd::seq_lib::impl&%0::contains
(assert
 (fuel_bool_default fuel%vstd!seq_lib.impl&%0.contains.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.contains.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (needle! Poly)) (!
    (= (vstd!seq_lib.impl&%0.contains.? A&. A& self! needle!) (exists ((i$ Poly)) (!
       (and
        (has_type i$ INT)
        (and
         (and
          (<= 0 (%I i$))
          (< (%I i$) (vstd!seq.Seq.len.? A&. A& self!))
         )
         (= (vstd!seq.Seq.index.? A&. A& self! i$) needle!)
       ))
       :pattern ((vstd!seq.Seq.index.? A&. A& self! i$))
       :qid user_vstd__seq_lib__impl&%0__contains_36
    )))
    :pattern ((vstd!seq_lib.impl&%0.contains.? A&. A& self! needle!))
    :qid internal_vstd!seq_lib.impl&__0.contains.?_definition
))))

;; Function-Specs vstd::seq_lib::impl&%0::filter_lemma_broadcast
(declare-fun ens%vstd!seq_lib.impl&%0.filter_lemma_broadcast. (Dcr Type Poly %%Function%%)
 Bool
)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (pred! %%Function%%)) (!
   (= (ens%vstd!seq_lib.impl&%0.filter_lemma_broadcast. A&. A& self! pred!) (and
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ INT)
        (=>
         (and
          (<= 0 (%I i$))
          (< (%I i$) (vstd!seq.Seq.len.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& self! (Poly%fun%1.
              pred!
         )))))
         (and
          (%B (%%apply%%0 pred! (vstd!seq.Seq.index.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&.
              A& self! (Poly%fun%1. pred!)
             ) i$
          )))
          (vstd!seq_lib.impl&%0.contains.? A&. A& self! (vstd!seq.Seq.index.? A&. A& (vstd!seq_lib.impl&%0.filter.?
             A&. A& self! (Poly%fun%1. pred!)
            ) i$
       )))))
       :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& self! (
           Poly%fun%1. pred!
          )
         ) i$
       ))
       :qid user_vstd__seq_lib__impl&%0__filter_lemma_broadcast_37
     ))
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ INT)
        (=>
         (and
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? A&. A& self!))
          )
          (%B (%%apply%%0 pred! (vstd!seq.Seq.index.? A&. A& self! i$)))
         )
         (vstd!seq_lib.impl&%0.contains.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& self!
           (Poly%fun%1. pred!)
          ) (vstd!seq.Seq.index.? A&. A& self! i$)
       )))
       :pattern ((vstd!seq_lib.impl&%0.contains.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&.
          A& self! (Poly%fun%1. pred!)
         ) (vstd!seq.Seq.index.? A&. A& self! i$)
       ))
       :qid user_vstd__seq_lib__impl&%0__filter_lemma_broadcast_38
     ))
     (<= (vstd!seq.Seq.len.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& self! (Poly%fun%1.
         pred!
       ))
      ) (vstd!seq.Seq.len.? A&. A& self!)
   )))
   :pattern ((ens%vstd!seq_lib.impl&%0.filter_lemma_broadcast. A&. A& self! pred!))
   :qid internal_ens__vstd!seq_lib.impl&__0.filter_lemma_broadcast._definition
)))

;; Broadcast vstd::seq_lib::impl&%0::filter_lemma_broadcast
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (pred! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type pred! (TYPE%fun%1. A&. A& $ BOOL))
    )
    (and
     (and
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& self! pred!)))
          )
          (and
           (%B (%%apply%%0 (%Poly%fun%1. pred!) (vstd!seq.Seq.index.? A&. A& (vstd!seq_lib.impl&%0.filter.?
               A&. A& self! pred!
              ) i$
           )))
           (vstd!seq_lib.impl&%0.contains.? A&. A& self! (vstd!seq.Seq.index.? A&. A& (vstd!seq_lib.impl&%0.filter.?
              A&. A& self! pred!
             ) i$
        )))))
        :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& self! pred!)
          i$
        ))
        :qid user_vstd__seq_lib__impl&%0__filter_lemma_broadcast_39
      ))
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (and
            (<= 0 (%I i$))
            (< (%I i$) (vstd!seq.Seq.len.? A&. A& self!))
           )
           (%B (%%apply%%0 (%Poly%fun%1. pred!) (vstd!seq.Seq.index.? A&. A& self! i$)))
          )
          (vstd!seq_lib.impl&%0.contains.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& self!
            pred!
           ) (vstd!seq.Seq.index.? A&. A& self! i$)
        )))
        :pattern ((vstd!seq_lib.impl&%0.contains.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&.
           A& self! pred!
          ) (vstd!seq.Seq.index.? A&. A& self! i$)
        ))
        :qid user_vstd__seq_lib__impl&%0__filter_lemma_broadcast_40
     )))
     (<= (vstd!seq.Seq.len.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& self! pred!))
      (vstd!seq.Seq.len.? A&. A& self!)
   )))
   :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& self! pred!)))
   :qid user_vstd__seq_lib__impl&%0__filter_lemma_broadcast_41
)))

;; Function-Specs vstd::seq_lib::impl&%0::filter_distributes_over_add_broacast
(declare-fun ens%vstd!seq_lib.impl&%0.filter_distributes_over_add_broacast. (Dcr Type
  Poly Poly %%Function%%
 ) Bool
)
(assert
 (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly) (pred! %%Function%%)) (!
   (= (ens%vstd!seq_lib.impl&%0.filter_distributes_over_add_broacast. A&. A& a! b! pred!)
    (= (vstd!seq_lib.impl&%0.filter.? A&. A& (vstd!seq.Seq.add.? A&. A& a! b!) (Poly%fun%1.
       pred!
      )
     ) (vstd!seq.Seq.add.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& a! (Poly%fun%1. pred!))
      (vstd!seq_lib.impl&%0.filter.? A&. A& b! (Poly%fun%1. pred!))
   )))
   :pattern ((ens%vstd!seq_lib.impl&%0.filter_distributes_over_add_broacast. A&. A& a!
     b! pred!
   ))
   :qid internal_ens__vstd!seq_lib.impl&__0.filter_distributes_over_add_broacast._definition
)))

;; Broadcast vstd::seq_lib::impl&%0::filter_distributes_over_add_broacast
(assert
 (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly) (pred! Poly)) (!
   (=>
    (and
     (has_type a! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type b! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type pred! (TYPE%fun%1. A&. A& $ BOOL))
    )
    (= (vstd!seq_lib.impl&%0.filter.? A&. A& (vstd!seq.Seq.add.? A&. A& a! b!) pred!)
     (vstd!seq.Seq.add.? A&. A& (vstd!seq_lib.impl&%0.filter.? A&. A& a! pred!) (vstd!seq_lib.impl&%0.filter.?
       A&. A& b! pred!
   ))))
   :pattern ((vstd!seq_lib.impl&%0.filter.? A&. A& (vstd!seq.Seq.add.? A&. A& a! b!) pred!))
   :qid user_vstd__seq_lib__impl&%0__filter_distributes_over_add_broacast_42
)))

;; Function-Axioms vstd::seq_lib::impl&%0::to_set
(assert
 (fuel_bool_default fuel%vstd!seq_lib.impl&%0.to_set.)
)
(declare-fun %%lambda%%0 (Dcr Type Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (a$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%0 %%hole%%0 %%hole%%1 %%hole%%2) a$) (B (vstd!seq_lib.impl&%0.contains.?
      %%hole%%0 %%hole%%1 %%hole%%2 a$
   )))
   :pattern ((%%apply%%0 (%%lambda%%0 %%hole%%0 %%hole%%1 %%hole%%2) a$))
)))
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.to_set.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!seq_lib.impl&%0.to_set.? A&. A& self!) (vstd!set.impl&%0.new.? A&. A& $ (TYPE%fun%1.
       A&. A& $ BOOL
      ) (Poly%fun%1. (mk_fun (%%lambda%%0 A&. A& self!)))
    ))
    :pattern ((vstd!seq_lib.impl&%0.to_set.? A&. A& self!))
    :qid internal_vstd!seq_lib.impl&__0.to_set.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
    (has_type (vstd!seq_lib.impl&%0.to_set.? A&. A& self!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!seq_lib.impl&%0.to_set.? A&. A& self!))
   :qid internal_vstd!seq_lib.impl&__0.to_set.?_pre_post_definition
)))

;; Function-Specs vstd::seq_lib::seq_to_set_is_finite_broadcast
(declare-fun ens%vstd!seq_lib.seq_to_set_is_finite_broadcast. (Dcr Type Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (seq! Poly)) (!
   (= (ens%vstd!seq_lib.seq_to_set_is_finite_broadcast. A&. A& seq!) (vstd!set.impl&%0.finite.?
     A&. A& (vstd!seq_lib.impl&%0.to_set.? A&. A& seq!)
   ))
   :pattern ((ens%vstd!seq_lib.seq_to_set_is_finite_broadcast. A&. A& seq!))
   :qid internal_ens__vstd!seq_lib.seq_to_set_is_finite_broadcast._definition
)))

;; Broadcast vstd::seq_lib::seq_to_set_is_finite_broadcast
(assert
 (forall ((A&. Dcr) (A& Type) (seq! Poly)) (!
   (=>
    (has_type seq! (TYPE%vstd!seq.Seq. A&. A&))
    (vstd!set.impl&%0.finite.? A&. A& (vstd!seq_lib.impl&%0.to_set.? A&. A& seq!))
   )
   :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!seq_lib.impl&%0.to_set.? A&. A& seq!)))
   :qid user_vstd__seq_lib__seq_to_set_is_finite_broadcast_43
)))

;; Function-Axioms vstd::set::impl&%0::union
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
    )
    (has_type (vstd!set.impl&%0.union.? A&. A& self! s2!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.impl&%0.union.? A&. A& self! s2!))
   :qid internal_vstd!set.impl&__0.union.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::intersect
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
    )
    (has_type (vstd!set.impl&%0.intersect.? A&. A& self! s2!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.impl&%0.intersect.? A&. A& self! s2!))
   :qid internal_vstd!set.impl&__0.intersect.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::difference
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
    )
    (has_type (vstd!set.impl&%0.difference.? A&. A& self! s2!) (TYPE%vstd!set.Set. A&.
      A&
   )))
   :pattern ((vstd!set.impl&%0.difference.? A&. A& self! s2!))
   :qid internal_vstd!set.impl&__0.difference.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::complement
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!set.Set. A&. A&))
    (has_type (vstd!set.impl&%0.complement.? A&. A& self!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.impl&%0.complement.? A&. A& self!))
   :qid internal_vstd!set.impl&__0.complement.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::len
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!set.Set. A&. A&))
    (<= 0 (vstd!set.impl&%0.len.? A&. A& self!))
   )
   :pattern ((vstd!set.impl&%0.len.? A&. A& self!))
   :qid internal_vstd!set.impl&__0.len.?_pre_post_definition
)))

;; Function-Specs vstd::set::axiom_set_empty
(declare-fun ens%vstd!set.axiom_set_empty. (Dcr Type Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_empty. A&. A& a!) (not (vstd!set.impl&%0.contains.? A&. A&
      (vstd!set.impl&%0.empty.? A&. A&) a!
   )))
   :pattern ((ens%vstd!set.axiom_set_empty. A&. A& a!))
   :qid internal_ens__vstd!set.axiom_set_empty._definition
)))

;; Broadcast vstd::set::axiom_set_empty
(assert
 (forall ((A&. Dcr) (A& Type) (a! Poly)) (!
   (=>
    (has_type a! A&)
    (not (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.empty.? A&. A&) a!))
   )
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.empty.? A&. A&) a!))
   :qid user_vstd__set__axiom_set_empty_44
)))

;; Function-Specs vstd::set::axiom_set_new
(declare-fun ens%vstd!set.axiom_set_new. (Dcr Type %%Function%% Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (f! %%Function%%) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_new. A&. A& f! a!) (= (vstd!set.impl&%0.contains.? A&. A&
      (vstd!set.impl&%0.new.? A&. A& $ (TYPE%fun%1. A&. A& $ BOOL) (Poly%fun%1. f!)) a!
     ) (%B (%%apply%%0 f! a!))
   ))
   :pattern ((ens%vstd!set.axiom_set_new. A&. A& f! a!))
   :qid internal_ens__vstd!set.axiom_set_new._definition
)))

;; Broadcast vstd::set::axiom_set_new
(assert
 (forall ((A&. Dcr) (A& Type) (f! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type f! (TYPE%fun%1. A&. A& $ BOOL))
     (has_type a! A&)
    )
    (= (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.new.? A&. A& $ (TYPE%fun%1.
        A&. A& $ BOOL
       ) f!
      ) a!
     ) (%B (%%apply%%0 (%Poly%fun%1. f!) a!))
   ))
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.new.? A&. A& $ (TYPE%fun%1.
       A&. A& $ BOOL
      ) f!
     ) a!
   ))
   :qid user_vstd__set__axiom_set_new_45
)))

;; Function-Specs vstd::set::axiom_set_insert_same
(declare-fun ens%vstd!set.axiom_set_insert_same. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_insert_same. A&. A& s! a!) (vstd!set.impl&%0.contains.?
     A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a!) a!
   ))
   :pattern ((ens%vstd!set.axiom_set_insert_same. A&. A& s! a!))
   :qid internal_ens__vstd!set.axiom_set_insert_same._definition
)))

;; Broadcast vstd::set::axiom_set_insert_same
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a!) a!)
   )
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a!)
     a!
   ))
   :qid user_vstd__set__axiom_set_insert_same_46
)))

;; Function-Specs vstd::set::axiom_set_insert_different
(declare-fun req%vstd!set.axiom_set_insert_different. (Dcr Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%30 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
   (= (req%vstd!set.axiom_set_insert_different. A&. A& s! a1! a2!) (=>
     %%global_location_label%%30
     (not (= a1! a2!))
   ))
   :pattern ((req%vstd!set.axiom_set_insert_different. A&. A& s! a1! a2!))
   :qid internal_req__vstd!set.axiom_set_insert_different._definition
)))
(declare-fun ens%vstd!set.axiom_set_insert_different. (Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
   (= (ens%vstd!set.axiom_set_insert_different. A&. A& s! a1! a2!) (= (vstd!set.impl&%0.contains.?
      A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a2!) a1!
     ) (vstd!set.impl&%0.contains.? A&. A& s! a1!)
   ))
   :pattern ((ens%vstd!set.axiom_set_insert_different. A&. A& s! a1! a2!))
   :qid internal_ens__vstd!set.axiom_set_insert_different._definition
)))

;; Broadcast vstd::set::axiom_set_insert_different
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a1! A&)
     (has_type a2! A&)
    )
    (=>
     (not (= a1! a2!))
     (= (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a2!) a1!)
      (vstd!set.impl&%0.contains.? A&. A& s! a1!)
   )))
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a2!)
     a1!
   ))
   :qid user_vstd__set__axiom_set_insert_different_47
)))

;; Function-Specs vstd::set::axiom_set_remove_same
(declare-fun ens%vstd!set.axiom_set_remove_same. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_remove_same. A&. A& s! a!) (not (vstd!set.impl&%0.contains.?
      A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!) a!
   )))
   :pattern ((ens%vstd!set.axiom_set_remove_same. A&. A& s! a!))
   :qid internal_ens__vstd!set.axiom_set_remove_same._definition
)))

;; Broadcast vstd::set::axiom_set_remove_same
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (not (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!) a!))
   )
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!)
     a!
   ))
   :qid user_vstd__set__axiom_set_remove_same_48
)))

;; Function-Specs vstd::set::axiom_set_remove_insert
(declare-fun req%vstd!set.axiom_set_remove_insert. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%31 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (req%vstd!set.axiom_set_remove_insert. A&. A& s! a!) (=>
     %%global_location_label%%31
     (vstd!set.impl&%0.contains.? A&. A& s! a!)
   ))
   :pattern ((req%vstd!set.axiom_set_remove_insert. A&. A& s! a!))
   :qid internal_req__vstd!set.axiom_set_remove_insert._definition
)))
(declare-fun ens%vstd!set.axiom_set_remove_insert. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_remove_insert. A&. A& s! a!) (= (vstd!set.impl&%0.insert.?
      A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!) a!
     ) s!
   ))
   :pattern ((ens%vstd!set.axiom_set_remove_insert. A&. A& s! a!))
   :qid internal_ens__vstd!set.axiom_set_remove_insert._definition
)))

;; Broadcast vstd::set::axiom_set_remove_insert
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (=>
     (vstd!set.impl&%0.contains.? A&. A& s! a!)
     (= (vstd!set.impl&%0.insert.? A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!) a!)
      s!
   )))
   :pattern ((vstd!set.impl&%0.remove.? A&. A& s! a!))
   :qid user_vstd__set__axiom_set_remove_insert_49
)))

;; Function-Specs vstd::set::axiom_set_remove_different
(declare-fun req%vstd!set.axiom_set_remove_different. (Dcr Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%32 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
   (= (req%vstd!set.axiom_set_remove_different. A&. A& s! a1! a2!) (=>
     %%global_location_label%%32
     (not (= a1! a2!))
   ))
   :pattern ((req%vstd!set.axiom_set_remove_different. A&. A& s! a1! a2!))
   :qid internal_req__vstd!set.axiom_set_remove_different._definition
)))
(declare-fun ens%vstd!set.axiom_set_remove_different. (Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
   (= (ens%vstd!set.axiom_set_remove_different. A&. A& s! a1! a2!) (= (vstd!set.impl&%0.contains.?
      A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a2!) a1!
     ) (vstd!set.impl&%0.contains.? A&. A& s! a1!)
   ))
   :pattern ((ens%vstd!set.axiom_set_remove_different. A&. A& s! a1! a2!))
   :qid internal_ens__vstd!set.axiom_set_remove_different._definition
)))

;; Broadcast vstd::set::axiom_set_remove_different
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a1! A&)
     (has_type a2! A&)
    )
    (=>
     (not (= a1! a2!))
     (= (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a2!) a1!)
      (vstd!set.impl&%0.contains.? A&. A& s! a1!)
   )))
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a2!)
     a1!
   ))
   :qid user_vstd__set__axiom_set_remove_different_50
)))

;; Function-Specs vstd::set::axiom_set_union
(declare-fun ens%vstd!set.axiom_set_union. (Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_union. A&. A& s1! s2! a!) (= (vstd!set.impl&%0.contains.?
      A&. A& (vstd!set.impl&%0.union.? A&. A& s1! s2!) a!
     ) (or
      (vstd!set.impl&%0.contains.? A&. A& s1! a!)
      (vstd!set.impl&%0.contains.? A&. A& s2! a!)
   )))
   :pattern ((ens%vstd!set.axiom_set_union. A&. A& s1! s2! a!))
   :qid internal_ens__vstd!set.axiom_set_union._definition
)))

;; Broadcast vstd::set::axiom_set_union
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (= (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.union.? A&. A& s1! s2!) a!)
     (or
      (vstd!set.impl&%0.contains.? A&. A& s1! a!)
      (vstd!set.impl&%0.contains.? A&. A& s2! a!)
   )))
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.union.? A&. A& s1! s2!)
     a!
   ))
   :qid user_vstd__set__axiom_set_union_51
)))

;; Function-Specs vstd::set::axiom_set_intersect
(declare-fun ens%vstd!set.axiom_set_intersect. (Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_intersect. A&. A& s1! s2! a!) (= (vstd!set.impl&%0.contains.?
      A&. A& (vstd!set.impl&%0.intersect.? A&. A& s1! s2!) a!
     ) (and
      (vstd!set.impl&%0.contains.? A&. A& s1! a!)
      (vstd!set.impl&%0.contains.? A&. A& s2! a!)
   )))
   :pattern ((ens%vstd!set.axiom_set_intersect. A&. A& s1! s2! a!))
   :qid internal_ens__vstd!set.axiom_set_intersect._definition
)))

;; Broadcast vstd::set::axiom_set_intersect
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (= (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.intersect.? A&. A& s1! s2!)
      a!
     ) (and
      (vstd!set.impl&%0.contains.? A&. A& s1! a!)
      (vstd!set.impl&%0.contains.? A&. A& s2! a!)
   )))
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.intersect.? A&. A& s1!
      s2!
     ) a!
   ))
   :qid user_vstd__set__axiom_set_intersect_52
)))

;; Function-Specs vstd::set::axiom_set_difference
(declare-fun ens%vstd!set.axiom_set_difference. (Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_difference. A&. A& s1! s2! a!) (= (vstd!set.impl&%0.contains.?
      A&. A& (vstd!set.impl&%0.difference.? A&. A& s1! s2!) a!
     ) (and
      (vstd!set.impl&%0.contains.? A&. A& s1! a!)
      (not (vstd!set.impl&%0.contains.? A&. A& s2! a!))
   )))
   :pattern ((ens%vstd!set.axiom_set_difference. A&. A& s1! s2! a!))
   :qid internal_ens__vstd!set.axiom_set_difference._definition
)))

;; Broadcast vstd::set::axiom_set_difference
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (= (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.difference.? A&. A& s1! s2!)
      a!
     ) (and
      (vstd!set.impl&%0.contains.? A&. A& s1! a!)
      (not (vstd!set.impl&%0.contains.? A&. A& s2! a!))
   )))
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.difference.? A&. A&
      s1! s2!
     ) a!
   ))
   :qid user_vstd__set__axiom_set_difference_53
)))

;; Function-Specs vstd::set::axiom_set_complement
(declare-fun ens%vstd!set.axiom_set_complement. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_complement. A&. A& s! a!) (= (vstd!set.impl&%0.contains.?
      A&. A& (vstd!set.impl&%0.complement.? A&. A& s!) a!
     ) (not (vstd!set.impl&%0.contains.? A&. A& s! a!))
   ))
   :pattern ((ens%vstd!set.axiom_set_complement. A&. A& s! a!))
   :qid internal_ens__vstd!set.axiom_set_complement._definition
)))

;; Broadcast vstd::set::axiom_set_complement
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (= (vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.complement.? A&. A& s!) a!)
     (not (vstd!set.impl&%0.contains.? A&. A& s! a!))
   ))
   :pattern ((vstd!set.impl&%0.contains.? A&. A& (vstd!set.impl&%0.complement.? A&. A&
      s!
     ) a!
   ))
   :qid user_vstd__set__axiom_set_complement_54
)))

;; Function-Specs vstd::set::axiom_set_ext_equal
(declare-fun ens%vstd!set.axiom_set_ext_equal. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!set.axiom_set_ext_equal. A&. A& s1! s2!) (= (ext_eq false (TYPE%vstd!set.Set.
       A&. A&
      ) s1! s2!
     ) (forall ((a$ Poly)) (!
       (=>
        (has_type a$ A&)
        (= (vstd!set.impl&%0.contains.? A&. A& s1! a$) (vstd!set.impl&%0.contains.? A&. A&
          s2! a$
       )))
       :pattern ((vstd!set.impl&%0.contains.? A&. A& s1! a$))
       :pattern ((vstd!set.impl&%0.contains.? A&. A& s2! a$))
       :qid user_vstd__set__axiom_set_ext_equal_55
   ))))
   :pattern ((ens%vstd!set.axiom_set_ext_equal. A&. A& s1! s2!))
   :qid internal_ens__vstd!set.axiom_set_ext_equal._definition
)))

;; Broadcast vstd::set::axiom_set_ext_equal
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
    )
    (= (ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!) (forall ((a$ Poly)) (!
       (=>
        (has_type a$ A&)
        (= (vstd!set.impl&%0.contains.? A&. A& s1! a$) (vstd!set.impl&%0.contains.? A&. A&
          s2! a$
       )))
       :pattern ((vstd!set.impl&%0.contains.? A&. A& s1! a$))
       :pattern ((vstd!set.impl&%0.contains.? A&. A& s2! a$))
       :qid user_vstd__set__axiom_set_ext_equal_56
   ))))
   :pattern ((ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!))
   :qid user_vstd__set__axiom_set_ext_equal_57
)))

;; Function-Specs vstd::set::axiom_set_ext_equal_deep
(declare-fun ens%vstd!set.axiom_set_ext_equal_deep. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!set.axiom_set_ext_equal_deep. A&. A& s1! s2!) (= (ext_eq true (TYPE%vstd!set.Set.
       A&. A&
      ) s1! s2!
     ) (ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!)
   ))
   :pattern ((ens%vstd!set.axiom_set_ext_equal_deep. A&. A& s1! s2!))
   :qid internal_ens__vstd!set.axiom_set_ext_equal_deep._definition
)))

;; Broadcast vstd::set::axiom_set_ext_equal_deep
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
    )
    (= (ext_eq true (TYPE%vstd!set.Set. A&. A&) s1! s2!) (ext_eq false (TYPE%vstd!set.Set.
       A&. A&
      ) s1! s2!
   )))
   :pattern ((ext_eq true (TYPE%vstd!set.Set. A&. A&) s1! s2!))
   :qid user_vstd__set__axiom_set_ext_equal_deep_58
)))

;; Function-Specs vstd::set::axiom_mk_map_domain
(declare-fun ens%vstd!set.axiom_mk_map_domain. (Dcr Type Dcr Type Poly %%Function%%)
 Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (s! Poly) (f! %%Function%%)) (!
   (= (ens%vstd!set.axiom_mk_map_domain. K&. K& V&. V& s! f!) (= (vstd!map.impl&%0.dom.?
      K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K& V&. V& $ (TYPE%fun%1. K&. K& V&. V&)
       s! (Poly%fun%1. f!)
      )
     ) s!
   ))
   :pattern ((ens%vstd!set.axiom_mk_map_domain. K&. K& V&. V& s! f!))
   :qid internal_ens__vstd!set.axiom_mk_map_domain._definition
)))

;; Broadcast vstd::set::axiom_mk_map_domain
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (s! Poly) (f! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. K&. K&))
     (has_type f! (TYPE%fun%1. K&. K& V&. V&))
    )
    (= (vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K& V&. V& $
       (TYPE%fun%1. K&. K& V&. V&) s! f!
      )
     ) s!
   ))
   :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K& V&.
      V& $ (TYPE%fun%1. K&. K& V&. V&) s! f!
   )))
   :qid user_vstd__set__axiom_mk_map_domain_59
)))

;; Function-Specs vstd::set::axiom_mk_map_index
(declare-fun req%vstd!set.axiom_mk_map_index. (Dcr Type Dcr Type Poly %%Function%%
  Poly
 ) Bool
)
(declare-const %%global_location_label%%33 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (s! Poly) (f! %%Function%%) (key! Poly))
  (!
   (= (req%vstd!set.axiom_mk_map_index. K&. K& V&. V& s! f! key!) (=>
     %%global_location_label%%33
     (vstd!set.impl&%0.contains.? K&. K& s! key!)
   ))
   :pattern ((req%vstd!set.axiom_mk_map_index. K&. K& V&. V& s! f! key!))
   :qid internal_req__vstd!set.axiom_mk_map_index._definition
)))
(declare-fun ens%vstd!set.axiom_mk_map_index. (Dcr Type Dcr Type Poly %%Function%%
  Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (s! Poly) (f! %%Function%%) (key! Poly))
  (!
   (= (ens%vstd!set.axiom_mk_map_index. K&. K& V&. V& s! f! key!) (= (vstd!map.impl&%0.index.?
      K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K& V&. V& $ (TYPE%fun%1. K&. K& V&. V&)
       s! (Poly%fun%1. f!)
      ) key!
     ) (%%apply%%0 f! key!)
   ))
   :pattern ((ens%vstd!set.axiom_mk_map_index. K&. K& V&. V& s! f! key!))
   :qid internal_ens__vstd!set.axiom_mk_map_index._definition
)))

;; Broadcast vstd::set::axiom_mk_map_index
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (s! Poly) (f! Poly) (key! Poly))
  (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. K&. K&))
     (has_type f! (TYPE%fun%1. K&. K& V&. V&))
     (has_type key! K&)
    )
    (=>
     (vstd!set.impl&%0.contains.? K&. K& s! key!)
     (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K& V&. V&
        $ (TYPE%fun%1. K&. K& V&. V&) s! f!
       ) key!
      ) (%%apply%%0 (%Poly%fun%1. f!) key!)
   )))
   :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K&
      V&. V& $ (TYPE%fun%1. K&. K& V&. V&) s! f!
     ) key!
   ))
   :qid user_vstd__set__axiom_mk_map_index_60
)))

;; Function-Specs vstd::set::axiom_set_empty_finite
(declare-fun ens%vstd!set.axiom_set_empty_finite. (Dcr Type) Bool)
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (ens%vstd!set.axiom_set_empty_finite. A&. A&) (vstd!set.impl&%0.finite.? A&. A&
     (vstd!set.impl&%0.empty.? A&. A&)
   ))
   :pattern ((ens%vstd!set.axiom_set_empty_finite. A&. A&))
   :qid internal_ens__vstd!set.axiom_set_empty_finite._definition
)))

;; Broadcast vstd::set::axiom_set_empty_finite
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.empty.? A&. A&))
   :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.empty.? A&. A&)))
   :qid user_vstd__set__axiom_set_empty_finite_61
)))

;; Function-Specs vstd::set::axiom_set_insert_finite
(declare-fun req%vstd!set.axiom_set_insert_finite. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%34 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (req%vstd!set.axiom_set_insert_finite. A&. A& s! a!) (=>
     %%global_location_label%%34
     (vstd!set.impl&%0.finite.? A&. A& s!)
   ))
   :pattern ((req%vstd!set.axiom_set_insert_finite. A&. A& s! a!))
   :qid internal_req__vstd!set.axiom_set_insert_finite._definition
)))
(declare-fun ens%vstd!set.axiom_set_insert_finite. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_insert_finite. A&. A& s! a!) (vstd!set.impl&%0.finite.?
     A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a!)
   ))
   :pattern ((ens%vstd!set.axiom_set_insert_finite. A&. A& s! a!))
   :qid internal_ens__vstd!set.axiom_set_insert_finite._definition
)))

;; Broadcast vstd::set::axiom_set_insert_finite
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (=>
     (vstd!set.impl&%0.finite.? A&. A& s!)
     (vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a!))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a!)))
   :qid user_vstd__set__axiom_set_insert_finite_62
)))

;; Function-Specs vstd::set::axiom_set_remove_finite
(declare-fun req%vstd!set.axiom_set_remove_finite. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%35 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (req%vstd!set.axiom_set_remove_finite. A&. A& s! a!) (=>
     %%global_location_label%%35
     (vstd!set.impl&%0.finite.? A&. A& s!)
   ))
   :pattern ((req%vstd!set.axiom_set_remove_finite. A&. A& s! a!))
   :qid internal_req__vstd!set.axiom_set_remove_finite._definition
)))
(declare-fun ens%vstd!set.axiom_set_remove_finite. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_remove_finite. A&. A& s! a!) (vstd!set.impl&%0.finite.?
     A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!)
   ))
   :pattern ((ens%vstd!set.axiom_set_remove_finite. A&. A& s! a!))
   :qid internal_ens__vstd!set.axiom_set_remove_finite._definition
)))

;; Broadcast vstd::set::axiom_set_remove_finite
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (=>
     (vstd!set.impl&%0.finite.? A&. A& s!)
     (vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!)))
   :qid user_vstd__set__axiom_set_remove_finite_63
)))

;; Function-Specs vstd::set::axiom_set_union_finite
(declare-fun req%vstd!set.axiom_set_union_finite. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%36 Bool)
(declare-const %%global_location_label%%37 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (req%vstd!set.axiom_set_union_finite. A&. A& s1! s2!) (and
     (=>
      %%global_location_label%%36
      (vstd!set.impl&%0.finite.? A&. A& s1!)
     )
     (=>
      %%global_location_label%%37
      (vstd!set.impl&%0.finite.? A&. A& s2!)
   )))
   :pattern ((req%vstd!set.axiom_set_union_finite. A&. A& s1! s2!))
   :qid internal_req__vstd!set.axiom_set_union_finite._definition
)))
(declare-fun ens%vstd!set.axiom_set_union_finite. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!set.axiom_set_union_finite. A&. A& s1! s2!) (vstd!set.impl&%0.finite.?
     A&. A& (vstd!set.impl&%0.union.? A&. A& s1! s2!)
   ))
   :pattern ((ens%vstd!set.axiom_set_union_finite. A&. A& s1! s2!))
   :qid internal_ens__vstd!set.axiom_set_union_finite._definition
)))

;; Broadcast vstd::set::axiom_set_union_finite
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
    )
    (=>
     (and
      (vstd!set.impl&%0.finite.? A&. A& s1!)
      (vstd!set.impl&%0.finite.? A&. A& s2!)
     )
     (vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.union.? A&. A& s1! s2!))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.union.? A&. A& s1! s2!)))
   :qid user_vstd__set__axiom_set_union_finite_64
)))

;; Function-Specs vstd::set::axiom_set_intersect_finite
(declare-fun req%vstd!set.axiom_set_intersect_finite. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%38 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (req%vstd!set.axiom_set_intersect_finite. A&. A& s1! s2!) (=>
     %%global_location_label%%38
     (or
      (vstd!set.impl&%0.finite.? A&. A& s1!)
      (vstd!set.impl&%0.finite.? A&. A& s2!)
   )))
   :pattern ((req%vstd!set.axiom_set_intersect_finite. A&. A& s1! s2!))
   :qid internal_req__vstd!set.axiom_set_intersect_finite._definition
)))
(declare-fun ens%vstd!set.axiom_set_intersect_finite. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!set.axiom_set_intersect_finite. A&. A& s1! s2!) (vstd!set.impl&%0.finite.?
     A&. A& (vstd!set.impl&%0.intersect.? A&. A& s1! s2!)
   ))
   :pattern ((ens%vstd!set.axiom_set_intersect_finite. A&. A& s1! s2!))
   :qid internal_ens__vstd!set.axiom_set_intersect_finite._definition
)))

;; Broadcast vstd::set::axiom_set_intersect_finite
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
    )
    (=>
     (or
      (vstd!set.impl&%0.finite.? A&. A& s1!)
      (vstd!set.impl&%0.finite.? A&. A& s2!)
     )
     (vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.intersect.? A&. A& s1! s2!))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.intersect.? A&. A& s1!
      s2!
   )))
   :qid user_vstd__set__axiom_set_intersect_finite_65
)))

;; Function-Specs vstd::set::axiom_set_difference_finite
(declare-fun req%vstd!set.axiom_set_difference_finite. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%39 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (req%vstd!set.axiom_set_difference_finite. A&. A& s1! s2!) (=>
     %%global_location_label%%39
     (vstd!set.impl&%0.finite.? A&. A& s1!)
   ))
   :pattern ((req%vstd!set.axiom_set_difference_finite. A&. A& s1! s2!))
   :qid internal_req__vstd!set.axiom_set_difference_finite._definition
)))
(declare-fun ens%vstd!set.axiom_set_difference_finite. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!set.axiom_set_difference_finite. A&. A& s1! s2!) (vstd!set.impl&%0.finite.?
     A&. A& (vstd!set.impl&%0.difference.? A&. A& s1! s2!)
   ))
   :pattern ((ens%vstd!set.axiom_set_difference_finite. A&. A& s1! s2!))
   :qid internal_ens__vstd!set.axiom_set_difference_finite._definition
)))

;; Broadcast vstd::set::axiom_set_difference_finite
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type s1! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
    )
    (=>
     (vstd!set.impl&%0.finite.? A&. A& s1!)
     (vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.difference.? A&. A& s1! s2!))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.difference.? A&. A& s1!
      s2!
   )))
   :qid user_vstd__set__axiom_set_difference_finite_66
)))

;; Function-Axioms vstd::set::impl&%0::choose
(assert
 (fuel_bool_default fuel%vstd!set.impl&%0.choose.)
)
(declare-fun %%choose%%0 (Type Dcr Type Poly Dcr Type Poly) Poly)
(assert
 (forall ((%%hole%%0 Type) (%%hole%%1 Dcr) (%%hole%%2 Type) (%%hole%%3 Poly) (%%hole%%4
    Dcr
   ) (%%hole%%5 Type) (%%hole%%6 Poly)
  ) (!
   (=>
    (exists ((a$ Poly)) (!
      (and
       (has_type a$ %%hole%%0)
       (vstd!set.impl&%0.contains.? %%hole%%1 %%hole%%2 %%hole%%3 a$)
      )
      :pattern ((vstd!set.impl&%0.contains.? %%hole%%4 %%hole%%5 %%hole%%6 a$))
      :qid user_vstd__set__impl&%0__choose_67
    ))
    (exists ((a$ Poly)) (!
      (and
       (and
        (has_type a$ %%hole%%0)
        (vstd!set.impl&%0.contains.? %%hole%%1 %%hole%%2 %%hole%%3 a$)
       )
       (= (%%choose%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5 %%hole%%6)
        a$
      ))
      :pattern ((vstd!set.impl&%0.contains.? %%hole%%4 %%hole%%5 %%hole%%6 a$))
   )))
   :pattern ((%%choose%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
     %%hole%%6
)))))
(assert
 (=>
  (fuel_bool fuel%vstd!set.impl&%0.choose.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!set.impl&%0.choose.? A&. A& self!) (as_type (%%choose%%0 A& A&. A& self! A&.
       A& self!
      ) A&
    ))
    :pattern ((vstd!set.impl&%0.choose.? A&. A& self!))
    :qid internal_vstd!set.impl&__0.choose.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!set.Set. A&. A&))
    (has_type (vstd!set.impl&%0.choose.? A&. A& self!) A&)
   )
   :pattern ((vstd!set.impl&%0.choose.? A&. A& self!))
   :qid internal_vstd!set.impl&__0.choose.?_pre_post_definition
)))

;; Function-Specs vstd::set::axiom_set_choose_finite
(declare-fun req%vstd!set.axiom_set_choose_finite. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%40 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly)) (!
   (= (req%vstd!set.axiom_set_choose_finite. A&. A& s!) (=>
     %%global_location_label%%40
     (not (vstd!set.impl&%0.finite.? A&. A& s!))
   ))
   :pattern ((req%vstd!set.axiom_set_choose_finite. A&. A& s!))
   :qid internal_req__vstd!set.axiom_set_choose_finite._definition
)))
(declare-fun ens%vstd!set.axiom_set_choose_finite. (Dcr Type Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly)) (!
   (= (ens%vstd!set.axiom_set_choose_finite. A&. A& s!) (vstd!set.impl&%0.contains.? A&.
     A& s! (vstd!set.impl&%0.choose.? A&. A& s!)
   ))
   :pattern ((ens%vstd!set.axiom_set_choose_finite. A&. A& s!))
   :qid internal_ens__vstd!set.axiom_set_choose_finite._definition
)))

;; Broadcast vstd::set::axiom_set_choose_finite
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly)) (!
   (=>
    (has_type s! (TYPE%vstd!set.Set. A&. A&))
    (=>
     (not (vstd!set.impl&%0.finite.? A&. A& s!))
     (vstd!set.impl&%0.contains.? A&. A& s! (vstd!set.impl&%0.choose.? A&. A& s!))
   ))
   :pattern ((vstd!set.impl&%0.contains.? A&. A& s! (vstd!set.impl&%0.choose.? A&. A& s!)))
   :qid user_vstd__set__axiom_set_choose_finite_68
)))

;; Function-Specs vstd::set::axiom_set_empty_len
(declare-fun ens%vstd!set.axiom_set_empty_len. (Dcr Type) Bool)
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (ens%vstd!set.axiom_set_empty_len. A&. A&) (= (vstd!set.impl&%0.len.? A&. A& (vstd!set.impl&%0.empty.?
       A&. A&
      )
     ) 0
   ))
   :pattern ((ens%vstd!set.axiom_set_empty_len. A&. A&))
   :qid internal_ens__vstd!set.axiom_set_empty_len._definition
)))

;; Broadcast vstd::set::axiom_set_empty_len
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (vstd!set.impl&%0.len.? A&. A& (vstd!set.impl&%0.empty.? A&. A&)) 0)
   :pattern ((vstd!set.impl&%0.len.? A&. A& (vstd!set.impl&%0.empty.? A&. A&)))
   :qid user_vstd__set__axiom_set_empty_len_69
)))

;; Function-Specs vstd::set::axiom_set_insert_len
(declare-fun req%vstd!set.axiom_set_insert_len. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%41 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (req%vstd!set.axiom_set_insert_len. A&. A& s! a!) (=>
     %%global_location_label%%41
     (vstd!set.impl&%0.finite.? A&. A& s!)
   ))
   :pattern ((req%vstd!set.axiom_set_insert_len. A&. A& s! a!))
   :qid internal_req__vstd!set.axiom_set_insert_len._definition
)))
(declare-fun ens%vstd!set.axiom_set_insert_len. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_insert_len. A&. A& s! a!) (= (vstd!set.impl&%0.len.? A&.
      A& (vstd!set.impl&%0.insert.? A&. A& s! a!)
     ) (Add (vstd!set.impl&%0.len.? A&. A& s!) (ite
       (vstd!set.impl&%0.contains.? A&. A& s! a!)
       0
       1
   ))))
   :pattern ((ens%vstd!set.axiom_set_insert_len. A&. A& s! a!))
   :qid internal_ens__vstd!set.axiom_set_insert_len._definition
)))

;; Broadcast vstd::set::axiom_set_insert_len
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (=>
     (vstd!set.impl&%0.finite.? A&. A& s!)
     (= (vstd!set.impl&%0.len.? A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a!)) (Add (vstd!set.impl&%0.len.?
        A&. A& s!
       ) (ite
        (vstd!set.impl&%0.contains.? A&. A& s! a!)
        0
        1
   )))))
   :pattern ((vstd!set.impl&%0.len.? A&. A& (vstd!set.impl&%0.insert.? A&. A& s! a!)))
   :qid user_vstd__set__axiom_set_insert_len_70
)))

;; Function-Specs vstd::set::axiom_set_remove_len
(declare-fun req%vstd!set.axiom_set_remove_len. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%42 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (req%vstd!set.axiom_set_remove_len. A&. A& s! a!) (=>
     %%global_location_label%%42
     (vstd!set.impl&%0.finite.? A&. A& s!)
   ))
   :pattern ((req%vstd!set.axiom_set_remove_len. A&. A& s! a!))
   :qid internal_req__vstd!set.axiom_set_remove_len._definition
)))
(declare-fun ens%vstd!set.axiom_set_remove_len. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_remove_len. A&. A& s! a!) (= (vstd!set.impl&%0.len.? A&.
      A& s!
     ) (Add (vstd!set.impl&%0.len.? A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!)) (ite
       (vstd!set.impl&%0.contains.? A&. A& s! a!)
       1
       0
   ))))
   :pattern ((ens%vstd!set.axiom_set_remove_len. A&. A& s! a!))
   :qid internal_ens__vstd!set.axiom_set_remove_len._definition
)))

;; Broadcast vstd::set::axiom_set_remove_len
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (=>
     (vstd!set.impl&%0.finite.? A&. A& s!)
     (= (vstd!set.impl&%0.len.? A&. A& s!) (Add (vstd!set.impl&%0.len.? A&. A& (vstd!set.impl&%0.remove.?
         A&. A& s! a!
        )
       ) (ite
        (vstd!set.impl&%0.contains.? A&. A& s! a!)
        1
        0
   )))))
   :pattern ((vstd!set.impl&%0.len.? A&. A& (vstd!set.impl&%0.remove.? A&. A& s! a!)))
   :qid user_vstd__set__axiom_set_remove_len_71
)))

;; Function-Specs vstd::set::axiom_set_contains_len
(declare-fun req%vstd!set.axiom_set_contains_len. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%43 Bool)
(declare-const %%global_location_label%%44 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (req%vstd!set.axiom_set_contains_len. A&. A& s! a!) (and
     (=>
      %%global_location_label%%43
      (vstd!set.impl&%0.finite.? A&. A& s!)
     )
     (=>
      %%global_location_label%%44
      (vstd!set.impl&%0.contains.? A&. A& s! a!)
   )))
   :pattern ((req%vstd!set.axiom_set_contains_len. A&. A& s! a!))
   :qid internal_req__vstd!set.axiom_set_contains_len._definition
)))
(declare-fun ens%vstd!set.axiom_set_contains_len. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!set.axiom_set_contains_len. A&. A& s! a!) (not (= (vstd!set.impl&%0.len.?
       A&. A& s!
      ) 0
   )))
   :pattern ((ens%vstd!set.axiom_set_contains_len. A&. A& s! a!))
   :qid internal_ens__vstd!set.axiom_set_contains_len._definition
)))

;; Broadcast vstd::set::axiom_set_contains_len
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (=>
     (and
      (vstd!set.impl&%0.finite.? A&. A& s!)
      (vstd!set.impl&%0.contains.? A&. A& s! a!)
     )
     (not (= (vstd!set.impl&%0.len.? A&. A& s!) 0))
   ))
   :pattern ((vstd!set.impl&%0.contains.? A&. A& s! a!) (vstd!set.impl&%0.len.? A&. A&
     s!
   ))
   :qid user_vstd__set__axiom_set_contains_len_72
)))

;; Function-Specs vstd::set::axiom_set_choose_len
(declare-fun req%vstd!set.axiom_set_choose_len. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%45 Bool)
(declare-const %%global_location_label%%46 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly)) (!
   (= (req%vstd!set.axiom_set_choose_len. A&. A& s!) (and
     (=>
      %%global_location_label%%45
      (vstd!set.impl&%0.finite.? A&. A& s!)
     )
     (=>
      %%global_location_label%%46
      (not (= (vstd!set.impl&%0.len.? A&. A& s!) 0))
   )))
   :pattern ((req%vstd!set.axiom_set_choose_len. A&. A& s!))
   :qid internal_req__vstd!set.axiom_set_choose_len._definition
)))
(declare-fun ens%vstd!set.axiom_set_choose_len. (Dcr Type Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly)) (!
   (= (ens%vstd!set.axiom_set_choose_len. A&. A& s!) (vstd!set.impl&%0.contains.? A&.
     A& s! (vstd!set.impl&%0.choose.? A&. A& s!)
   ))
   :pattern ((ens%vstd!set.axiom_set_choose_len. A&. A& s!))
   :qid internal_ens__vstd!set.axiom_set_choose_len._definition
)))

;; Broadcast vstd::set::axiom_set_choose_len
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly)) (!
   (=>
    (has_type s! (TYPE%vstd!set.Set. A&. A&))
    (=>
     (and
      (vstd!set.impl&%0.finite.? A&. A& s!)
      (not (= (vstd!set.impl&%0.len.? A&. A& s!) 0))
     )
     (vstd!set.impl&%0.contains.? A&. A& s! (vstd!set.impl&%0.choose.? A&. A& s!))
   ))
   :pattern ((vstd!set.impl&%0.len.? A&. A& s!) (vstd!set.impl&%0.contains.? A&. A& s!
     (vstd!set.impl&%0.choose.? A&. A& s!)
   ))
   :qid user_vstd__set__axiom_set_choose_len_73
)))

;; Function-Axioms lib::marshal_v::Marshalable::is_marshalable
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (lib!marshal_v.Marshalable.is_marshalable.? Self%&. Self%& self!) BOOL)
   )
   :pattern ((lib!marshal_v.Marshalable.is_marshalable.? Self%&. Self%& self!))
   :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_pre_post_definition
)))

;; Function-Specs lib::marshal_v::Marshalable::ghost_serialize
(declare-fun req%lib!marshal_v.Marshalable.ghost_serialize. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%47 Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly)) (!
   (= (req%lib!marshal_v.Marshalable.ghost_serialize. Self%&. Self%& self!) (=>
     %%global_location_label%%47
     (%B (lib!marshal_v.Marshalable.is_marshalable.? Self%&. Self%& self!))
   ))
   :pattern ((req%lib!marshal_v.Marshalable.ghost_serialize. Self%&. Self%& self!))
   :qid internal_req__lib!marshal_v.Marshalable.ghost_serialize._definition
)))

;; Function-Axioms lib::marshal_v::Marshalable::ghost_serialize
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (lib!marshal_v.Marshalable.ghost_serialize.? Self%&. Self%& self!) (TYPE%vstd!seq.Seq.
      $ (UINT 8)
   )))
   :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? Self%&. Self%& self!))
   :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_pre_post_definition
)))

;; Function-Axioms lib::marshal_v::Marshalable::view_equal
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly) (other! Poly)) (!
   (=>
    (and
     (has_type self! Self%&)
     (has_type other! Self%&)
    )
    (has_type (lib!marshal_v.Marshalable.view_equal.? Self%&. Self%& self! other!) BOOL)
   )
   :pattern ((lib!marshal_v.Marshalable.view_equal.? Self%&. Self%& self! other!))
   :qid internal_lib!marshal_v.Marshalable.view_equal.?_pre_post_definition
)))

;; Function-Specs lib::marshal_v::Marshalable::lemma_serialize_injective
(declare-fun req%lib!marshal_v.Marshalable.lemma_serialize_injective. (Dcr Type Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%48 Bool)
(declare-const %%global_location_label%%49 Bool)
(declare-const %%global_location_label%%50 Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly) (other! Poly)) (!
   (= (req%lib!marshal_v.Marshalable.lemma_serialize_injective. Self%&. Self%& self! other!)
    (and
     (=>
      %%global_location_label%%48
      (%B (lib!marshal_v.Marshalable.is_marshalable.? Self%&. Self%& self!))
     )
     (=>
      %%global_location_label%%49
      (%B (lib!marshal_v.Marshalable.is_marshalable.? Self%&. Self%& other!))
     )
     (=>
      %%global_location_label%%50
      (= (lib!marshal_v.Marshalable.ghost_serialize.? Self%&. Self%& self!) (lib!marshal_v.Marshalable.ghost_serialize.?
        Self%&. Self%& other!
   )))))
   :pattern ((req%lib!marshal_v.Marshalable.lemma_serialize_injective. Self%&. Self%&
     self! other!
   ))
   :qid internal_req__lib!marshal_v.Marshalable.lemma_serialize_injective._definition
)))
(declare-fun ens%lib!marshal_v.Marshalable.lemma_serialize_injective. (Dcr Type Poly
  Poly
 ) Bool
)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly) (other! Poly)) (!
   (= (ens%lib!marshal_v.Marshalable.lemma_serialize_injective. Self%&. Self%& self! other!)
    (%B (lib!marshal_v.Marshalable.view_equal.? Self%&. Self%& self! other!))
   )
   :pattern ((ens%lib!marshal_v.Marshalable.lemma_serialize_injective. Self%&. Self%&
     self! other!
   ))
   :qid internal_ens__lib!marshal_v.Marshalable.lemma_serialize_injective._definition
)))

;; Function-Axioms lib::io_t::EndPoint::view
(assert
 (fuel_bool_default fuel%lib!io_t.impl&%5.view.)
)
(assert
 (=>
  (fuel_bool fuel%lib!io_t.impl&%5.view.)
  (forall ((self! Poly)) (!
    (= (lib!io_t.impl&%5.view.? self!) (lib!abstract_end_point_t.AbstractEndPoint./AbstractEndPoint
      (%Poly%vstd!seq.Seq<u8.>. (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $
         TYPE%alloc!alloc.Global.
        ) (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!io_t.EndPoint./EndPoint/id (%Poly%lib!io_t.EndPoint.
           self!
    )))))))
    :pattern ((lib!io_t.impl&%5.view.? self!))
    :qid internal_lib!io_t.impl&__5.view.?_definition
))))

;; Function-Axioms lib::hashmap_t::ckeykvlt
(assert
 (fuel_bool_default fuel%lib!hashmap_t.ckeykvlt.)
)
(assert
 (=>
  (fuel_bool fuel%lib!hashmap_t.ckeykvlt.)
  (forall ((a! Poly) (b! Poly)) (!
    (= (lib!hashmap_t.ckeykvlt.? a! b!) (< (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey.
        (Poly%lib!keys_t.SHTKey. (lib!hashmap_t.CKeyKV./CKeyKV/k (%Poly%lib!hashmap_t.CKeyKV.
           a!
       ))))
      ) (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
         (lib!hashmap_t.CKeyKV./CKeyKV/k (%Poly%lib!hashmap_t.CKeyKV. b!))
    )))))
    :pattern ((lib!hashmap_t.ckeykvlt.? a! b!))
    :qid internal_lib!hashmap_t.ckeykvlt.?_definition
))))

;; Function-Axioms lib::hashmap_t::spec_sorted_keys
(assert
 (fuel_bool_default fuel%lib!hashmap_t.spec_sorted_keys.)
)
(assert
 (=>
  (fuel_bool fuel%lib!hashmap_t.spec_sorted_keys.)
  (forall ((v! Poly)) (!
    (= (lib!hashmap_t.spec_sorted_keys.? v!) (forall ((i$ Poly) (j$ Poly)) (!
       (=>
        (and
         (has_type i$ INT)
         (has_type j$ INT)
        )
        (=>
         (and
          (and
           (<= 0 (%I i$))
           (< (Add (%I i$) 1) (vstd!std_specs.vec.spec_vec_len.? $ TYPE%lib!hashmap_t.CKeyKV.
             $ TYPE%alloc!alloc.Global. v!
          )))
          (= (%I j$) (Add (%I i$) 1))
         )
         (lib!hashmap_t.ckeykvlt.? (vstd!seq.Seq.index.? $ TYPE%lib!hashmap_t.CKeyKV. (vstd!view.View.view.?
            $ (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.) v!
           ) i$
          ) (vstd!seq.Seq.index.? $ TYPE%lib!hashmap_t.CKeyKV. (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
             $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.
            ) v!
           ) j$
       ))))
       :pattern ((lib!hashmap_t.ckeykvlt.? (vstd!seq.Seq.index.? $ TYPE%lib!hashmap_t.CKeyKV.
          (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.)
           v!
          ) i$
         ) (vstd!seq.Seq.index.? $ TYPE%lib!hashmap_t.CKeyKV. (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
            $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.
           ) v!
          ) j$
       )))
       :qid user_lib__hashmap_t__spec_sorted_keys_74
    )))
    :pattern ((lib!hashmap_t.spec_sorted_keys.? v!))
    :qid internal_lib!hashmap_t.spec_sorted_keys.?_definition
))))

;; Function-Axioms lib::hashmap_t::CKeyKV::view
(assert
 (fuel_bool_default fuel%lib!hashmap_t.impl&%1.view.)
)
(assert
 (=>
  (fuel_bool fuel%lib!hashmap_t.impl&%1.view.)
  (forall ((self! Poly)) (!
    (= (lib!hashmap_t.impl&%1.view.? self!) (tuple%2./tuple%2 (Poly%lib!keys_t.SHTKey. (
        lib!hashmap_t.CKeyKV./CKeyKV/k (%Poly%lib!hashmap_t.CKeyKV. self!)
       )
      ) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
       (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!hashmap_t.CKeyKV./CKeyKV/v (%Poly%lib!hashmap_t.CKeyKV.
          self!
    ))))))
    :pattern ((lib!hashmap_t.impl&%1.view.? self!))
    :qid internal_lib!hashmap_t.impl&__1.view.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%lib!hashmap_t.CKeyKV.)
    (has_type (Poly%tuple%2. (lib!hashmap_t.impl&%1.view.? self!)) (TYPE%tuple%2. $ TYPE%lib!keys_t.SHTKey.
      $ (TYPE%vstd!seq.Seq. $ (UINT 8))
   )))
   :pattern ((lib!hashmap_t.impl&%1.view.? self!))
   :qid internal_lib!hashmap_t.impl&__1.view.?_pre_post_definition
)))

;; Function-Axioms vstd::map_lib::impl&%0::contains_pair
(assert
 (fuel_bool_default fuel%vstd!map_lib.impl&%0.contains_pair.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map_lib.impl&%0.contains_pair.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (k! Poly) (v! Poly))
   (!
    (= (vstd!map_lib.impl&%0.contains_pair.? K&. K& V&. V& self! k! v!) (and
      (vstd!set.impl&%0.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) k!)
      (= (vstd!map.impl&%0.index.? K&. K& V&. V& self! k!) v!)
    ))
    :pattern ((vstd!map_lib.impl&%0.contains_pair.? K&. K& V&. V& self! k! v!))
    :qid internal_vstd!map_lib.impl&__0.contains_pair.?_definition
))))

;; Function-Specs lib::hashmap_t::CKeyHashMap::lemma_to_vec
(declare-fun ens%lib!hashmap_t.impl&%0.lemma_to_vec. (lib!hashmap_t.CKeyHashMap.)
 Bool
)
(assert
 (forall ((self! lib!hashmap_t.CKeyHashMap.)) (!
   (= (ens%lib!hashmap_t.impl&%0.lemma_to_vec. self!) (and
     (= (lib!hashmap_t.impl&%0.spec_from_vec.? (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
        (lib!hashmap_t.impl&%0.spec_to_vec.? (Poly%lib!hashmap_t.CKeyHashMap. self!))
       )
      ) self!
     )
     (= (vstd!std_specs.vec.spec_vec_len.? $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.
       (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
         (Poly%lib!hashmap_t.CKeyHashMap. self!)
       ))
      ) (vstd!set.impl&%0.len.? $ TYPE%lib!keys_t.SHTKey. (vstd!map.impl&%0.dom.? $ TYPE%lib!keys_t.SHTKey.
        $ (TYPE%vstd!seq.Seq. $ (UINT 8)) (Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.
         (lib!hashmap_t.impl&%0.view.? (Poly%lib!hashmap_t.CKeyHashMap. self!))
     ))))
     (lib!hashmap_t.spec_sorted_keys.? (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
       (lib!hashmap_t.impl&%0.spec_to_vec.? (Poly%lib!hashmap_t.CKeyHashMap. self!))
     ))
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ INT)
        (=>
         (and
          (<= 0 (%I i$))
          (< (%I i$) (vstd!std_specs.vec.spec_vec_len.? $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.
            (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
              (Poly%lib!hashmap_t.CKeyHashMap. self!)
         )))))
         (let
          ((tmp%%$ (lib!hashmap_t.impl&%1.view.? (vstd!seq.Seq.index.? $ TYPE%lib!hashmap_t.CKeyKV.
              (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.)
               (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
                 (Poly%lib!hashmap_t.CKeyHashMap. self!)
               ))
              ) i$
          ))))
          (let
           ((k$ (%Poly%lib!keys_t.SHTKey. (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))))))
           (let
            ((v$ (%Poly%vstd!seq.Seq<u8.>. (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))))))
            (vstd!map_lib.impl&%0.contains_pair.? $ TYPE%lib!keys_t.SHTKey. $ (TYPE%vstd!seq.Seq.
              $ (UINT 8)
             ) (Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. (lib!hashmap_t.impl&%0.view.?
               (Poly%lib!hashmap_t.CKeyHashMap. self!)
              )
             ) (Poly%lib!keys_t.SHTKey. k$) (Poly%vstd!seq.Seq<u8.>. v$)
       ))))))
       :pattern ((vstd!seq.Seq.index.? $ TYPE%lib!hashmap_t.CKeyKV. (vstd!view.View.view.?
          $ (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.) (
           Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
            (Poly%lib!hashmap_t.CKeyHashMap. self!)
          ))
         ) i$
       ))
       :qid user_lib__hashmap_t__CKeyHashMap__lemma_to_vec_75
   ))))
   :pattern ((ens%lib!hashmap_t.impl&%0.lemma_to_vec. self!))
   :qid internal_ens__lib!hashmap_t.impl&__0.lemma_to_vec._definition
)))

;; Broadcast lib::hashmap_t::CKeyHashMap::lemma_to_vec
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%lib!hashmap_t.CKeyHashMap.)
    (and
     (and
      (and
       (= (lib!hashmap_t.impl&%0.spec_from_vec.? (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
          (lib!hashmap_t.impl&%0.spec_to_vec.? self!)
         )
        ) (%Poly%lib!hashmap_t.CKeyHashMap. self!)
       )
       (= (vstd!std_specs.vec.spec_vec_len.? $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.
         (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
           self!
         ))
        ) (vstd!set.impl&%0.len.? $ TYPE%lib!keys_t.SHTKey. (vstd!map.impl&%0.dom.? $ TYPE%lib!keys_t.SHTKey.
          $ (TYPE%vstd!seq.Seq. $ (UINT 8)) (Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.
           (lib!hashmap_t.impl&%0.view.? self!)
      )))))
      (lib!hashmap_t.spec_sorted_keys.? (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
        (lib!hashmap_t.impl&%0.spec_to_vec.? self!)
     )))
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ INT)
        (=>
         (and
          (<= 0 (%I i$))
          (< (%I i$) (vstd!std_specs.vec.spec_vec_len.? $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.
            (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
              self!
         )))))
         (let
          ((tmp%%$ (lib!hashmap_t.impl&%1.view.? (vstd!seq.Seq.index.? $ TYPE%lib!hashmap_t.CKeyKV.
              (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.)
               (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
                 self!
               ))
              ) i$
          ))))
          (let
           ((k$ (%Poly%lib!keys_t.SHTKey. (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))))))
           (let
            ((v$ (%Poly%vstd!seq.Seq<u8.>. (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))))))
            (vstd!map_lib.impl&%0.contains_pair.? $ TYPE%lib!keys_t.SHTKey. $ (TYPE%vstd!seq.Seq.
              $ (UINT 8)
             ) (Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. (lib!hashmap_t.impl&%0.view.?
               self!
              )
             ) (Poly%lib!keys_t.SHTKey. k$) (Poly%vstd!seq.Seq<u8.>. v$)
       ))))))
       :pattern ((vstd!seq.Seq.index.? $ TYPE%lib!hashmap_t.CKeyKV. (vstd!view.View.view.?
          $ (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.) (
           Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
            self!
          ))
         ) i$
       ))
       :qid user_lib__hashmap_t__CKeyHashMap__lemma_to_vec_76
   ))))
   :pattern ((lib!hashmap_t.impl&%0.spec_from_vec.? (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
      (lib!hashmap_t.impl&%0.spec_to_vec.? self!)
   )))
   :qid user_lib__hashmap_t__CKeyHashMap__lemma_to_vec_77
)))

;; Function-Specs lib::hashmap_t::CKeyHashMap::lemma_from_vec
(declare-fun ens%lib!hashmap_t.impl&%0.lemma_from_vec. (alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.)
 Bool
)
(assert
 (forall ((v! alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.)) (!
   (= (ens%lib!hashmap_t.impl&%0.lemma_from_vec. v!) (=>
     (lib!hashmap_t.spec_sorted_keys.? (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
       v!
     ))
     (= (lib!hashmap_t.impl&%0.spec_to_vec.? (Poly%lib!hashmap_t.CKeyHashMap. (lib!hashmap_t.impl&%0.spec_from_vec.?
         (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. v!)
       ))
      ) v!
   )))
   :pattern ((ens%lib!hashmap_t.impl&%0.lemma_from_vec. v!))
   :qid internal_ens__lib!hashmap_t.impl&__0.lemma_from_vec._definition
)))

;; Broadcast lib::hashmap_t::CKeyHashMap::lemma_from_vec
(assert
 (forall ((v! Poly)) (!
   (=>
    (has_type v! (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.))
    (=>
     (lib!hashmap_t.spec_sorted_keys.? v!)
     (= (lib!hashmap_t.impl&%0.spec_to_vec.? (Poly%lib!hashmap_t.CKeyHashMap. (lib!hashmap_t.impl&%0.spec_from_vec.?
         v!
       ))
      ) (%Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. v!)
   )))
   :pattern ((lib!hashmap_t.spec_sorted_keys.? v!))
   :qid user_lib__hashmap_t__CKeyHashMap__lemma_from_vec_78
)))

;; Function-Axioms vstd::std_specs::vec::impl&%2::spec_len
(assert
 (fuel_bool_default fuel%vstd!std_specs.vec.impl&%2.spec_len.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.vec.impl&%2.spec_len.)
  (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!std_specs.vec.VecAdditionalSpecFns.spec_len.? $ (TYPE%alloc!vec.Vec. T&. T&
       A&. A&
      ) T&. T& self!
     ) (I (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T&
         A&. A&
        ) self!
    ))))
    :pattern ((vstd!std_specs.vec.VecAdditionalSpecFns.spec_len.? $ (TYPE%alloc!vec.Vec.
       T&. T& A&. A&
      ) T&. T& self!
    ))
    :qid internal_vstd!std_specs.vec.VecAdditionalSpecFns.spec_len.?_definition
))))

;; Function-Axioms vstd::seq_lib::impl&%0::fold_left
(assert
 (fuel_bool_default fuel%vstd!seq_lib.impl&%0.fold_left.)
)
(declare-const fuel_nat%vstd!seq_lib.impl&%0.fold_left. Fuel)
(assert
 (forall ((A&. Dcr) (A& Type) (B&. Dcr) (B& Type) (self! Poly) (b! Poly) (f! Poly) (
    fuel% Fuel
   )
  ) (!
   (= (vstd!seq_lib.impl&%0.rec%fold_left.? A&. A& B&. B& self! b! f! fuel%) (vstd!seq_lib.impl&%0.rec%fold_left.?
     A&. A& B&. B& self! b! f! zero
   ))
   :pattern ((vstd!seq_lib.impl&%0.rec%fold_left.? A&. A& B&. B& self! b! f! fuel%))
   :qid internal_vstd!seq_lib.impl&__0.fold_left._fuel_to_zero_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type) (B&. Dcr) (B& Type) (self! Poly) (b! Poly) (f! Poly) (
    fuel% Fuel
   )
  ) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type b! B&)
     (has_type f! (TYPE%fun%2. B&. B& A&. A& B&. B&))
    )
    (= (vstd!seq_lib.impl&%0.rec%fold_left.? A&. A& B&. B& self! b! f! (succ fuel%)) (
      ite
      (= (vstd!seq.Seq.len.? A&. A& self!) 0)
      b!
      (%%apply%%1 (%Poly%fun%2. f!) (vstd!seq_lib.impl&%0.rec%fold_left.? A&. A& B&. B& (
         vstd!seq_lib.impl&%0.drop_last.? A&. A& self!
        ) b! f! fuel%
       ) (vstd!seq.Seq.last.? A&. A& self!)
   ))))
   :pattern ((vstd!seq_lib.impl&%0.rec%fold_left.? A&. A& B&. B& self! b! f! (succ fuel%)))
   :qid internal_vstd!seq_lib.impl&__0.fold_left._fuel_to_body_definition
)))
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.fold_left.)
  (forall ((A&. Dcr) (A& Type) (B&. Dcr) (B& Type) (self! Poly) (b! Poly) (f! Poly))
   (!
    (=>
     (and
      (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type b! B&)
      (has_type f! (TYPE%fun%2. B&. B& A&. A& B&. B&))
     )
     (= (vstd!seq_lib.impl&%0.fold_left.? A&. A& B&. B& self! b! f!) (vstd!seq_lib.impl&%0.rec%fold_left.?
       A&. A& B&. B& self! b! f! (succ fuel_nat%vstd!seq_lib.impl&%0.fold_left.)
    )))
    :pattern ((vstd!seq_lib.impl&%0.fold_left.? A&. A& B&. B& self! b! f!))
    :qid internal_vstd!seq_lib.impl&__0.fold_left.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (B&. Dcr) (B& Type) (self! Poly) (b! Poly) (f! Poly))
  (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type b! B&)
     (has_type f! (TYPE%fun%2. B&. B& A&. A& B&. B&))
    )
    (has_type (vstd!seq_lib.impl&%0.fold_left.? A&. A& B&. B& self! b! f!) B&)
   )
   :pattern ((vstd!seq_lib.impl&%0.fold_left.? A&. A& B&. B& self! b! f!))
   :qid internal_vstd!seq_lib.impl&__0.fold_left.?_pre_post_definition
)))

;; Function-Axioms vstd::view::impl&%0::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%0.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%0.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!view.View.view.? (REF A&.) A& self!) (vstd!view.View.view.? A&. A& self!))
    :pattern ((vstd!view.View.view.? (REF A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%2::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%2.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%2.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!view.View.view.? (BOX A&.) A& self!) (vstd!view.View.view.? A&. A& self!))
    :pattern ((vstd!view.View.view.? (BOX A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%4::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%4.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%4.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!view.View.view.? (RC A&.) A& self!) (vstd!view.View.view.? A&. A& self!))
    :pattern ((vstd!view.View.view.? (RC A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%6::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%6.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%6.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!view.View.view.? (ARC A&.) A& self!) (vstd!view.View.view.? A&. A& self!))
    :pattern ((vstd!view.View.view.? (ARC A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%8::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%8.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%8.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ TYPE%tuple%0. self!) self!)
    :pattern ((vstd!view.View.view.? $ TYPE%tuple%0. self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%10::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%10.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%10.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ BOOL self!) self!)
    :pattern ((vstd!view.View.view.? $ BOOL self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%12::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%12.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%12.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT 8) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT 8) self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%18::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%18.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%18.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT 64) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT 64) self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%22::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%22.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%22.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT SZ) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT SZ) self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%38::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%38.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%38.view.)
  (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type) (self! Poly)) (!
    (= (vstd!view.View.view.? $ (TYPE%tuple%2. A0&. A0& A1&. A1&) self!) (Poly%tuple%2.
      (tuple%2./tuple%2 (vstd!view.View.view.? A0&. A0& (tuple%2./tuple%2/0 (%Poly%tuple%2.
          self!
        ))
       ) (vstd!view.View.view.? A1&. A1& (tuple%2./tuple%2/1 (%Poly%tuple%2. self!)))
    )))
    :pattern ((vstd!view.View.view.? $ (TYPE%tuple%2. A0&. A0& A1&. A1&) self!))
    :qid internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms lib::cmessage_v::optional_value_view
(assert
 (fuel_bool_default fuel%lib!cmessage_v.optional_value_view.)
)
(assert
 (=>
  (fuel_bool fuel%lib!cmessage_v.optional_value_view.)
  (forall ((ov! Poly)) (!
    (= (lib!cmessage_v.optional_value_view.? ov!) (ite
      (is-core!option.Option./Some (%Poly%core!option.Option. ov!))
      (let
       ((v$ (%Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (core!option.Option./Some/0 (%Poly%core!option.Option.
            ov!
       )))))
       (core!option.Option./Some (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $
          TYPE%alloc!alloc.Global.
         ) (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. v$)
      )))
      core!option.Option./None
    ))
    :pattern ((lib!cmessage_v.optional_value_view.? ov!))
    :qid internal_lib!cmessage_v.optional_value_view.?_definition
))))
(assert
 (forall ((ov! Poly)) (!
   (=>
    (has_type ov! (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)))
    (has_type (Poly%core!option.Option. (lib!cmessage_v.optional_value_view.? ov!)) (TYPE%core!option.Option.
      $ (TYPE%vstd!seq.Seq. $ (UINT 8))
   )))
   :pattern ((lib!cmessage_v.optional_value_view.? ov!))
   :qid internal_lib!cmessage_v.optional_value_view.?_pre_post_definition
)))

;; Function-Axioms lib::cmessage_v::CMessage::view
(assert
 (fuel_bool_default fuel%lib!cmessage_v.impl&%1.view.)
)
(assert
 (=>
  (fuel_bool fuel%lib!cmessage_v.impl&%1.view.)
  (forall ((self! Poly)) (!
    (= (lib!cmessage_v.impl&%1.view.? self!) (ite
      (is-lib!cmessage_v.CMessage./GetRequest (%Poly%lib!cmessage_v.CMessage. self!))
      (let
       ((k$ (lib!cmessage_v.CMessage./GetRequest/k (%Poly%lib!cmessage_v.CMessage. self!))))
       (lib!message_t.Message./GetRequest (%Poly%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
          k$
      ))))
      (ite
       (is-lib!cmessage_v.CMessage./SetRequest (%Poly%lib!cmessage_v.CMessage. self!))
       (let
        ((k$ (lib!cmessage_v.CMessage./SetRequest/k (%Poly%lib!cmessage_v.CMessage. self!))))
        (let
         ((v$ (lib!cmessage_v.CMessage./SetRequest/v (%Poly%lib!cmessage_v.CMessage. self!))))
         (lib!message_t.Message./SetRequest (%Poly%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
            k$
           )
          ) (%Poly%core!option.Option. (Poly%core!option.Option. (lib!cmessage_v.optional_value_view.?
             (Poly%core!option.Option. v$)
       ))))))
       (ite
        (is-lib!cmessage_v.CMessage./Reply (%Poly%lib!cmessage_v.CMessage. self!))
        (let
         ((k$ (lib!cmessage_v.CMessage./Reply/k (%Poly%lib!cmessage_v.CMessage. self!))))
         (let
          ((v$ (lib!cmessage_v.CMessage./Reply/v (%Poly%lib!cmessage_v.CMessage. self!))))
          (lib!message_t.Message./Reply (%Poly%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey. k$))
           (%Poly%core!option.Option. (Poly%core!option.Option. (lib!cmessage_v.optional_value_view.?
              (Poly%core!option.Option. v$)
        ))))))
        (ite
         (is-lib!cmessage_v.CMessage./Redirect (%Poly%lib!cmessage_v.CMessage. self!))
         (let
          ((k$ (lib!cmessage_v.CMessage./Redirect/k (%Poly%lib!cmessage_v.CMessage. self!))))
          (let
           ((id$ (lib!cmessage_v.CMessage./Redirect/id (%Poly%lib!cmessage_v.CMessage. self!))))
           (lib!message_t.Message./Redirect (%Poly%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
              k$
             )
            ) (%Poly%lib!abstract_end_point_t.AbstractEndPoint. (Poly%lib!abstract_end_point_t.AbstractEndPoint.
              (lib!io_t.impl&%5.view.? (Poly%lib!io_t.EndPoint. id$))
         )))))
         (ite
          (is-lib!cmessage_v.CMessage./Shard (%Poly%lib!cmessage_v.CMessage. self!))
          (let
           ((kr$ (lib!cmessage_v.CMessage./Shard/kr (%Poly%lib!cmessage_v.CMessage. self!))))
           (let
            ((recipient$ (lib!cmessage_v.CMessage./Shard/recipient (%Poly%lib!cmessage_v.CMessage.
                self!
            ))))
            (lib!message_t.Message./Shard (%Poly%lib!keys_t.KeyRange. (Poly%lib!keys_t.KeyRange.
               kr$
              )
             ) (%Poly%lib!abstract_end_point_t.AbstractEndPoint. (Poly%lib!abstract_end_point_t.AbstractEndPoint.
               (lib!io_t.impl&%5.view.? (Poly%lib!io_t.EndPoint. recipient$))
          )))))
          (let
           ((range$ (lib!cmessage_v.CMessage./Delegate/range (%Poly%lib!cmessage_v.CMessage. self!))))
           (let
            ((h$ (lib!cmessage_v.CMessage./Delegate/h (%Poly%lib!cmessage_v.CMessage. self!))))
            (lib!message_t.Message./Delegate (%Poly%lib!keys_t.KeyRange. (Poly%lib!keys_t.KeyRange.
               range$
              )
             ) (%Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>. (Poly%vstd!map.Map<lib!keys_t.SHTKey./vstd!seq.Seq<u8.>.>.
               (lib!hashmap_t.impl&%0.view.? (Poly%lib!hashmap_t.CKeyHashMap. h$))
    )))))))))))
    :pattern ((lib!cmessage_v.impl&%1.view.? self!))
    :qid internal_lib!cmessage_v.impl&__1.view.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%lib!cmessage_v.CMessage.)
    (has_type (Poly%lib!message_t.Message. (lib!cmessage_v.impl&%1.view.? self!)) TYPE%lib!message_t.Message.)
   )
   :pattern ((lib!cmessage_v.impl&%1.view.? self!))
   :qid internal_lib!cmessage_v.impl&__1.view.?_pre_post_definition
)))

;; Function-Axioms lib::cmessage_v::CSingleMessage::view
(assert
 (fuel_bool_default fuel%lib!cmessage_v.impl&%2.view.)
)
(assert
 (=>
  (fuel_bool fuel%lib!cmessage_v.impl&%2.view.)
  (forall ((self! Poly)) (!
    (= (lib!cmessage_v.impl&%2.view.? self!) (ite
      (is-lib!cmessage_v.CSingleMessage./Message (%Poly%lib!cmessage_v.CSingleMessage. self!))
      (let
       ((seqno$ (lib!cmessage_v.CSingleMessage./Message/seqno (%Poly%lib!cmessage_v.CSingleMessage.
           self!
       ))))
       (let
        ((dst$ (lib!cmessage_v.CSingleMessage./Message/dst (%Poly%lib!cmessage_v.CSingleMessage.
            self!
        ))))
        (let
         ((m$ (lib!cmessage_v.CSingleMessage./Message/m (%Poly%lib!cmessage_v.CSingleMessage.
             self!
         ))))
         (lib!single_message_t.SingleMessage./Message (%I (I seqno$)) (%Poly%lib!abstract_end_point_t.AbstractEndPoint.
           (Poly%lib!abstract_end_point_t.AbstractEndPoint. (lib!io_t.impl&%5.view.? (Poly%lib!io_t.EndPoint.
              dst$
           )))
          ) (Poly%lib!message_t.Message. (lib!cmessage_v.impl&%1.view.? (Poly%lib!cmessage_v.CMessage.
             m$
      )))))))
      (ite
       (is-lib!cmessage_v.CSingleMessage./Ack (%Poly%lib!cmessage_v.CSingleMessage. self!))
       (let
        ((ack_seqno$ (lib!cmessage_v.CSingleMessage./Ack/ack_seqno (%Poly%lib!cmessage_v.CSingleMessage.
            self!
        ))))
        (lib!single_message_t.SingleMessage./Ack (%I (I ack_seqno$)))
       )
       lib!single_message_t.SingleMessage./InvalidMessage
    )))
    :pattern ((lib!cmessage_v.impl&%2.view.? self!))
    :qid internal_lib!cmessage_v.impl&__2.view.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%lib!cmessage_v.CSingleMessage.)
    (has_type (Poly%lib!single_message_t.SingleMessage. (lib!cmessage_v.impl&%2.view.? self!))
     (TYPE%lib!single_message_t.SingleMessage. $ TYPE%lib!message_t.Message.)
   ))
   :pattern ((lib!cmessage_v.impl&%2.view.? self!))
   :qid internal_lib!cmessage_v.impl&__2.view.?_pre_post_definition
)))

;; Function-Axioms lib::marshal_v::impl&%0::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%0.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%0.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ (UINT 64) self! other!) (B (= self! other!)))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ (UINT 64) self! other!))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms alloc::vec::Vec::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%2.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%2.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
      self! other!
     ) (B (= (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
        self!
       ) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
        other!
    ))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ (TYPE%alloc!vec.Vec. $ (UINT 8)
       $ TYPE%alloc!alloc.Global.
      ) self! other!
    ))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms lib::io_t::EndPoint::forward_bijection_for_view_equality_do_not_use_for_anything_else
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%7.forward_bijection_for_view_equality_do_not_use_for_anything_else.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%7.forward_bijection_for_view_equality_do_not_use_for_anything_else.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_ironsht_specific_v.impl&%7.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
      self!
     ) (lib!io_t.EndPoint./EndPoint/id (%Poly%lib!io_t.EndPoint. self!))
    )
    :pattern ((lib!marshal_ironsht_specific_v.impl&%7.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
      self!
    ))
    :qid internal_lib!marshal_ironsht_specific_v.impl&__7.forward_bijection_for_view_equality_do_not_use_for_anything_else.?_definition
))))

;; Function-Axioms lib::io_t::EndPoint::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%8.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%8.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!io_t.EndPoint. self! other!)
     (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
      (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!marshal_ironsht_specific_v.impl&%7.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
        self!
       )
      ) (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!marshal_ironsht_specific_v.impl&%7.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
        other!
    ))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!io_t.EndPoint. self! other!))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms lib::keys_t::SHTKey::forward_bijection_for_view_equality_do_not_use_for_anything_else
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
      self!
     ) (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey. self!))
    )
    :pattern ((lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
      self!
    ))
    :qid internal_lib!marshal_ironsht_specific_v.impl&__9.forward_bijection_for_view_equality_do_not_use_for_anything_else.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%lib!keys_t.SHTKey.)
    (uInv 64 (lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
      self!
   )))
   :pattern ((lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
     self!
   ))
   :qid internal_lib!marshal_ironsht_specific_v.impl&__9.forward_bijection_for_view_equality_do_not_use_for_anything_else.?_pre_post_definition
)))

;; Function-Axioms lib::keys_t::SHTKey::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%10.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%10.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!keys_t.SHTKey. self! other!)
     (lib!marshal_v.Marshalable.view_equal.? $ (UINT 64) (I (lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
        self!
       )
      ) (I (lib!marshal_ironsht_specific_v.impl&%9.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
        other!
    ))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!keys_t.SHTKey. self! other!))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms lib::marshal_v::impl&%0::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%0.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%0.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ (UINT 64) self!) (Poly%vstd!seq.Seq<u8.>.
      (vstd!bytes.spec_u64_to_le_bytes.? self!)
    ))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ (UINT 64) self!))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms lib::marshal_v::impl&%1::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%1.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%1.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ (UINT SZ) self!) (lib!marshal_v.Marshalable.ghost_serialize.?
      $ (UINT 64) (I (uClip 64 (%I self!)))
    ))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ (UINT SZ) self!))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms alloc::vec::Vec::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%2.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%2.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
      self!
     ) (B (and
       (<= (vstd!seq.Seq.len.? $ (UINT 8) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ (UINT
            8
           ) $ TYPE%alloc!alloc.Global.
          ) self!
         )
        ) (- (uHi SZ) 1)
       )
       (<= (Add (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
           $ (UINT SZ) (I (uClip SZ (vstd!seq.Seq.len.? $ (UINT 8) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
                $ (UINT 8) $ TYPE%alloc!alloc.Global.
               ) self!
          )))))
         ) (vstd!seq.Seq.len.? $ (UINT 8) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ (UINT
             8
            ) $ TYPE%alloc!alloc.Global.
           ) self!
         ))
        ) (- (uHi SZ) 1)
    ))))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%alloc!vec.Vec. $ (UINT
        8
       ) $ TYPE%alloc!alloc.Global.
      ) self!
    ))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::marshal_v::impl&%1::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%1.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%1.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ (UINT SZ) self!) (B (<= (%I self!)
       18446744073709551615
    )))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ (UINT SZ) self!))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::marshal_v::impl&%0::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%0.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%0.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ (UINT 64) self!) (B true))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ (UINT 64) self!))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms alloc::vec::Vec::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%2.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%2.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $
       TYPE%alloc!alloc.Global.
      ) self!
     ) (vstd!seq.Seq.add.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ (UINT
        SZ
       ) (I (uClip SZ (vstd!seq.Seq.len.? $ (UINT 8) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
            $ (UINT 8) $ TYPE%alloc!alloc.Global.
           ) self!
       ))))
      ) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
       self!
    )))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%alloc!vec.Vec. $ (UINT
        8
       ) $ TYPE%alloc!alloc.Global.
      ) self!
    ))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.))
)

;; Function-Axioms core::option::Option::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%3.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%3.view_equal.)
  (forall ((T&. Dcr) (T& Type) (self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%core!option.Option. T&. T&) self!
      other!
     ) (B (let
       ((tmp%%$ (tuple%2./tuple%2 self! other!)))
       (=>
        (not (and
          (is-core!option.Option./None (%Poly%core!option.Option. (tuple%2./tuple%2/0 (%Poly%tuple%2.
              (Poly%tuple%2. tmp%%$)
          ))))
          (is-core!option.Option./None (%Poly%core!option.Option. (tuple%2./tuple%2/1 (%Poly%tuple%2.
              (Poly%tuple%2. tmp%%$)
        ))))))
        (and
         (and
          (is-core!option.Option./Some (%Poly%core!option.Option. (tuple%2./tuple%2/0 (%Poly%tuple%2.
              (Poly%tuple%2. tmp%%$)
          ))))
          (is-core!option.Option./Some (%Poly%core!option.Option. (tuple%2./tuple%2/1 (%Poly%tuple%2.
              (Poly%tuple%2. tmp%%$)
         )))))
         (%B (let
           ((s$ (core!option.Option./Some/0 (%Poly%core!option.Option. (tuple%2./tuple%2/0 (%Poly%tuple%2.
                 (Poly%tuple%2. tmp%%$)
           ))))))
           (let
            ((o$ (core!option.Option./Some/0 (%Poly%core!option.Option. (tuple%2./tuple%2/1 (%Poly%tuple%2.
                  (Poly%tuple%2. tmp%%$)
            ))))))
            (lib!marshal_v.Marshalable.view_equal.? T&. T& s$ o$)
    ))))))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ (TYPE%core!option.Option. T&. T&)
      self! other!
    ))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms core::option::Option::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%3.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%3.is_marshalable.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%core!option.Option. T&. T&)
      self!
     ) (B (=>
       (not (is-core!option.Option./None (%Poly%core!option.Option. self!)))
       (let
        ((x$ (core!option.Option./Some/0 (%Poly%core!option.Option. self!))))
        (and
         (%B (lib!marshal_v.Marshalable.is_marshalable.? T&. T& x$))
         (<= (nClip (Add 1 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
              T&. T& x$
           )))
          ) (- (uHi SZ) 1)
    ))))))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%core!option.Option. T&.
       T&
      ) self!
    ))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms core::option::Option::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%3.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%3.ghost_serialize.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%core!option.Option. T&. T&)
      self!
     ) (ite
      (is-core!option.Option./None (%Poly%core!option.Option. self!))
      (vstd!seq.Seq.push.? $ (UINT 8) (vstd!seq.Seq.empty.? $ (UINT 8)) (I 0))
      (let
       ((x$ (core!option.Option./Some/0 (%Poly%core!option.Option. self!))))
       (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.push.? $ (UINT 8) (vstd!seq.Seq.empty.?
          $ (UINT 8)
         ) (I 1)
        ) (lib!marshal_v.Marshalable.ghost_serialize.? T&. T& x$)
    ))))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%core!option.Option. T&.
       T&
      ) self!
    ))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (tr_bound%lib!marshal_v.Marshalable. T&. T&)
    (tr_bound%lib!marshal_v.Marshalable. $ (TYPE%core!option.Option. T&. T&))
   )
   :pattern ((tr_bound%lib!marshal_v.Marshalable. $ (TYPE%core!option.Option. T&. T&)))
   :qid internal_lib__marshal_v__impl&__3_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ (UINT 64))
)

;; Function-Axioms lib::marshal_v::impl&%5::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%5.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%5.view_equal.)
  (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%tuple%2. T&. T& U&. U&) self! other!)
     (B (and
       (%B (lib!marshal_v.Marshalable.view_equal.? T&. T& (tuple%2./tuple%2/0 (%Poly%tuple%2.
           self!
          )
         ) (tuple%2./tuple%2/0 (%Poly%tuple%2. other!))
       ))
       (%B (lib!marshal_v.Marshalable.view_equal.? U&. U& (tuple%2./tuple%2/1 (%Poly%tuple%2.
           self!
          )
         ) (tuple%2./tuple%2/1 (%Poly%tuple%2. other!))
    )))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ (TYPE%tuple%2. T&. T& U&. U&) self!
      other!
    ))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms lib::keys_t::KeyRange::forward_bijection_for_view_equality_do_not_use_for_anything_else
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
      self!
     ) (tuple%2./tuple%2 (Poly%core!option.Option. (let
        ((tmp%%$ (lib!keys_t.KeyIterator./KeyIterator/k (%Poly%lib!keys_t.KeyIterator. (Poly%lib!keys_t.KeyIterator.
             (lib!keys_t.KeyRange./KeyRange/lo (%Poly%lib!keys_t.KeyRange. self!))
        )))))
        (ite
         (is-core!option.Option./None tmp%%$)
         core!option.Option./None
         (let
          ((x$ (%Poly%lib!keys_t.SHTKey. (core!option.Option./Some/0 (%Poly%core!option.Option.
               (Poly%core!option.Option. tmp%%$)
          )))))
          (core!option.Option./Some (I (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey.
              (Poly%lib!keys_t.SHTKey. x$)
       )))))))
      ) (Poly%core!option.Option. (let
        ((tmp%%$ (lib!keys_t.KeyIterator./KeyIterator/k (%Poly%lib!keys_t.KeyIterator. (Poly%lib!keys_t.KeyIterator.
             (lib!keys_t.KeyRange./KeyRange/hi (%Poly%lib!keys_t.KeyRange. self!))
        )))))
        (ite
         (is-core!option.Option./None tmp%%$)
         core!option.Option./None
         (let
          ((x$ (%Poly%lib!keys_t.SHTKey. (core!option.Option./Some/0 (%Poly%core!option.Option.
               (Poly%core!option.Option. tmp%%$)
          )))))
          (core!option.Option./Some (I (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey.
              (Poly%lib!keys_t.SHTKey. x$)
    ))))))))))
    :pattern ((lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
      self!
    ))
    :qid internal_lib!marshal_ironsht_specific_v.impl&__5.forward_bijection_for_view_equality_do_not_use_for_anything_else.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.))
    (has_type (Poly%tuple%2. (lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
       self!
      )
     ) (TYPE%tuple%2. $ (TYPE%core!option.Option. $ (UINT 64)) $ (TYPE%core!option.Option.
       $ (UINT 64)
   ))))
   :pattern ((lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
     self!
   ))
   :qid internal_lib!marshal_ironsht_specific_v.impl&__5.forward_bijection_for_view_equality_do_not_use_for_anything_else.?_pre_post_definition
)))

;; Function-Axioms lib::keys_t::KeyRange::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%6.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%6.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
      self! other!
     ) (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%tuple%2. $ (TYPE%core!option.Option.
        $ (UINT 64)
       ) $ (TYPE%core!option.Option. $ (UINT 64))
      ) (Poly%tuple%2. (lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
        self!
       )
      ) (Poly%tuple%2. (lib!marshal_ironsht_specific_v.impl&%5.forward_bijection_for_view_equality_do_not_use_for_anything_else.?
        other!
    ))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
      self! other!
    ))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms lib::hashmap_t::CKeyHashMap::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%2.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%2.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!hashmap_t.CKeyHashMap. self!
      other!
     ) (B (= (lib!hashmap_t.impl&%0.view.? self!) (lib!hashmap_t.impl&%0.view.? other!)))
    )
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!hashmap_t.CKeyHashMap.
      self! other!
    ))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms lib::cmessage_v::CMessage::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%3.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%3.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!cmessage_v.CMessage. self! other!)
     (B (let
       ((tmp%%$ (tuple%2./tuple%2 self! other!)))
       (ite
        (and
         (is-lib!cmessage_v.CMessage./GetRequest (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
            (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
         )))
         (is-lib!cmessage_v.CMessage./GetRequest (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
            (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
        ))))
        (let
         ((k$ (lib!cmessage_v.CMessage./GetRequest/k (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
              (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
         )))))
         (let
          ((o0$ (lib!cmessage_v.CMessage./GetRequest/k (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
               (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
          )))))
          (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
             k$
            ) (Poly%lib!keys_t.SHTKey. o0$)
        ))))
        (ite
         (and
          (is-lib!cmessage_v.CMessage./SetRequest (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
             (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
          )))
          (is-lib!cmessage_v.CMessage./SetRequest (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
             (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
         ))))
         (let
          ((k$ (lib!cmessage_v.CMessage./SetRequest/k (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
               (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
          )))))
          (let
           ((v$ (lib!cmessage_v.CMessage./SetRequest/v (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
           )))))
           (let
            ((o0$ (lib!cmessage_v.CMessage./SetRequest/k (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
            )))))
            (let
             ((o1$ (lib!cmessage_v.CMessage./SetRequest/v (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                  (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
             )))))
             (and
              (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
                 k$
                ) (Poly%lib!keys_t.SHTKey. o0$)
              ))
              (%B (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec.
                  $ (UINT 8) $ TYPE%alloc!alloc.Global.
                 )
                ) (Poly%core!option.Option. v$) (Poly%core!option.Option. o1$)
         )))))))
         (ite
          (and
           (is-lib!cmessage_v.CMessage./Reply (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
              (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
           )))
           (is-lib!cmessage_v.CMessage./Reply (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
              (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
          ))))
          (let
           ((k$ (lib!cmessage_v.CMessage./Reply/k (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
           )))))
           (let
            ((v$ (lib!cmessage_v.CMessage./Reply/v (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
            )))))
            (let
             ((o0$ (lib!cmessage_v.CMessage./Reply/k (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                  (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
             )))))
             (let
              ((o1$ (lib!cmessage_v.CMessage./Reply/v (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                   (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
              )))))
              (and
               (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
                  k$
                 ) (Poly%lib!keys_t.SHTKey. o0$)
               ))
               (%B (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec.
                   $ (UINT 8) $ TYPE%alloc!alloc.Global.
                  )
                 ) (Poly%core!option.Option. v$) (Poly%core!option.Option. o1$)
          )))))))
          (ite
           (and
            (is-lib!cmessage_v.CMessage./Redirect (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
               (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
            )))
            (is-lib!cmessage_v.CMessage./Redirect (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
               (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
           ))))
           (let
            ((k$ (lib!cmessage_v.CMessage./Redirect/k (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
            )))))
            (let
             ((id$ (lib!cmessage_v.CMessage./Redirect/id (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                  (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
             )))))
             (let
              ((o0$ (lib!cmessage_v.CMessage./Redirect/k (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                   (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
              )))))
              (let
               ((o1$ (lib!cmessage_v.CMessage./Redirect/id (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                    (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
               )))))
               (and
                (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
                   k$
                  ) (Poly%lib!keys_t.SHTKey. o0$)
                ))
                (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint.
                   id$
                  ) (Poly%lib!io_t.EndPoint. o1$)
           )))))))
           (ite
            (and
             (is-lib!cmessage_v.CMessage./Shard (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
             )))
             (is-lib!cmessage_v.CMessage./Shard (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
            ))))
            (let
             ((kr$ (lib!cmessage_v.CMessage./Shard/kr (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                  (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
             )))))
             (let
              ((recipient$ (lib!cmessage_v.CMessage./Shard/recipient (%Poly%lib!cmessage_v.CMessage.
                  (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
              ))))
              (let
               ((o0$ (lib!cmessage_v.CMessage./Shard/kr (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                    (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
               )))))
               (let
                ((o1$ (lib!cmessage_v.CMessage./Shard/recipient (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                     (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
                )))))
                (and
                 (%B (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
                   (Poly%lib!keys_t.KeyRange. kr$) (Poly%lib!keys_t.KeyRange. o0$)
                 ))
                 (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint.
                    recipient$
                   ) (Poly%lib!io_t.EndPoint. o1$)
            )))))))
            (and
             (and
              (is-lib!cmessage_v.CMessage./Delegate (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
              )))
              (is-lib!cmessage_v.CMessage./Delegate (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
             ))))
             (let
              ((range$ (lib!cmessage_v.CMessage./Delegate/range (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                   (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
              )))))
              (let
               ((h$ (lib!cmessage_v.CMessage./Delegate/h (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/0
                    (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
               )))))
               (let
                ((o0$ (lib!cmessage_v.CMessage./Delegate/range (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                     (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
                )))))
                (let
                 ((o1$ (lib!cmessage_v.CMessage./Delegate/h (%Poly%lib!cmessage_v.CMessage. (tuple%2./tuple%2/1
                      (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
                 )))))
                 (and
                  (%B (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
                    (Poly%lib!keys_t.KeyRange. range$) (Poly%lib!keys_t.KeyRange. o0$)
                  ))
                  (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!hashmap_t.CKeyHashMap. (Poly%lib!hashmap_t.CKeyHashMap.
                     h$
                    ) (Poly%lib!hashmap_t.CKeyHashMap. o1$)
    ))))))))))))))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!cmessage_v.CMessage. self!
      other!
    ))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms lib::cmessage_v::CSingleMessage::view_equal
(assert
 (fuel_bool_default fuel%lib!cmessage_v.impl&%6.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!cmessage_v.impl&%6.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!cmessage_v.CSingleMessage. self!
      other!
     ) (B (let
       ((tmp%%$ (tuple%2./tuple%2 self! other!)))
       (ite
        (and
         (is-lib!cmessage_v.CSingleMessage./Message (%Poly%lib!cmessage_v.CSingleMessage. (tuple%2./tuple%2/0
            (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
         )))
         (is-lib!cmessage_v.CSingleMessage./Message (%Poly%lib!cmessage_v.CSingleMessage. (tuple%2./tuple%2/1
            (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
        ))))
        (let
         ((seqno$ (lib!cmessage_v.CSingleMessage./Message/seqno (%Poly%lib!cmessage_v.CSingleMessage.
             (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
         ))))
         (let
          ((dst$ (lib!cmessage_v.CSingleMessage./Message/dst (%Poly%lib!cmessage_v.CSingleMessage.
              (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
          ))))
          (let
           ((m$ (lib!cmessage_v.CSingleMessage./Message/m (%Poly%lib!cmessage_v.CSingleMessage.
               (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
           ))))
           (let
            ((o0$ (lib!cmessage_v.CSingleMessage./Message/seqno (%Poly%lib!cmessage_v.CSingleMessage.
                (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
            ))))
            (let
             ((o1$ (lib!cmessage_v.CSingleMessage./Message/dst (%Poly%lib!cmessage_v.CSingleMessage.
                 (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
             ))))
             (let
              ((o2$ (lib!cmessage_v.CSingleMessage./Message/m (%Poly%lib!cmessage_v.CSingleMessage.
                  (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
              ))))
              (and
               (and
                (%B (lib!marshal_v.Marshalable.view_equal.? $ (UINT 64) (I seqno$) (I o0$)))
                (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint.
                   dst$
                  ) (Poly%lib!io_t.EndPoint. o1$)
               )))
               (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!cmessage_v.CMessage. (Poly%lib!cmessage_v.CMessage.
                  m$
                 ) (Poly%lib!cmessage_v.CMessage. o2$)
        )))))))))
        (ite
         (and
          (is-lib!cmessage_v.CSingleMessage./Ack (%Poly%lib!cmessage_v.CSingleMessage. (tuple%2./tuple%2/0
             (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
          )))
          (is-lib!cmessage_v.CSingleMessage./Ack (%Poly%lib!cmessage_v.CSingleMessage. (tuple%2./tuple%2/1
             (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
         ))))
         (let
          ((ack_seqno$ (lib!cmessage_v.CSingleMessage./Ack/ack_seqno (%Poly%lib!cmessage_v.CSingleMessage.
              (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
          ))))
          (let
           ((o0$ (lib!cmessage_v.CSingleMessage./Ack/ack_seqno (%Poly%lib!cmessage_v.CSingleMessage.
               (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
           ))))
           (%B (lib!marshal_v.Marshalable.view_equal.? $ (UINT 64) (I ack_seqno$) (I o0$)))
         ))
         (and
          (is-lib!cmessage_v.CSingleMessage./InvalidMessage (%Poly%lib!cmessage_v.CSingleMessage.
            (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
          ))
          (is-lib!cmessage_v.CSingleMessage./InvalidMessage (%Poly%lib!cmessage_v.CSingleMessage.
            (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$)))
    ))))))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!cmessage_v.CSingleMessage.
      self! other!
    ))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms lib::io_t::EndPoint::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%8.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%8.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!io_t.EndPoint. self!) (lib!marshal_v.Marshalable.is_marshalable.?
      $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.) (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>.
       (lib!io_t.EndPoint./EndPoint/id (%Poly%lib!io_t.EndPoint. self!))
    )))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!io_t.EndPoint. self!))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::keys_t::SHTKey::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%10.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%10.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!keys_t.SHTKey. self!) (lib!marshal_v.Marshalable.is_marshalable.?
      $ (UINT 64) (I (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey. self!)))
    ))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!keys_t.SHTKey. self!))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::keys_t::SHTKey::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%10.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%10.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!keys_t.SHTKey. self!) (
      lib!marshal_v.Marshalable.ghost_serialize.? $ (UINT 64) (I (lib!keys_t.SHTKey./SHTKey/ukey
        (%Poly%lib!keys_t.SHTKey. self!)
    ))))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!keys_t.SHTKey. self!))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms lib::io_t::EndPoint::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%8.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%8.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!io_t.EndPoint. self!) (
      lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
      (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!io_t.EndPoint./EndPoint/id (%Poly%lib!io_t.EndPoint.
         self!
    )))))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!io_t.EndPoint. self!))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms lib::marshal_v::impl&%5::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%5.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%5.is_marshalable.)
  (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%tuple%2. T&. T& U&. U&) self!)
     (B (and
       (and
        (%B (lib!marshal_v.Marshalable.is_marshalable.? T&. T& (tuple%2./tuple%2/0 (%Poly%tuple%2.
            self!
        ))))
        (%B (lib!marshal_v.Marshalable.is_marshalable.? U&. U& (tuple%2./tuple%2/1 (%Poly%tuple%2.
            self!
       )))))
       (<= (nClip (Add (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
            T&. T& (tuple%2./tuple%2/0 (%Poly%tuple%2. self!))
           )
          ) (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? U&. U&
            (tuple%2./tuple%2/1 (%Poly%tuple%2. self!))
         )))
        ) (- (uHi SZ) 1)
    ))))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%tuple%2. T&. T& U&. U&)
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::keys_t::KeyRange::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%6.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%6.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
      self!
     ) (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%tuple%2. $ (TYPE%core!option.Option.
        $ (UINT 64)
       ) $ (TYPE%core!option.Option. $ (UINT 64))
      ) (Poly%tuple%2. (tuple%2./tuple%2 (Poly%core!option.Option. (let
          ((tmp%%$ (lib!keys_t.KeyIterator./KeyIterator/k (%Poly%lib!keys_t.KeyIterator. (Poly%lib!keys_t.KeyIterator.
               (lib!keys_t.KeyRange./KeyRange/lo (%Poly%lib!keys_t.KeyRange. self!))
          )))))
          (ite
           (is-core!option.Option./None tmp%%$)
           core!option.Option./None
           (let
            ((x$ (%Poly%lib!keys_t.SHTKey. (core!option.Option./Some/0 (%Poly%core!option.Option.
                 (Poly%core!option.Option. tmp%%$)
            )))))
            (core!option.Option./Some (I (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey.
                (Poly%lib!keys_t.SHTKey. x$)
         )))))))
        ) (Poly%core!option.Option. (let
          ((tmp%%$ (lib!keys_t.KeyIterator./KeyIterator/k (%Poly%lib!keys_t.KeyIterator. (Poly%lib!keys_t.KeyIterator.
               (lib!keys_t.KeyRange./KeyRange/hi (%Poly%lib!keys_t.KeyRange. self!))
          )))))
          (ite
           (is-core!option.Option./None tmp%%$)
           core!option.Option./None
           (let
            ((x$ (%Poly%lib!keys_t.SHTKey. (core!option.Option./Some/0 (%Poly%core!option.Option.
                 (Poly%core!option.Option. tmp%%$)
            )))))
            (core!option.Option./Some (I (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey.
                (Poly%lib!keys_t.SHTKey. x$)
    ))))))))))))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%lib!keys_t.KeyRange. $
       TYPE%lib!keys_t.SHTKey.
      ) self!
    ))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::marshal_v::impl&%5::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%5.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%5.ghost_serialize.)
  (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%tuple%2. T&. T& U&. U&) self!)
     (vstd!seq.Seq.add.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? T&. T&
       (tuple%2./tuple%2/0 (%Poly%tuple%2. self!))
      ) (lib!marshal_v.Marshalable.ghost_serialize.? U&. U& (tuple%2./tuple%2/1 (%Poly%tuple%2.
         self!
    )))))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%tuple%2. T&. T& U&. U&)
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms lib::keys_t::KeyRange::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%6.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%6.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
      self!
     ) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%tuple%2. $ (TYPE%core!option.Option.
        $ (UINT 64)
       ) $ (TYPE%core!option.Option. $ (UINT 64))
      ) (Poly%tuple%2. (tuple%2./tuple%2 (Poly%core!option.Option. (let
          ((tmp%%$ (lib!keys_t.KeyIterator./KeyIterator/k (%Poly%lib!keys_t.KeyIterator. (Poly%lib!keys_t.KeyIterator.
               (lib!keys_t.KeyRange./KeyRange/lo (%Poly%lib!keys_t.KeyRange. self!))
          )))))
          (ite
           (is-core!option.Option./None tmp%%$)
           core!option.Option./None
           (let
            ((x$ (%Poly%lib!keys_t.SHTKey. (core!option.Option./Some/0 (%Poly%core!option.Option.
                 (Poly%core!option.Option. tmp%%$)
            )))))
            (core!option.Option./Some (I (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey.
                (Poly%lib!keys_t.SHTKey. x$)
         )))))))
        ) (Poly%core!option.Option. (let
          ((tmp%%$ (lib!keys_t.KeyIterator./KeyIterator/k (%Poly%lib!keys_t.KeyIterator. (Poly%lib!keys_t.KeyIterator.
               (lib!keys_t.KeyRange./KeyRange/hi (%Poly%lib!keys_t.KeyRange. self!))
          )))))
          (ite
           (is-core!option.Option./None tmp%%$)
           core!option.Option./None
           (let
            ((x$ (%Poly%lib!keys_t.SHTKey. (core!option.Option./Some/0 (%Poly%core!option.Option.
                 (Poly%core!option.Option. tmp%%$)
            )))))
            (core!option.Option./Some (I (lib!keys_t.SHTKey./SHTKey/ukey (%Poly%lib!keys_t.SHTKey.
                (Poly%lib!keys_t.SHTKey. x$)
    ))))))))))))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%lib!keys_t.KeyRange.
       $ TYPE%lib!keys_t.SHTKey.
      ) self!
    ))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms lib::hashmap_t::CKeyKV::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%4.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%4.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!hashmap_t.CKeyKV. self! other!)
     (B (and
       (%B (lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
          (lib!hashmap_t.CKeyKV./CKeyKV/k (%Poly%lib!hashmap_t.CKeyKV. self!))
         ) (Poly%lib!keys_t.SHTKey. (lib!hashmap_t.CKeyKV./CKeyKV/k (%Poly%lib!hashmap_t.CKeyKV.
            other!
       )))))
       (%B (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
         (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!hashmap_t.CKeyKV./CKeyKV/v (%Poly%lib!hashmap_t.CKeyKV.
            self!
          ))
         ) (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!hashmap_t.CKeyKV./CKeyKV/v (%Poly%lib!hashmap_t.CKeyKV.
            other!
    ))))))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ TYPE%lib!hashmap_t.CKeyKV. self!
      other!
    ))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms lib::hashmap_t::CKeyKV::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%4.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%4.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!hashmap_t.CKeyKV. self!)
     (B (and
       (and
        (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
           (lib!hashmap_t.CKeyKV./CKeyKV/k (%Poly%lib!hashmap_t.CKeyKV. self!))
        )))
        (%B (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $
           TYPE%alloc!alloc.Global.
          ) (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!hashmap_t.CKeyKV./CKeyKV/v (%Poly%lib!hashmap_t.CKeyKV.
             self!
       ))))))
       (<= (nClip (Add (nClip (Add 0 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
              $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey. (lib!hashmap_t.CKeyKV./CKeyKV/k
                (%Poly%lib!hashmap_t.CKeyKV. self!)
           )))))
          ) (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%alloc!vec.Vec.
             $ (UINT 8) $ TYPE%alloc!alloc.Global.
            ) (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!hashmap_t.CKeyKV./CKeyKV/v (%Poly%lib!hashmap_t.CKeyKV.
               self!
         ))))))
        ) (- (uHi SZ) 1)
    ))))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!hashmap_t.CKeyKV.
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::hashmap_t::CKeyKV::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%4.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%4.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!hashmap_t.CKeyKV. self!)
     (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.empty.?
        $ (UINT 8)
       ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
         (lib!hashmap_t.CKeyKV./CKeyKV/k (%Poly%lib!hashmap_t.CKeyKV. self!))
       ))
      ) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%alloc!vec.Vec. $ (UINT 8) $
        TYPE%alloc!alloc.Global.
       ) (Poly%alloc!vec.Vec<u8./alloc!alloc.Global.>. (lib!hashmap_t.CKeyKV./CKeyKV/v (%Poly%lib!hashmap_t.CKeyKV.
          self!
    ))))))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!hashmap_t.CKeyKV.
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ TYPE%lib!hashmap_t.CKeyKV.)
)

;; Function-Axioms alloc::vec::Vec::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%4.is_marshalable.)
)
(declare-fun %%lambda%%1 (Dcr Type Dcr Type) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Dcr) (%%hole%%3 Type) (acc$ Poly)
   (x$ Poly)
  ) (!
   (= (%%apply%%1 (%%lambda%%1 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3) acc$ x$) (I (Add
      (%I acc$) (vstd!seq.Seq.len.? %%hole%%2 %%hole%%3 (lib!marshal_v.Marshalable.ghost_serialize.?
        %%hole%%0 %%hole%%1 x$
   )))))
   :pattern ((%%apply%%1 (%%lambda%%1 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3) acc$ x$))
)))
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%4.is_marshalable.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%alloc!vec.Vec. T&. T& $ TYPE%alloc!alloc.Global.)
      self!
     ) (B (and
       (and
        (<= (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& $
            TYPE%alloc!alloc.Global.
           ) self!
          )
         ) (- (uHi SZ) 1)
        )
        (forall ((x$ Poly)) (!
          (=>
           (has_type x$ T&)
           (=>
            (vstd!seq_lib.impl&%0.contains.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
               T&. T& $ TYPE%alloc!alloc.Global.
              ) self!
             ) x$
            )
            (%B (lib!marshal_v.Marshalable.is_marshalable.? T&. T& x$))
          ))
          :pattern ((lib!marshal_v.Marshalable.is_marshalable.? T&. T& x$))
          :qid user_alloc__vec__Vec__is_marshalable_79
       )))
       (<= (Add (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
           $ (UINT SZ) (I (uClip SZ (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
                T&. T& $ TYPE%alloc!alloc.Global.
               ) self!
          )))))
         ) (%I (vstd!seq_lib.impl&%0.fold_left.? T&. T& $ INT (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
             T&. T& $ TYPE%alloc!alloc.Global.
            ) self!
           ) (I 0) (Poly%fun%2. (mk_fun (%%lambda%%1 T&. T& $ (UINT 8))))
         ))
        ) (- (uHi SZ) 1)
    ))))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%alloc!vec.Vec. T&. T&
       $ TYPE%alloc!alloc.Global.
      ) self!
    ))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms alloc::vec::Vec::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%4.ghost_serialize.)
)
(declare-fun %%lambda%%2 (Dcr Type Dcr Type) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Dcr) (%%hole%%3 Type) (acc$ Poly)
   (x$ Poly)
  ) (!
   (= (%%apply%%1 (%%lambda%%2 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3) acc$ x$) (vstd!seq.Seq.add.?
     %%hole%%2 %%hole%%3 acc$ (lib!marshal_v.Marshalable.ghost_serialize.? %%hole%%0 %%hole%%1
      x$
   )))
   :pattern ((%%apply%%1 (%%lambda%%2 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3) acc$ x$))
)))
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%4.ghost_serialize.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%alloc!vec.Vec. T&. T& $ TYPE%alloc!alloc.Global.)
      self!
     ) (vstd!seq.Seq.add.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ (UINT
        SZ
       ) (I (uClip SZ (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
            T&. T& $ TYPE%alloc!alloc.Global.
           ) self!
       ))))
      ) (vstd!seq_lib.impl&%0.fold_left.? T&. T& $ (TYPE%vstd!seq.Seq. $ (UINT 8)) (vstd!view.View.view.?
        $ (TYPE%alloc!vec.Vec. T&. T& $ TYPE%alloc!alloc.Global.) self!
       ) (vstd!seq.Seq.empty.? $ (UINT 8)) (Poly%fun%2. (mk_fun (%%lambda%%2 T&. T& $ (UINT
           8
    )))))))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%alloc!vec.Vec. T&. T&
       $ TYPE%alloc!alloc.Global.
      ) self!
    ))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms lib::marshal_ironsht_specific_v::ckeyhashmap_max_serialized_size
(assert
 (forall ((no%param Poly)) (!
   (=>
    (has_type no%param INT)
    (uInv SZ (lib!marshal_ironsht_specific_v.ckeyhashmap_max_serialized_size.? no%param))
   )
   :pattern ((lib!marshal_ironsht_specific_v.ckeyhashmap_max_serialized_size.? no%param))
   :qid internal_lib!marshal_ironsht_specific_v.ckeyhashmap_max_serialized_size.?_pre_post_definition
)))

;; Function-Axioms lib::hashmap_t::CKeyHashMap::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%2.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%2.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!hashmap_t.CKeyHashMap. self!)
     (B (and
       (and
        (%B (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV.
           $ TYPE%alloc!alloc.Global.
          ) (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
            self!
        ))))
        (lib!hashmap_t.spec_sorted_keys.? (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>.
          (lib!hashmap_t.impl&%0.spec_to_vec.? self!)
       )))
       (<= (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%alloc!vec.Vec.
           $ TYPE%lib!hashmap_t.CKeyKV. $ TYPE%alloc!alloc.Global.
          ) (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
            self!
         )))
        ) (lib!marshal_ironsht_specific_v.ckeyhashmap_max_serialized_size.? (I 0))
    ))))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!hashmap_t.CKeyHashMap.
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::hashmap_t::CKeyHashMap::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%2.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%2.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!hashmap_t.CKeyHashMap. self!)
     (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%alloc!vec.Vec. $ TYPE%lib!hashmap_t.CKeyKV.
       $ TYPE%alloc!alloc.Global.
      ) (Poly%alloc!vec.Vec<lib!hashmap_t.CKeyKV./alloc!alloc.Global.>. (lib!hashmap_t.impl&%0.spec_to_vec.?
        self!
    ))))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!hashmap_t.CKeyHashMap.
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms lib::cmessage_v::CMessage::is_marshalable
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%3.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%3.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!cmessage_v.CMessage. self!)
     (B (ite
       (is-lib!cmessage_v.CMessage./GetRequest (%Poly%lib!cmessage_v.CMessage. self!))
       (let
        ((k$ (lib!cmessage_v.CMessage./GetRequest/k (%Poly%lib!cmessage_v.CMessage. self!))))
        (and
         (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
            k$
         )))
         (<= (nClip (Add 1 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
              $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey. k$)
           )))
          ) (- (uHi SZ) 1)
       )))
       (ite
        (is-lib!cmessage_v.CMessage./SetRequest (%Poly%lib!cmessage_v.CMessage. self!))
        (let
         ((k$ (lib!cmessage_v.CMessage./SetRequest/k (%Poly%lib!cmessage_v.CMessage. self!))))
         (let
          ((v$ (lib!cmessage_v.CMessage./SetRequest/v (%Poly%lib!cmessage_v.CMessage. self!))))
          (and
           (and
            (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
               k$
            )))
            (%B (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec.
                $ (UINT 8) $ TYPE%alloc!alloc.Global.
               )
              ) (Poly%core!option.Option. v$)
           )))
           (<= (nClip (Add (nClip (Add 1 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
                  $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey. k$)
               )))
              ) (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%core!option.Option.
                 $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
                ) (Poly%core!option.Option. v$)
             )))
            ) (- (uHi SZ) 1)
        ))))
        (ite
         (is-lib!cmessage_v.CMessage./Reply (%Poly%lib!cmessage_v.CMessage. self!))
         (let
          ((k$ (lib!cmessage_v.CMessage./Reply/k (%Poly%lib!cmessage_v.CMessage. self!))))
          (let
           ((v$ (lib!cmessage_v.CMessage./Reply/v (%Poly%lib!cmessage_v.CMessage. self!))))
           (and
            (and
             (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
                k$
             )))
             (%B (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec.
                 $ (UINT 8) $ TYPE%alloc!alloc.Global.
                )
               ) (Poly%core!option.Option. v$)
            )))
            (<= (nClip (Add (nClip (Add 1 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
                   $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey. k$)
                )))
               ) (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%core!option.Option.
                  $ (TYPE%alloc!vec.Vec. $ (UINT 8) $ TYPE%alloc!alloc.Global.)
                 ) (Poly%core!option.Option. v$)
              )))
             ) (- (uHi SZ) 1)
         ))))
         (ite
          (is-lib!cmessage_v.CMessage./Redirect (%Poly%lib!cmessage_v.CMessage. self!))
          (let
           ((k$ (lib!cmessage_v.CMessage./Redirect/k (%Poly%lib!cmessage_v.CMessage. self!))))
           (let
            ((id$ (lib!cmessage_v.CMessage./Redirect/id (%Poly%lib!cmessage_v.CMessage. self!))))
            (and
             (and
              (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
                 k$
              )))
              (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint.
                 id$
             ))))
             (<= (nClip (Add (nClip (Add 1 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
                    $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey. k$)
                 )))
                ) (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!io_t.EndPoint.
                  (Poly%lib!io_t.EndPoint. id$)
               )))
              ) (- (uHi SZ) 1)
          ))))
          (ite
           (is-lib!cmessage_v.CMessage./Shard (%Poly%lib!cmessage_v.CMessage. self!))
           (let
            ((kr$ (lib!cmessage_v.CMessage./Shard/kr (%Poly%lib!cmessage_v.CMessage. self!))))
            (let
             ((recipient$ (lib!cmessage_v.CMessage./Shard/recipient (%Poly%lib!cmessage_v.CMessage.
                 self!
             ))))
             (and
              (and
               (%B (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
                 (Poly%lib!keys_t.KeyRange. kr$)
               ))
               (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint.
                  recipient$
              ))))
              (<= (nClip (Add (nClip (Add 1 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
                     $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.) (Poly%lib!keys_t.KeyRange.
                      kr$
                  ))))
                 ) (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!io_t.EndPoint.
                   (Poly%lib!io_t.EndPoint. recipient$)
                )))
               ) (- (uHi SZ) 1)
           ))))
           (let
            ((range$ (lib!cmessage_v.CMessage./Delegate/range (%Poly%lib!cmessage_v.CMessage. self!))))
            (let
             ((h$ (lib!cmessage_v.CMessage./Delegate/h (%Poly%lib!cmessage_v.CMessage. self!))))
             (and
              (and
               (%B (lib!marshal_v.Marshalable.is_marshalable.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
                 (Poly%lib!keys_t.KeyRange. range$)
               ))
               (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!hashmap_t.CKeyHashMap. (
                  Poly%lib!hashmap_t.CKeyHashMap. h$
              ))))
              (<= (nClip (Add (nClip (Add 1 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
                     $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.) (Poly%lib!keys_t.KeyRange.
                      range$
                  ))))
                 ) (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!hashmap_t.CKeyHashMap.
                   (Poly%lib!hashmap_t.CKeyHashMap. h$)
                )))
               ) (- (uHi SZ) 1)
    )))))))))))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!cmessage_v.CMessage.
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::cmessage_v::CMessage::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!marshal_ironsht_specific_v.impl&%3.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_ironsht_specific_v.impl&%3.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CMessage. self!)
     (ite
      (is-lib!cmessage_v.CMessage./GetRequest (%Poly%lib!cmessage_v.CMessage. self!))
      (let
       ((k$ (lib!cmessage_v.CMessage./GetRequest/k (%Poly%lib!cmessage_v.CMessage. self!))))
       (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.push.? $ (UINT 8) (vstd!seq.Seq.empty.?
          $ (UINT 8)
         ) (I 0)
        ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
          k$
      ))))
      (ite
       (is-lib!cmessage_v.CMessage./SetRequest (%Poly%lib!cmessage_v.CMessage. self!))
       (let
        ((k$ (lib!cmessage_v.CMessage./SetRequest/k (%Poly%lib!cmessage_v.CMessage. self!))))
        (let
         ((v$ (lib!cmessage_v.CMessage./SetRequest/v (%Poly%lib!cmessage_v.CMessage. self!))))
         (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.push.? $
            (UINT 8) (vstd!seq.Seq.empty.? $ (UINT 8)) (I 1)
           ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
             k$
           ))
          ) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec.
             $ (UINT 8) $ TYPE%alloc!alloc.Global.
            )
           ) (Poly%core!option.Option. v$)
       ))))
       (ite
        (is-lib!cmessage_v.CMessage./Reply (%Poly%lib!cmessage_v.CMessage. self!))
        (let
         ((k$ (lib!cmessage_v.CMessage./Reply/k (%Poly%lib!cmessage_v.CMessage. self!))))
         (let
          ((v$ (lib!cmessage_v.CMessage./Reply/v (%Poly%lib!cmessage_v.CMessage. self!))))
          (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.push.? $
             (UINT 8) (vstd!seq.Seq.empty.? $ (UINT 8)) (I 2)
            ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
              k$
            ))
           ) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%core!option.Option. $ (TYPE%alloc!vec.Vec.
              $ (UINT 8) $ TYPE%alloc!alloc.Global.
             )
            ) (Poly%core!option.Option. v$)
        ))))
        (ite
         (is-lib!cmessage_v.CMessage./Redirect (%Poly%lib!cmessage_v.CMessage. self!))
         (let
          ((k$ (lib!cmessage_v.CMessage./Redirect/k (%Poly%lib!cmessage_v.CMessage. self!))))
          (let
           ((id$ (lib!cmessage_v.CMessage./Redirect/id (%Poly%lib!cmessage_v.CMessage. self!))))
           (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.push.? $
              (UINT 8) (vstd!seq.Seq.empty.? $ (UINT 8)) (I 3)
             ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!keys_t.SHTKey. (Poly%lib!keys_t.SHTKey.
               k$
             ))
            ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint.
              id$
         )))))
         (ite
          (is-lib!cmessage_v.CMessage./Shard (%Poly%lib!cmessage_v.CMessage. self!))
          (let
           ((kr$ (lib!cmessage_v.CMessage./Shard/kr (%Poly%lib!cmessage_v.CMessage. self!))))
           (let
            ((recipient$ (lib!cmessage_v.CMessage./Shard/recipient (%Poly%lib!cmessage_v.CMessage.
                self!
            ))))
            (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.push.? $
               (UINT 8) (vstd!seq.Seq.empty.? $ (UINT 8)) (I 4)
              ) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
               (Poly%lib!keys_t.KeyRange. kr$)
              )
             ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint.
               recipient$
          )))))
          (let
           ((range$ (lib!cmessage_v.CMessage./Delegate/range (%Poly%lib!cmessage_v.CMessage. self!))))
           (let
            ((h$ (lib!cmessage_v.CMessage./Delegate/h (%Poly%lib!cmessage_v.CMessage. self!))))
            (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.push.? $
               (UINT 8) (vstd!seq.Seq.empty.? $ (UINT 8)) (I 5)
              ) (lib!marshal_v.Marshalable.ghost_serialize.? $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.)
               (Poly%lib!keys_t.KeyRange. range$)
              )
             ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!hashmap_t.CKeyHashMap. (
               Poly%lib!hashmap_t.CKeyHashMap. h$
    )))))))))))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CMessage.
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms lib::cmessage_v::CSingleMessage::is_marshalable
(assert
 (fuel_bool_default fuel%lib!cmessage_v.impl&%6.is_marshalable.)
)
(assert
 (=>
  (fuel_bool fuel%lib!cmessage_v.impl&%6.is_marshalable.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!cmessage_v.CSingleMessage.
      self!
     ) (B (ite
       (is-lib!cmessage_v.CSingleMessage./Message (%Poly%lib!cmessage_v.CSingleMessage. self!))
       (let
        ((seqno$ (lib!cmessage_v.CSingleMessage./Message/seqno (%Poly%lib!cmessage_v.CSingleMessage.
            self!
        ))))
        (let
         ((dst$ (lib!cmessage_v.CSingleMessage./Message/dst (%Poly%lib!cmessage_v.CSingleMessage.
             self!
         ))))
         (let
          ((m$ (lib!cmessage_v.CSingleMessage./Message/m (%Poly%lib!cmessage_v.CSingleMessage.
              self!
          ))))
          (and
           (and
            (and
             (%B (lib!marshal_v.Marshalable.is_marshalable.? $ (UINT 64) (I seqno$)))
             (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint.
                dst$
            ))))
            (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!cmessage_v.CMessage. (Poly%lib!cmessage_v.CMessage.
               m$
           ))))
           (<= (nClip (Add (nClip (Add (nClip (Add 1 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
                    $ (UINT 64) (I seqno$)
                 )))
                ) (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!io_t.EndPoint.
                  (Poly%lib!io_t.EndPoint. dst$)
               )))
              ) (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CMessage.
                (Poly%lib!cmessage_v.CMessage. m$)
             )))
            ) (- (uHi SZ) 1)
       )))))
       (ite
        (is-lib!cmessage_v.CSingleMessage./Ack (%Poly%lib!cmessage_v.CSingleMessage. self!))
        (let
         ((ack_seqno$ (lib!cmessage_v.CSingleMessage./Ack/ack_seqno (%Poly%lib!cmessage_v.CSingleMessage.
             self!
         ))))
         (and
          (%B (lib!marshal_v.Marshalable.is_marshalable.? $ (UINT 64) (I ack_seqno$)))
          (<= (nClip (Add 1 (vstd!seq.Seq.len.? $ (UINT 8) (lib!marshal_v.Marshalable.ghost_serialize.?
               $ (UINT 64) (I ack_seqno$)
            )))
           ) (- (uHi SZ) 1)
        )))
        (<= 1 (- (uHi SZ) 1))
    ))))
    :pattern ((lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!cmessage_v.CSingleMessage.
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.is_marshalable.?_definition
))))

;; Function-Axioms lib::cmessage_v::CSingleMessage::ghost_serialize
(assert
 (fuel_bool_default fuel%lib!cmessage_v.impl&%6.ghost_serialize.)
)
(assert
 (=>
  (fuel_bool fuel%lib!cmessage_v.impl&%6.ghost_serialize.)
  (forall ((self! Poly)) (!
    (= (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CSingleMessage.
      self!
     ) (ite
      (is-lib!cmessage_v.CSingleMessage./Message (%Poly%lib!cmessage_v.CSingleMessage. self!))
      (let
       ((seqno$ (lib!cmessage_v.CSingleMessage./Message/seqno (%Poly%lib!cmessage_v.CSingleMessage.
           self!
       ))))
       (let
        ((dst$ (lib!cmessage_v.CSingleMessage./Message/dst (%Poly%lib!cmessage_v.CSingleMessage.
            self!
        ))))
        (let
         ((m$ (lib!cmessage_v.CSingleMessage./Message/m (%Poly%lib!cmessage_v.CSingleMessage.
             self!
         ))))
         (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.add.? $
            (UINT 8) (vstd!seq.Seq.push.? $ (UINT 8) (vstd!seq.Seq.empty.? $ (UINT 8)) (I 0))
            (lib!marshal_v.Marshalable.ghost_serialize.? $ (UINT 64) (I seqno$))
           ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!io_t.EndPoint. (Poly%lib!io_t.EndPoint.
             dst$
           ))
          ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CMessage. (Poly%lib!cmessage_v.CMessage.
            m$
      ))))))
      (ite
       (is-lib!cmessage_v.CSingleMessage./Ack (%Poly%lib!cmessage_v.CSingleMessage. self!))
       (let
        ((ack_seqno$ (lib!cmessage_v.CSingleMessage./Ack/ack_seqno (%Poly%lib!cmessage_v.CSingleMessage.
            self!
        ))))
        (vstd!seq.Seq.add.? $ (UINT 8) (vstd!seq.Seq.push.? $ (UINT 8) (vstd!seq.Seq.empty.?
           $ (UINT 8)
          ) (I 1)
         ) (lib!marshal_v.Marshalable.ghost_serialize.? $ (UINT 64) (I ack_seqno$))
       ))
       (vstd!seq.Seq.push.? $ (UINT 8) (vstd!seq.Seq.empty.? $ (UINT 8)) (I 2))
    )))
    :pattern ((lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CSingleMessage.
      self!
    ))
    :qid internal_lib!marshal_v.Marshalable.ghost_serialize.?_definition
))))

;; Function-Axioms lib::marshal_v::impl&%1::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%1.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%1.view_equal.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ (UINT SZ) self! other!) (B (= self! other!)))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ (UINT SZ) self! other!))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Function-Axioms alloc::vec::Vec::view_equal
(assert
 (fuel_bool_default fuel%lib!marshal_v.impl&%4.view_equal.)
)
(assert
 (=>
  (fuel_bool fuel%lib!marshal_v.impl&%4.view_equal.)
  (forall ((T&. Dcr) (T& Type) (self! Poly) (other! Poly)) (!
    (= (lib!marshal_v.Marshalable.view_equal.? $ (TYPE%alloc!vec.Vec. T&. T& $ TYPE%alloc!alloc.Global.)
      self! other!
     ) (B (let
       ((s$ (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& $ TYPE%alloc!alloc.Global.)
          self!
       )))
       (let
        ((o$ (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& $ TYPE%alloc!alloc.Global.)
           other!
        )))
        (and
         (= (vstd!seq.Seq.len.? T&. T& s$) (vstd!seq.Seq.len.? T&. T& o$))
         (forall ((i$ Poly)) (!
           (=>
            (has_type i$ INT)
            (=>
             (and
              (<= 0 (%I i$))
              (< (%I i$) (vstd!seq.Seq.len.? T&. T& s$))
             )
             (%B (lib!marshal_v.Marshalable.view_equal.? T&. T& (vstd!seq.Seq.index.? T&. T& s$ i$)
               (vstd!seq.Seq.index.? T&. T& o$ i$)
           ))))
           :pattern ((lib!marshal_v.Marshalable.view_equal.? T&. T& (vstd!seq.Seq.index.? T&. T&
              s$ i$
             ) (vstd!seq.Seq.index.? T&. T& o$ i$)
           ))
           :qid user_alloc__vec__Vec__view_equal_80
    )))))))
    :pattern ((lib!marshal_v.Marshalable.view_equal.? $ (TYPE%alloc!vec.Vec. T&. T& $ TYPE%alloc!alloc.Global.)
      self! other!
    ))
    :qid internal_lib!marshal_v.Marshalable.view_equal.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (REF A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (REF A&.) A&))
   :qid internal_vstd__view__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (BOX A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (BOX A&.) A&))
   :qid internal_vstd__view__impl&__2_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (RC A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (RC A&.) A&))
   :qid internal_vstd__view__impl&__4_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (ARC A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (ARC A&.) A&))
   :qid internal_vstd__view__impl&__6_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ TYPE%tuple%0.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ BOOL)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT 8))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT 64))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT SZ))
)

;; Trait-Impl-Axiom
(assert
 (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type)) (!
   (=>
    (and
     (tr_bound%vstd!view.View. A0&. A0&)
     (tr_bound%vstd!view.View. A1&. A1&)
    )
    (tr_bound%vstd!view.View. $ (TYPE%tuple%2. A0&. A0& A1&. A1&))
   )
   :pattern ((tr_bound%vstd!view.View. $ (TYPE%tuple%2. A0&. A0& A1&. A1&)))
   :qid internal_vstd__view__impl&__38_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (tr_bound%vstd!view.View. $ (TYPE%alloc!vec.Vec. T&. T& A&. A&))
   :pattern ((tr_bound%vstd!view.View. $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)))
   :qid internal_vstd__std_specs__vec__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (tr_bound%vstd!std_specs.vec.VecAdditionalSpecFns. $ (TYPE%alloc!vec.Vec. T&. T& A&.
     A&
    ) T&. T&
   )
   :pattern ((tr_bound%vstd!std_specs.vec.VecAdditionalSpecFns. $ (TYPE%alloc!vec.Vec.
      T&. T& A&. A&
     ) T&. T&
   ))
   :qid internal_vstd__std_specs__vec__impl&__2_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ TYPE%lib!hashmap_t.CKeyHashMap.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ (UINT SZ))
)

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (tr_bound%lib!marshal_v.Marshalable. T&. T&)
    (tr_bound%lib!marshal_v.Marshalable. $ (TYPE%alloc!vec.Vec. T&. T& $ TYPE%alloc!alloc.Global.))
   )
   :pattern ((tr_bound%lib!marshal_v.Marshalable. $ (TYPE%alloc!vec.Vec. T&. T& $ TYPE%alloc!alloc.Global.)))
   :qid internal_lib__marshal_v__impl&__4_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type)) (!
   (=>
    (and
     (tr_bound%lib!marshal_v.Marshalable. T&. T&)
     (tr_bound%lib!marshal_v.Marshalable. U&. U&)
    )
    (tr_bound%lib!marshal_v.Marshalable. $ (TYPE%tuple%2. T&. T& U&. U&))
   )
   :pattern ((tr_bound%lib!marshal_v.Marshalable. $ (TYPE%tuple%2. T&. T& U&. U&)))
   :qid internal_lib__marshal_v__impl&__5_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ TYPE%lib!cmessage_v.CMessage.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ (TYPE%lib!keys_t.KeyRange. $ TYPE%lib!keys_t.SHTKey.))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ TYPE%lib!io_t.EndPoint.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ TYPE%lib!keys_t.SHTKey.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%lib!marshal_v.Marshalable. $ TYPE%lib!cmessage_v.CSingleMessage.)
)

;; Function-Specs vstd::seq_lib::impl&%0::push_distributes_over_add
(declare-fun ens%vstd!seq_lib.impl&%0.push_distributes_over_add. (Dcr Type Poly Poly
  Poly
 ) Bool
)
(assert
 (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly) (elt! Poly)) (!
   (= (ens%vstd!seq_lib.impl&%0.push_distributes_over_add. A&. A& a! b! elt!) (= (vstd!seq.Seq.push.?
      A&. A& (vstd!seq.Seq.add.? A&. A& a! b!) elt!
     ) (vstd!seq.Seq.add.? A&. A& a! (vstd!seq.Seq.push.? A&. A& b! elt!))
   ))
   :pattern ((ens%vstd!seq_lib.impl&%0.push_distributes_over_add. A&. A& a! b! elt!))
   :qid internal_ens__vstd!seq_lib.impl&__0.push_distributes_over_add._definition
)))

;; Broadcast vstd::seq_lib::impl&%0::push_distributes_over_add
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.push_distributes_over_add.)
  (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly) (elt! Poly)) (!
    (=>
     (and
      (has_type a! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type b! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type elt! A&)
     )
     (= (vstd!seq.Seq.push.? A&. A& (vstd!seq.Seq.add.? A&. A& a! b!) elt!) (vstd!seq.Seq.add.?
       A&. A& a! (vstd!seq.Seq.push.? A&. A& b! elt!)
    )))
    :pattern ((vstd!seq.Seq.push.? A&. A& (vstd!seq.Seq.add.? A&. A& a! b!) elt!))
    :pattern ((vstd!seq.Seq.add.? A&. A& a! (vstd!seq.Seq.push.? A&. A& b! elt!)))
    :qid user_vstd__seq_lib__impl&%0__push_distributes_over_add_81
))))

;; Function-Specs vstd::seq_lib::impl&%0::add_empty_right
(declare-fun req%vstd!seq_lib.impl&%0.add_empty_right. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%51 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly)) (!
   (= (req%vstd!seq_lib.impl&%0.add_empty_right. A&. A& a! b!) (=>
     %%global_location_label%%51
     (= (vstd!seq.Seq.len.? A&. A& b!) 0)
   ))
   :pattern ((req%vstd!seq_lib.impl&%0.add_empty_right. A&. A& a! b!))
   :qid internal_req__vstd!seq_lib.impl&__0.add_empty_right._definition
)))
(declare-fun ens%vstd!seq_lib.impl&%0.add_empty_right. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly)) (!
   (= (ens%vstd!seq_lib.impl&%0.add_empty_right. A&. A& a! b!) (= (vstd!seq.Seq.add.? A&.
      A& a! b!
     ) a!
   ))
   :pattern ((ens%vstd!seq_lib.impl&%0.add_empty_right. A&. A& a! b!))
   :qid internal_ens__vstd!seq_lib.impl&__0.add_empty_right._definition
)))

;; Broadcast vstd::seq_lib::impl&%0::add_empty_right
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.add_empty_right.)
  (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly)) (!
    (=>
     (and
      (has_type a! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type b! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (=>
      (= (vstd!seq.Seq.len.? A&. A& b!) 0)
      (= (vstd!seq.Seq.add.? A&. A& a! b!) a!)
    ))
    :pattern ((vstd!seq.Seq.add.? A&. A& a! b!))
    :qid user_vstd__seq_lib__impl&%0__add_empty_right_82
))))

;; Function-Specs vstd::seq_lib::impl&%0::add_empty_left
(declare-fun req%vstd!seq_lib.impl&%0.add_empty_left. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%52 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly)) (!
   (= (req%vstd!seq_lib.impl&%0.add_empty_left. A&. A& a! b!) (=>
     %%global_location_label%%52
     (= (vstd!seq.Seq.len.? A&. A& a!) 0)
   ))
   :pattern ((req%vstd!seq_lib.impl&%0.add_empty_left. A&. A& a! b!))
   :qid internal_req__vstd!seq_lib.impl&__0.add_empty_left._definition
)))
(declare-fun ens%vstd!seq_lib.impl&%0.add_empty_left. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly)) (!
   (= (ens%vstd!seq_lib.impl&%0.add_empty_left. A&. A& a! b!) (= (vstd!seq.Seq.add.? A&.
      A& a! b!
     ) b!
   ))
   :pattern ((ens%vstd!seq_lib.impl&%0.add_empty_left. A&. A& a! b!))
   :qid internal_ens__vstd!seq_lib.impl&__0.add_empty_left._definition
)))

;; Broadcast vstd::seq_lib::impl&%0::add_empty_left
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.add_empty_left.)
  (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly)) (!
    (=>
     (and
      (has_type a! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type b! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (=>
      (= (vstd!seq.Seq.len.? A&. A& a!) 0)
      (= (vstd!seq.Seq.add.? A&. A& a! b!) b!)
    ))
    :pattern ((vstd!seq.Seq.add.? A&. A& a! b!))
    :qid user_vstd__seq_lib__impl&%0__add_empty_left_83
))))

;; Function-Specs lib::net_sht_v::sht_marshal_data_injective
(declare-fun req%lib!net_sht_v.sht_marshal_data_injective. (lib!cmessage_v.CSingleMessage.
  lib!cmessage_v.CSingleMessage.
 ) Bool
)
(declare-const %%global_location_label%%53 Bool)
(declare-const %%global_location_label%%54 Bool)
(declare-const %%global_location_label%%55 Bool)
(assert
 (forall ((a! lib!cmessage_v.CSingleMessage.) (b! lib!cmessage_v.CSingleMessage.))
  (!
   (= (req%lib!net_sht_v.sht_marshal_data_injective. a! b!) (and
     (=>
      %%global_location_label%%53
      (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!cmessage_v.CSingleMessage.
        (Poly%lib!cmessage_v.CSingleMessage. a!)
     )))
     (=>
      %%global_location_label%%54
      (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!cmessage_v.CSingleMessage.
        (Poly%lib!cmessage_v.CSingleMessage. b!)
     )))
     (=>
      %%global_location_label%%55
      (= (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CSingleMessage.
        (Poly%lib!cmessage_v.CSingleMessage. a!)
       ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CSingleMessage.
        (Poly%lib!cmessage_v.CSingleMessage. b!)
   )))))
   :pattern ((req%lib!net_sht_v.sht_marshal_data_injective. a! b!))
   :qid internal_req__lib!net_sht_v.sht_marshal_data_injective._definition
)))
(declare-fun ens%lib!net_sht_v.sht_marshal_data_injective. (lib!cmessage_v.CSingleMessage.
  lib!cmessage_v.CSingleMessage.
 ) Bool
)
(assert
 (forall ((a! lib!cmessage_v.CSingleMessage.) (b! lib!cmessage_v.CSingleMessage.))
  (!
   (= (ens%lib!net_sht_v.sht_marshal_data_injective. a! b!) (= (lib!cmessage_v.impl&%2.view.?
      (Poly%lib!cmessage_v.CSingleMessage. a!)
     ) (lib!cmessage_v.impl&%2.view.? (Poly%lib!cmessage_v.CSingleMessage. b!))
   ))
   :pattern ((ens%lib!net_sht_v.sht_marshal_data_injective. a! b!))
   :qid internal_ens__lib!net_sht_v.sht_marshal_data_injective._definition
)))

;; Function-Def lib::net_sht_v::sht_marshal_data_injective
;; net_sht_v.rs:78:1: 78:80 (#0)

 (declare-const a! lib!cmessage_v.CSingleMessage.)
 (declare-const b! lib!cmessage_v.CSingleMessage.)
 (declare-const tmp%1 Bool)
 (assert
  fuel_defaults
 )
 (assert
  (has_type (Poly%lib!cmessage_v.CSingleMessage. a!) TYPE%lib!cmessage_v.CSingleMessage.)
 )
 (assert
  (has_type (Poly%lib!cmessage_v.CSingleMessage. b!) TYPE%lib!cmessage_v.CSingleMessage.)
 )
 (assert
  (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!cmessage_v.CSingleMessage.
    (Poly%lib!cmessage_v.CSingleMessage. a!)
 )))
 (assert
  (%B (lib!marshal_v.Marshalable.is_marshalable.? $ TYPE%lib!cmessage_v.CSingleMessage.
    (Poly%lib!cmessage_v.CSingleMessage. b!)
 )))
 (assert
  (= (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CSingleMessage.
    (Poly%lib!cmessage_v.CSingleMessage. a!)
   ) (lib!marshal_v.Marshalable.ghost_serialize.? $ TYPE%lib!cmessage_v.CSingleMessage.
    (Poly%lib!cmessage_v.CSingleMessage. b!)
 )))
 ;; precondition not satisfied
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%2 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (and
     (=>
      %%location_label%%0
      (req%lib!marshal_v.Marshalable.lemma_serialize_injective. $ TYPE%lib!cmessage_v.CSingleMessage.
       (Poly%lib!cmessage_v.CSingleMessage. a!) (Poly%lib!cmessage_v.CSingleMessage. b!)
     ))
     (=>
      (ens%lib!marshal_v.Marshalable.lemma_serialize_injective. $ TYPE%lib!cmessage_v.CSingleMessage.
       (Poly%lib!cmessage_v.CSingleMessage. a!) (Poly%lib!cmessage_v.CSingleMessage. b!)
      )
      (=>
       (= tmp%1 (= (lib!cmessage_v.impl&%2.view.? (Poly%lib!cmessage_v.CSingleMessage. a!))
         (lib!cmessage_v.impl&%2.view.? (Poly%lib!cmessage_v.CSingleMessage. b!))
       ))
       (and
        (=>
         %%location_label%%1
         tmp%1
        )
        (=>
         tmp%1
         (=>
          %%location_label%%2
          (= (lib!cmessage_v.impl&%2.view.? (Poly%lib!cmessage_v.CSingleMessage. a!)) (lib!cmessage_v.impl&%2.view.?
            (Poly%lib!cmessage_v.CSingleMessage. b!)
 )))))))))))
 (assert
  %%query%%
 )
 (check-sat)

