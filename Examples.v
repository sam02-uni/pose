From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From POSE Require Import Syntax.
From POSE Require Import SemanticsTypes.
From POSE Require Import SemanticsAux.
From POSE Require Import Interp.
From POSE Require Import Parse.
From POSE Require Import Prettyprint.
From POSE Require Import Smt.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(***************************** Examples ***************************)

(* Computes 2 + 3 *)

Compute parse "class Object {  } (2 + 3)".

Definition e1 : s_expr := s_expr_add (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 2)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 3)))).

Definition P1 : s_prg := s_prg_l [CObject] e1.

Compute prg_to_str P1.

Compute step_to_str (step_at P1 0).
Compute step_to_str (step_at P1 1).
Compute step_to_str (step_at P1 2).

(* Computes 2 + 3 via method call *)

Compute parse "class Object {  } class Class1 extends Object {  int m(int x) := (2 + x); } (new Class1.m[3])".

Definition C2_1 : s_dc_c :=
  s_dc_c_l "Class1" "Object" []
  [s_dc_m_l s_ty_int "m" (s_dc_v_l s_ty_int "x")
   (s_expr_add (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 2)))) (s_expr_var "x"))].

Definition e2 : s_expr := s_expr_invoke (s_expr_new "Class1") "m" (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 3)))).

Definition P2 : s_prg := s_prg_l [CObject ; C2_1] e2.

Compute prg_to_str P2.

Compute step_to_str (step_at P2 0).
Compute step_to_str (step_at P2 1).
Compute step_to_str (step_at P2 2).
Compute step_to_str (step_at P2 3).
Compute step_to_str (step_at P2 4).

(* Computes let x := X0 in if x = 2 then true else false *)

Compute parse "class Object {  } let x := X0 in if (x = 2) then true else false".

Definition e3 : s_expr := s_expr_let "x" (s_expr_val (s_val_prim_c (s_prim_c_symb (s_symb_expr 0)))) (s_expr_if (s_expr_eq (s_expr_var "x") (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 2))))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)))).

Definition P3 : s_prg := s_prg_l [CObject] e3.

Compute prg_to_str P3.

Compute step_to_str (step_at P3 0).
Compute step_to_str (step_at P3 1).
Compute step_to_str (step_at P3 2).
Compute step_to_str (step_at P3 3).
Compute step_to_str (step_at P3 4).

(* Computes Y0.f; Class1 has field f. *)

Compute parse "class Object {  } class Class1 extends Object { int f; } (Y0.f)".

Definition e4 : s_expr := s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) "f".

Definition C4_1 : s_dc_c :=
  s_dc_c_l "Class1" "Object"
  [s_dc_v_l s_ty_int "f"] [].

Definition P4 : s_prg := s_prg_l [CObject ; C4_1] e4.

Compute prg_to_str P4.

Compute step_to_str (step_at P4 0).
Compute step_to_str (step_at P4 1).
Compute step_to_str (step_at P4 2).

(* Computes Y0.f + Y0.g; Class1 has field f and Class2 <: Class1 has field g. *)

Compute parse "class Object {  } class Class1 extends Object { int f; } class Class2 extends Class1 { int g; } let x := (Y0.f) in (x + (Y0.g))".

Definition e5 : s_expr := s_expr_let "x" (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) "f") (s_expr_add (s_expr_var "x") (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) "g")).

Definition C5_1 : s_dc_c :=
  s_dc_c_l "Class1" "Object"
  [s_dc_v_l s_ty_int "f"] [].

Definition C5_2 : s_dc_c :=
  s_dc_c_l "Class2" "Class1"
  [s_dc_v_l s_ty_int "g"] [].

Definition P5 : s_prg := s_prg_l [CObject ; C5_1 ; C5_2] e5.

Compute prg_to_str P5.

Compute step_to_str (step_at P5 0).
Compute step_to_str (step_at P5 1).
Compute step_to_str (step_at P5 2).
Compute step_to_str (step_at P5 3).
Compute step_to_str (step_at P5 4).
Compute step_to_str (step_at P5 5).

(* Computes Y0.f + Y1.f; Class1 has field f. *)

Compute parse "class Object {  } class Class1 extends Object { int f; } let x := (Y0.f) in (x + (Y1.f))".

Definition e6 : s_expr := s_expr_let "x" (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) "f") (s_expr_add (s_expr_var "x") (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 1)))) "f")).

Definition C6_1 : s_dc_c :=
  s_dc_c_l "Class1" "Object"
  [s_dc_v_l s_ty_int "f"] [].

Definition P6 : s_prg := s_prg_l [CObject ; C6_1] e6.

Compute prg_to_str P6.

Compute step_to_str (step_at P6 0).
Compute step_to_str (step_at P6 1).
Compute step_to_str (step_at P6 2).
Compute step_to_str (step_at P6 3).
Compute step_to_str (step_at P6 4).
Compute step_to_str (step_at P6 5).

(* Computes Y0.f + (Y1.f + Y2.f); Class1 has field f. *)

Compute parse "class Object {  } class Class1 extends Object { int f; } let x := (Y0.f) in let y := (Y1.f) in (x + (y + (Y2.f)))".

Definition e7 : s_expr := s_expr_let "x" (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) "f")  (s_expr_let "y" (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 1)))) "f") (s_expr_add (s_expr_var "x") (s_expr_add (s_expr_var "y") (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 2)))) "f")))).

Definition C7_1 : s_dc_c :=
  s_dc_c_l "Class1" "Object"
  [s_dc_v_l s_ty_int "f"] [].

Definition P7 : s_prg := s_prg_l [CObject ; C7_1] e7.

Compute prg_to_str P7.

Compute step_to_str (step_at P7 0).
Compute step_to_str (step_at P7 1).
Compute step_to_str (step_at P7 2).
Compute step_to_str (step_at P7 3).
Compute step_to_str (step_at P7 4).
Compute step_to_str (step_at P7 5).
Compute step_to_str (step_at P7 6).
Compute step_to_str (step_at P7 7).
Compute step_to_str (step_at P7 8).

(* Computes Y0.f.g; Class1 has field f, Class2 has field g. *)

Compute parse "class Object {  } class Class1 extends Object { Class2 f; } class Class2 extends Object { int g; } ((Y0.f).g)".

Definition e8 : s_expr := s_expr_getfield (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) "f") "g".

Definition C8_1 : s_dc_c :=
  s_dc_c_l "Class1" "Object"
  [s_dc_v_l (s_ty_class "Class2") "f"] [].

Definition C8_2 : s_dc_c :=
  s_dc_c_l "Class2" "Object"
  [s_dc_v_l s_ty_int "g"] [].

Definition P8 : s_prg := s_prg_l [CObject ; C8_1 ; C8_2] e8.

Compute prg_to_str P8.

Compute step_to_str (step_at P8 0).
Compute step_to_str (step_at P8 1).
Compute step_to_str (step_at P8 2).
Compute step_to_str (step_at P8 3).

(* Computes Y0.f.g; Class1 has fields f and g. *)

Compute parse "class Object {  } class Class1 extends Object { Class1 f; int g; } ((Y0.f).g)".

Definition e9 : s_expr := s_expr_getfield (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) "f") "g".

Definition C9_1 : s_dc_c :=
  s_dc_c_l "Class1" "Object"
  [s_dc_v_l (s_ty_class "Class1") "f" ; s_dc_v_l s_ty_int "g"] [].

Definition P9 : s_prg := s_prg_l [CObject ; C9_1] e9.

Compute prg_to_str P9.

Compute step_to_str (step_at P9 0).
Compute step_to_str (step_at P9 1).
Compute step_to_str (step_at P9 2).
Compute step_to_str (step_at P9 3).

(* Computes Y1.f := Y0.f, with Y1.f evaluated after Y0.f; Class1 has field f. *)

Compute parse "class Object {  } class Class1 extends Object { Class1 f; } let x := (Y0.f) in (Y1.f := x)".

Definition e10 : s_expr := s_expr_let "x" (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) "f") (s_expr_putfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 1)))) "f"  (s_expr_var "x")).

Definition C10_1 : s_dc_c :=
  s_dc_c_l "Class1" "Object"
  [s_dc_v_l (s_ty_class "Class1") "f"] [].

Definition P10 : s_prg := s_prg_l [CObject ; C10_1] e10.

Compute prg_to_str P10.

Compute step_to_str (step_at P10 0).
Compute step_to_str (step_at P10 1).
Compute step_to_str (step_at P10 2).
Compute step_to_str (step_at P10 3).
Compute step_to_str (step_at P10 4).

(* Computes Y0.f.f := Y1.f, with Y1.f evaluated before Y0.f (so Y0.f contains an ite); Class1 has field f. *)

Compute parse "class Object {  } class Class1 extends Object { Class1 f; } let x := (Y1.f) in let y := (Y0.f) in (y.f := x)".

Definition e11 : s_expr := s_expr_let "x" (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 1)))) "f") (s_expr_let "y" (s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) "f") (s_expr_putfield (s_expr_var "y") "f"  (s_expr_var "x"))).

Definition C11_1 : s_dc_c :=
  s_dc_c_l "Class1" "Object"
  [s_dc_v_l (s_ty_class "Class1") "f"] [].

Definition P11 : s_prg := s_prg_l [CObject ; C11_1] e11.

Compute prg_to_str P11.

Compute step_to_str (step_at P11 0).
Compute step_to_str (step_at P11 1).
Compute step_to_str (step_at P11 2).
Compute step_to_str (step_at P11 3).
Compute step_to_str (step_at P11 4).
Compute step_to_str (step_at P11 5).
Compute step_to_str (step_at P11 6).

(* Figure 1a from paper *)

Compute parse "class Object { } class Void extends Object { } class Container extends Object { Object data; Void swap(Container c) := if (c = null) then new Void else let e := (this.data) in let foo := (this.data := (c.data)) in let baz := (c.data := e) in new Void; } let y0 := Y0 in let y1 := Y1 in (y0.swap[y1])". 

Definition e12 : s_expr :=
  (s_expr_let "y0" (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0))))
     (s_expr_let "y1" (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 1))))
        (s_expr_invoke (s_expr_var "y0") "swap" (s_expr_var "y1")))).

Definition CVoid : s_dc_c :=
  s_dc_c_l "Void" "Object" [] [].
  
Definition C12_1 : s_dc_c :=
  s_dc_c_l "Container" "Object"
    [s_dc_v_l (s_ty_class "Object") "data"]
    [s_dc_m_l (s_ty_class "Void") "swap"
       (s_dc_v_l (s_ty_class "Container") "c")
       (s_expr_if (s_expr_eq (s_expr_var "c") (s_expr_val (s_val_ref_c s_ref_c_null))) (s_expr_new "Void")
          (s_expr_let "e" (s_expr_getfield (s_expr_var "this") "data")
             (s_expr_let "foo" (s_expr_putfield (s_expr_var "this") "data" (s_expr_getfield (s_expr_var "c") "data"))
                (s_expr_let "baz" (s_expr_putfield (s_expr_var "c") "data" (s_expr_var "e")) (s_expr_new "Void")))))].

Definition P12 : s_prg := s_prg_l [CObject ; CVoid ; C12_1] e12.

Compute prg_to_str P12.

Compute step_to_str (step_at P12 0).
Compute step_to_str (step_at P12 1).
Compute step_to_str (step_at P12 2).
Compute step_to_str (step_at P12 3).
Compute step_to_str (step_at P12 4).
Compute step_to_str (step_at P12 5).
Compute step_to_str (step_at P12 6).
Compute step_to_str (step_at P12 7).
Compute step_to_str (step_at P12 8).
Compute step_to_str (step_at P12 9).
Compute step_to_str (step_at P12 10).
Compute step_to_str (step_at P12 11).
Compute step_to_str (step_at P12 12).
Compute step_to_str (step_at P12 13).
Compute step_to_str (step_at P12 14).

(* Figure 1b from the paper *)

Compute parse "class Object { } class Void extends Object { } class Node extends Object { int val; Node c0; Node c1; Node c2; int sum(Void foo) := let s1 := (this.val) in let s2 := (s1 + ((this.c0).val)) in let s3 := (s2 + ((this.c1).val)) in let s4 := (s3 + ((this.c2).val)) in s4; } let y := Y0 in (y.sum[new Void])".

Definition e13 : s_expr := s_expr_let "y" (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0)))) (s_expr_invoke (s_expr_var "y") "sum" (s_expr_new "Void")).

Definition C13_1 : s_dc_c :=
  s_dc_c_l "Node" "Object"
    [s_dc_v_l s_ty_int "val"; s_dc_v_l (s_ty_class "Node") "c0"; s_dc_v_l (s_ty_class "Node") "c1"; s_dc_v_l (s_ty_class "Node") "c2"]
    [s_dc_m_l s_ty_int "sum" (s_dc_v_l (s_ty_class "Void") "foo")
       (s_expr_let "s1" (s_expr_getfield (s_expr_var "this") "val")
          (s_expr_let "s2" (s_expr_add (s_expr_var "s1") (s_expr_getfield (s_expr_getfield (s_expr_var "this") "c0") "val"))
             (s_expr_let "s3" (s_expr_add (s_expr_var "s2") (s_expr_getfield (s_expr_getfield (s_expr_var "this") "c1") "val"))
                (s_expr_let "s4" (s_expr_add (s_expr_var "s3") (s_expr_getfield (s_expr_getfield (s_expr_var "this") "c2") "val"))
                   (s_expr_var "s4")))))].

Definition P13 : s_prg := s_prg_l [CObject ; CVoid ; C13_1] e13.

Compute prg_to_str P13.

Compute step_to_str (step_at P13 0).
Compute step_to_str (step_at P13 1).
Compute step_to_str (step_at P13 2).
Compute step_to_str (step_at P13 3).
Compute step_to_str (step_at P13 4).
Compute step_to_str (step_at P13 5).
Compute step_to_str (step_at P13 6).
Compute step_to_str (step_at P13 7).
Compute step_to_str (step_at P13 8).
Compute step_to_str (step_at P13 9).
Compute step_to_str (step_at P13 10).
Compute step_to_str (step_at P13 11).
Compute step_to_str (step_at P13 12).
Compute step_to_str (step_at P13 13).
Compute step_to_str (step_at P13 14).
Compute step_to_str (step_at P13 15).
Compute step_to_str (step_at P13 16).
Compute step_to_str (step_at P13 17).
Compute step_to_str (step_at P13 18).

(* Figure 1c from the paper *)

Compute parse "class Object { } class Void extends Object { } class LoopFrame extends Object { Node n; int i; } class Node extends Object { int max; Node next; bool hasNullWithin(Void foo1) := let f := new LoopFrame in let foo2 := (f.n := (this.next)) in let foo3 := (f.i := 1) in let fPost := (this.doLoop[f]) in ((fPost.n) = null); LoopFrame doLoop(LoopFrame f) := if ((f.n) = null) then f else if ((this.max) < (f.i)) then f else let foo4 := (f.n := ((f.n).next)) in let foo5 := (f.i := ((f.i) + 1)) in (this.doLoop[f]); } let y := Y0 in let foo6 := (y.max := 4) in (y.hasNullWithin[new Void])".

Definition e14 : s_expr :=
  s_expr_let "y" (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0))))
    (s_expr_let "foo6" (s_expr_putfield (s_expr_var "y") "max" (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 4)))))
       (s_expr_invoke (s_expr_var "y") "hasNullWithin" (s_expr_new "Void"))).

Definition C14_1 : s_dc_c := s_dc_c_l "LoopFrame" "Object" [s_dc_v_l (s_ty_class "Node") "n"; s_dc_v_l s_ty_int "i"] [].

Definition C14_2 : s_dc_c :=
  s_dc_c_l "Node" "Object" [s_dc_v_l s_ty_int "max"; s_dc_v_l (s_ty_class "Node") "next"]
    [s_dc_m_l s_ty_bool "hasNullWithin" (s_dc_v_l (s_ty_class "Void") "foo1")
       (s_expr_let "f" (s_expr_new "LoopFrame")
          (s_expr_let "foo2" (s_expr_putfield (s_expr_var "f") "n" (s_expr_getfield (s_expr_var "this") "next"))
             (s_expr_let "foo3" (s_expr_putfield (s_expr_var "f") "i" (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 1)))))
                (s_expr_let "fPost" (s_expr_invoke (s_expr_var "this") "doLoop" (s_expr_var "f"))
                   (s_expr_eq (s_expr_getfield (s_expr_var "fPost") "n") (s_expr_val (s_val_ref_c s_ref_c_null)))))));
     s_dc_m_l (s_ty_class "LoopFrame") "doLoop" (s_dc_v_l (s_ty_class "LoopFrame") "f")
       (s_expr_if (s_expr_eq (s_expr_getfield (s_expr_var "f") "n") (s_expr_val (s_val_ref_c s_ref_c_null))) (s_expr_var "f")
          (s_expr_if (s_expr_lt (s_expr_getfield (s_expr_var "this") "max") (s_expr_getfield (s_expr_var "f") "i")) (s_expr_var "f")
             (s_expr_let "foo4" (s_expr_putfield (s_expr_var "f") "n" (s_expr_getfield (s_expr_getfield (s_expr_var "f") "n") "next"))
                (s_expr_let "foo5"
                   (s_expr_putfield (s_expr_var "f") "i" (s_expr_add (s_expr_getfield (s_expr_var "f") "i") (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 1))))))
                   (s_expr_invoke (s_expr_var "this") "doLoop" (s_expr_var "f"))))))].

Definition P14 : s_prg := s_prg_l [CObject ; CVoid ; C14_1 ; C14_2] e14.

Compute prg_to_str P14.

Compute step_to_str (step_at P14 0).
Compute step_to_str (step_at P14 1).
Compute step_to_str (step_at P14 2).
Compute step_to_str (step_at P14 3).
Compute step_to_str (step_at P14 4).
Compute step_to_str (step_at P14 5).
Compute step_to_str (step_at P14 6).
Compute step_to_str (step_at P14 7).
Compute step_to_str (step_at P14 8).
Compute step_to_str (step_at P14 9).
Compute step_to_str (step_at P14 10).
Compute step_to_str (step_at P14 11).
Compute step_to_str (step_at P14 12).
Compute step_to_str (step_at P14 13).
Compute step_to_str (step_at P14 14).
Compute step_to_str (step_at P14 15).
Compute step_to_str (step_at P14 16).
Compute step_to_str (step_at P14 17).
Compute step_to_str (step_at P14 18).
Compute step_to_str (step_at P14 19).
Compute step_to_str (step_at P14 20).
Compute step_to_str (step_at P14 21).
Compute step_to_str (step_at P14 22).
Compute step_to_str (step_at P14 23).
Compute step_to_str (step_at P14 24).
Compute step_to_str (step_at P14 25).
Compute step_to_str (step_at P14 26).
Compute step_to_str (step_at P14 27).
Compute step_to_str (step_at P14 28).
Compute step_to_str (step_at P14 29).
Compute step_to_str (step_at P14 30).
Compute step_to_str (step_at P14 31).
Compute step_to_str (step_at P14 32).
Compute step_to_str (step_at P14 33).
Compute step_to_str (step_at P14 34).
Compute step_to_str (step_at P14 35).
Compute step_to_str (step_at P14 36).
Compute step_to_str (step_at P14 37).
Compute step_to_str (step_at P14 38).
Compute step_to_str (step_at P14 39).
Compute step_to_str (step_at P14 40).
Compute step_to_str (step_at P14 41).
Compute step_to_str (step_at P14 42).
Compute step_to_str (step_at P14 43).
Compute step_to_str (step_at P14 44).
Compute step_to_str (step_at P14 45).
Compute step_to_str (step_at P14 46).
Compute step_to_str (step_at P14 47).
Compute step_to_str (step_at P14 48).
Compute step_to_str (step_at P14 49).
Compute step_to_str (step_at P14 50).
Compute step_to_str (step_at P14 51).
Compute step_to_str (step_at P14 52).
Compute step_to_str (step_at P14 53).
Compute step_to_str (step_at P14 54).
Compute step_to_str (step_at P14 55).
Compute step_to_str (step_at P14 56).
Compute step_to_str (step_at P14 57).
Compute step_to_str (step_at P14 58).
Compute step_to_str (step_at P14 59).
Compute step_to_str (step_at P14 60).
Compute step_to_str (step_at P14 61).
Compute step_to_str (step_at P14 62).
Compute step_to_str (step_at P14 63).
Compute step_to_str (step_at P14 64).
Compute step_to_str (step_at P14 65).
Compute step_to_str (step_at P14 66).
Compute step_to_str (step_at P14 67).
Compute step_to_str (step_at P14 68).
Compute step_to_str (step_at P14 69).
Compute step_to_str (step_at P14 70).
Compute step_to_str (step_at P14 71).
Compute step_to_str (step_at P14 72).
Compute step_to_str (step_at P14 73).
Compute step_to_str (step_at P14 74).
Compute step_to_str (step_at P14 75).
Compute step_to_str (step_at P14 76).
Compute step_to_str (step_at P14 77).
Compute step_to_str (step_at P14 78).
Compute step_to_str (step_at P14 79).
Compute step_to_str (step_at P14 80).
Compute step_to_str (step_at P14 81).
Compute step_to_str (step_at P14 82).
Compute step_to_str (step_at P14 83).
Compute step_to_str (step_at P14 84).
Compute step_to_str (step_at P14 85).
Compute step_to_str (step_at P14 86).
Compute step_to_str (step_at P14 87).
Compute step_to_str (step_at P14 88).

(* Check for correctness... *)
Compute parse "class Object { } class N extends Object { N n; } let a := Y0 in let b := (a.n) in let foo := (a.n := null) in let c := (b.n) in c".

Definition P15 : s_prg :=
  s_prg_l [s_dc_c_l "Object" "" [] []; s_dc_c_l "N" "Object" [s_dc_v_l (s_ty_class "N") "n"] []]
    (s_expr_let "a" (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0))))
       (s_expr_let "b" (s_expr_getfield (s_expr_var "a") "n")
          (s_expr_let "foo" (s_expr_putfield (s_expr_var "a") "n" (s_expr_val (s_val_ref_c s_ref_c_null)))
             (s_expr_let "c" (s_expr_getfield (s_expr_var "b") "n") (s_expr_var "c"))))).

Compute prg_to_str P15.

Compute step_to_str (step_at P15 0).
Compute step_to_str (step_at P15 1).
Compute step_to_str (step_at P15 2).
Compute step_to_str (step_at P15 3).
Compute step_to_str (step_at P15 4).
Compute step_to_str (step_at P15 5).
Compute step_to_str (step_at P15 6).
Compute step_to_str (step_at P15 7).
Compute step_to_str (step_at P15 8).

Compute (step_at P15 7).

(* Check for correctness... *)
Compute parse "class Object { } class N extends Object { N n; } let a := Y0 in let b := Y1 in let foo := (a.n := null) in let c := (b.n) in c".

Definition P16 : s_prg :=
  s_prg_l [s_dc_c_l "Object" "" [] []; s_dc_c_l "N" "Object" [s_dc_v_l (s_ty_class "N") "n"] []]
    (s_expr_let "a" (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 0))))
       (s_expr_let "b" (s_expr_val (s_val_ref_c (s_ref_c_symb (s_symb_expr 1))))
          (s_expr_let "foo" (s_expr_putfield (s_expr_var "a") "n" (s_expr_val (s_val_ref_c s_ref_c_null)))
             (s_expr_let "c" (s_expr_getfield (s_expr_var "b") "n") (s_expr_var "c"))))).

Compute prg_to_str P16.

Compute step_to_str (step_at P16 0).
Compute step_to_str (step_at P16 1).
Compute step_to_str (step_at P16 2).
Compute step_to_str (step_at P16 3).
Compute step_to_str (step_at P16 4).
Compute step_to_str (step_at P16 5).
Compute step_to_str (step_at P16 6).
Compute step_to_str (step_at P16 7).
