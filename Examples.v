From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From BOSE Require Import Syntax.
From BOSE Require Import SemanticsTypes.
From BOSE Require Import SemanticsAux.
From BOSE Require Import Interp.
From BOSE Require Import Parse.
From BOSE Require Import Prettyprint.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(***************************** Examples ***************************)

(* An example to check that merging heaps in getfield works:
   let o1 <> o1' and o2 <> o2', the start heap:

   H  = [L1 -> o1 ; L2 -> o2]

   the heaps to merge:

   H1' = [L1 -> o1' ; L2 -> o2 ; Y0 -> o3']
   H2' = [L1 -> o1  ; L2 -> o2'; Y1 -> o4' ; Y0 -> o3']

   o1, o1' : A
   o2, o2' : B
   o3' : C
   o4' : D

   and the merge result:

   H' = [L1 -> o1' ; L2 -> o2' ; Y0 -> o3' ; Y1 -> o4']

Example example_merge_getfield_ok : forall o1 o1' o2 o2' o3' o4' M1' M2' M' M T1' T2' T' T R1' R2' R' R K1' K2' K' K, 
o1 <> o1' -> o2 <> o2' -> 
M1' = [o1' ; o2 ; o3'] -> 
M2' = [o1 ; o2' ; o4' ; o3'] -> 
M' = [o1' ; o2' ; o3' ; o4'] -> 
M = cons o1 (cons o2 nil) -> 
T1' = ["A" ; "B" ; "C"] -> 
T2' = ["A" ; "B" ; "D" ; "C"] -> 
T' = ["A" ; "B" ; "C" ; "D"] -> 
R1' (s_symb_expr 0) = Some 2 -> (forall s, s <> (s_symb_expr 0) -> R1' s = None) -> 
R2' (s_symb_expr 0) = Some 3 -> R2' (s_symb_expr 1) = Some 2 -> (forall s, s <> (s_symb_expr 0) -> s <> (s_symb_expr 1) -> R2' s = None) ->
R' (s_symb_expr 0) = Some 2 -> R' (s_symb_expr 1) = Some 3 -> forall s, s <> (s_symb_expr 0) -> s <> (s_symb_expr 1) -> R' s = None -> 
K1' = [None ; None ; Some (s_symb_expr 0)] ->
K2' = [None ; None :: Some (s_symb_expr 1) ; Some (s_symb_expr 0)] ->
K' = [None ; None :: Some (s_symb_expr 0) ; Some (s_symb_expr 1)] ->
merge1 (M1', T1', R1', K1') (M2', T2', R2', K2') (M', T', R', K') (M, T, R, K).
Proof.
  intros. unfold merge1. unfold memory. unfold obj_classes. unfold resolutions. unfold resolutions_inv. rewrite H1. rewrite H2. rewrite H3. rewrite H4. 
  unfold Datatypes.length. rewrite H5. rewrite H6. rewrite H7. rewrite H18. rewrite H19. rewrite H20. unfold merge1_fp. unfold tl. right. right. split.
  reflexivity. split. reflexivity. right. left. split. reflexivity. split. reflexivity.
  unfold merge1_a. exists (s_symb_expr 1). split. assumption. right. split. admit. 
  unfold hd_error. exists (s_symb_expr 0). split. assumption. left. unfold Datatypes.length. unfold Nat.add. exists 2.
  unfold Nat.sub. unfold List.app. 
  split. unfold upd_resolutions. unfold Nat.eqb. assumption.
  split. auto. 
  split. unfold nth_error. reflexivity.
  split. reflexivity. split. reflexivity. admit.
Admitted.
*)

(* An example to check that the definition of merge works:
   H  = [L0 -> o1 ; L1 -> o2 ; L2 -> o3]
   H1 = [L0 -> o1'; L1 -> o2 ; L2 -> o3 ; Y0 -> o4']
   H2 = [L0 -> o1 ; L1 -> o2 ; L2 -> o3'; Y0 -> o4' ; Y1 -> o5']

   where:
   get o1 f = v1, o1' = o1[f->σ1] 
   get o3 f = v3, o3' = o3[f->σ3] 
   get o4' f = σ4 
   get o5' f = σ5

   and it must be

   H' = [L1 -> o1'' ; L2 -> o2 ; L3 -> o3'' ; Y0 -> o4' ; Y1 -> o5'']

   where: 
   o1'' = o1[f->ite(σ,σ1,v1)] 
   o3'' = o3[f->ite(σ,v3,σ3)] 
   o5'' = o5'[f->ite(σ,Z5,σ5)]
   Z = Y1_f

   o1, o1', o1'' : A
   o2 : B
   o3, o3', o3'' : C
   o4' : D
   o5', o5'' : E 
*)
(*Example example_merge_ok : forall o1 o1' o1'' o2 o3 o3' o3'' o4' o5' o5'' Y0 Y1 σ σ1 σ3 σ4 σ5 v1 v3 Z5 f H H1 H2 H', 
get o1 f = Some v1 -> o1' = upd_obj o1 f σ1 -> v1 <> σ1 -> 
get o3 f = Some v3 -> o3' = upd_obj o3 f σ3 -> v3 <> σ3 -> 
get o4' f = Some σ4 -> 
get o5' f = Some σ5 ->
Y0 = s_ref_c_symb (s_symb_expr 0) ->
Y1 = s_ref_c_symb (s_symb_expr 1) ->
(let (H_1, _) := add_obj H0 o1 in
let (H_2, _) := add_obj H_1 o2 in
let (H_3, _) := add_obj H_2 o3 in
H = H_3) ->
(let (H_1, _) := add_obj H0 o1' in
let (H_2, _) := add_obj H_1 o2 in
let (H_3, _) := add_obj H_2 o3 in
let H_4 := add_obj_symb H_3 (s_symb_expr 0) o4' in
H1 = H_4) ->
(let (H_1, _) := add_obj H0 o1 in
let (H_2, _) := add_obj H_1 o2 in
let (H_3, _) := add_obj H_2 o3' in
let H_4 := add_obj_symb H_3 (s_symb_expr 0) o4' in
let H_5 := add_obj_symb H_4 (s_symb_expr 1) o5' in
H2 = H_5) ->
o1'' = upd_obj o1 f (s_val_ite σ σ1 v1) ->
o3'' = upd_obj o3 f (s_val_ite σ v3 σ3) ->
o5'' = upd_obj o5' f (s_val_ite σ Z5 σ5) ->
(let (H_1, _) := add_obj H0 o1'' in
let (H_2, _) := add_obj H_1 o2 in
let (H_3, _) := add_obj H_2 o3'' in
let H_4 := add_obj_symb H_3 (s_symb_expr 0) o4' in
let H_5 := add_obj_symb H_4 (s_symb_expr 1) o5'' in
H' = H_5) ->
Z5 = s_val_ref_c (s_ref_c_symb (s_symb_fld (s_symb_expr 1) f)) ->
merge H1 H2 H' H f σ.
Proof.
  intros. unfold merge. split. rewrite H12. unfold SemanticsTypes.H0. unfold Aux.MapRefC.cardinal.  unfold Aux.MapRefC.empty. unfold Aux.MapRefC.this.  unfold Aux.MapRefC.Raw.empty.   unfold Aux.MapRefC.this.   unfold Aux.MapRefC.add.  unfold Aux.MapRefC.Raw.add.

unfold Datatypes.length. fold Datatypes.length. rewrite H16. rewrite H17. rewrite H21. unfold Aux.MapRefC.add. unfold Aux.MapRefC.Raw.add. unfold Datatypes.length. right. split. left.
  - admit.
  - exists σ1. exists v1. split. split. assumption. split. admit. assumption. 
    left. split. reflexivity. split. reflexivity. right. split. 
    -- admit. 
    -- exists v3. exists σ3. split. split. admit. split. assumption. assumption. 
       exists (cons o4' nil). exists nil. split. exists (s_symb_expr 0). intros. 
       --- split. assumption. left. exists 4.  split. assumption. split. auto. unfold sub.
           unfold nth_error. split. reflexivity. unfold app. split. reflexivity. reflexivity.
       --- exists (s_symb_expr 1). split. assumption. right. right. split. admit. 
           exists σ5. split. assumption. unfold hd_error. exists Z5.
           split. unfold Datatypes.length. unfold add. rewrite H30. reflexivity. 
           exists (s_symb_expr 0). split. assumption.
           unfold Datatypes.length. unfold add. unfold app. 
           left. exists 3. split. unfold upd_resolutions. 
           unfold Nat.eqb. assumption. split. auto. unfold Nat.sub.
           unfold nth_error. split. reflexivity. split. rewrite H21.
           reflexivity. split. reflexivity. split. admit. split. reflexivity. reflexivity.
Admitted.*)

(* Computes 3 + 2 *)

Compute parse "class Object {  } (2 + 3)".

Definition e1 : s_expr := s_expr_add (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 2)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l 3)))).

Definition P1 : s_prg := s_prg_l [CObject] e1.

Compute prg_to_str P1.

Compute step_to_str (step_at P1 0).
Compute step_to_str (step_at P1 1).
Compute step_to_str (step_at P1 2).

(* Computes 3 + 2 via method call *)

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

(* Computes let x = X0 in if x = 2 then true else false *)

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


