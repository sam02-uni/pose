From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From POSE Require Import Syntax.
From POSE Require Import SemanticsTypes.
From POSE Require Import SemanticsAux.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(***************** Operational semantics, declarative ****************)

(* Refinement step relation ~~> *)

Reserved Notation " x '~~>' y " (at level 50, left associativity).

Inductive rstep : config -> config -> Prop :=
| RStepGetfield1 : forall P H H' Σ' Σ e f Y s c C o σ1' σ2',
  e = s_expr_getfield (s_expr_val (s_val_ref_c Y)) f ->
  Y = s_ref_c_symb s ->
  unresolved H s ->
  class_has_field C f ->
  c = class_name C ->
  new_obj_symb P c o ->
  H' = add_obj_symb H s o -> 
  σ1' = s_val_not (s_val_eq (s_val_ref_c Y) (s_val_ref_c s_ref_c_null)) -> (* TODO redundant? *)
  σ2' = s_val_subtype (s_val_ref_c Y) (s_ty_class c) ->
  Σ' = Σ ++ [σ1' ; σ2'] ->
  (P, H, Σ, e) ~~> (P, H', Σ', e)
| RStepGetfield2 : forall P H H' Σ Σ' e f Y s c c' C' o o' σ',
  e = s_expr_getfield (s_expr_val (s_val_ref_c Y)) f ->
  Y = s_ref_c_symb s ->
  has_obj H Y o ->
  get o f = None ->
  c = o_class_name o ->
  class_has_field C' f ->
  c' = class_name C' ->
  refine_obj_symb P c c' o o' ->
  H' = repl_obj H Y o' ->
  σ' = s_val_subtype (s_val_ref_c Y) (s_ty_class c') ->
  Σ' = Σ ++ [σ'] ->
  (P, H, Σ, e) ~~> (P, H', Σ', e)
| RStepGetfield3 : forall P H H' Σ Σ' e f C t Y Z s s' o o' σ σ',
  e = s_expr_getfield (s_expr_val (s_val_ref_c Y)) f ->
  Y = s_ref_c_symb s ->
  has_obj H Y o ->
  get o f = Some s_val_unassumed ->
  class_has_field C f ->
  fdecl C f = Some (s_dc_v_l t f) ->
  is_type_primitive t = true ->
  assume_num H Y f σ Z ->
  Z = s_prim_c_symb s' ->
  o' = upd_obj o f σ ->
  H' = repl_obj H Y o' ->
  σ' = s_val_field s f s' ->
  Σ' = Σ ++ [σ'] ->
  (P, H, Σ, e) ~~> (P, H', Σ', e)
| RStepGetfield4 : forall P H H' Σ Σ' e f C t Y Z s s' o o' σ σ',
  e = s_expr_getfield (s_expr_val (s_val_ref_c Y)) f ->
  Y = s_ref_c_symb s ->
  has_obj H Y o ->
  get o f = Some s_val_unassumed ->
  class_has_field C f ->
  fdecl C f = Some (s_dc_v_l t f) ->
  is_type_reference t = true ->
  assume_ref H Y f σ Z ->
  Z = s_ref_c_symb s' ->
  o' = upd_obj o f σ ->
  H' = repl_obj H Y o' ->
  σ' = s_val_field s f s' ->
  Σ' = Σ ++ [σ'] ->
  (P, H, Σ, e) ~~> (P, H', Σ', e)
| RStepPutfield1 : forall P H H' Σ Σ' e f Y σ s c C o σ1' σ2',
  e = s_expr_putfield (s_expr_val (s_val_ref_c Y)) f (s_expr_val σ) ->
  Y = s_ref_c_symb s ->
  unresolved H s ->
  class_has_field C f ->
  c = class_name C ->
  new_obj_symb P c o ->
  H' = add_obj_symb H s o ->
  σ1' = s_val_not (s_val_eq (s_val_ref_c Y) (s_val_ref_c s_ref_c_null)) -> (* TODO redundant? *)
  σ2' = s_val_subtype (s_val_ref_c Y) (s_ty_class c) ->
  Σ' = Σ ++ [σ1' ; σ2'] ->
  (P, H, Σ, e) ~~> (P, H', Σ', e)
| RStepPutfield2 : forall P H H' Σ Σ' e f Y σ σ' s c c' C' o o',
  e = s_expr_putfield (s_expr_val (s_val_ref_c Y)) f (s_expr_val σ) ->
  Y = s_ref_c_symb s ->
  has_obj H Y o ->
  c = o_class_name o ->
  get o f = None ->
  class_has_field C' f ->
  c' = class_name C' ->
  refine_obj_symb P c c' o o' ->
  H' = repl_obj H Y o' ->
  σ' = s_val_subtype (s_val_ref_c Y) (s_ty_class c') ->
  Σ' = Σ ++ [σ'] ->
  (P, H, Σ, e) ~~> (P, H', Σ', e)
| RStepCtxGetfield : forall P H H' Σ Σ' e e' f,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_getfield e f) ~~> (P, H', Σ', s_expr_getfield e' f)
| RStepCtxPutfield1 : forall P H H' Σ Σ' e e' e1 f,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_putfield e f e1) ~~> (P, H', Σ', s_expr_putfield e' f e1)
| RStepCtxPutfield2 : forall P H H' Σ Σ' e e' σ f,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_putfield (s_expr_val σ) f e) ~~> (P, H', Σ', s_expr_putfield (s_expr_val σ) f e')
| RStepCtxLet : forall P H H' Σ Σ' e e' e1 x,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_let x e e1) ~~> (P, H', Σ', s_expr_let x e' e1)
| RStepCtxAdd1 : forall P H H' Σ Σ' e e' e1,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_add e e1) ~~> (P, H', Σ', s_expr_add e' e1)
| RStepCtxAdd2 : forall P H H' Σ Σ' e e' σ,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_add (s_expr_val σ) e) ~~> (P, H', Σ', s_expr_add (s_expr_val σ) e')
| RStepCtxLt1 : forall P H H' Σ Σ' e e' e1,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->
  (P, H, Σ, s_expr_lt e e1) ~~> (P, H', Σ', s_expr_lt e' e1)
| RStepCtxLt2 : forall P H H' Σ Σ' e e' σ,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->
  (P, H, Σ, s_expr_lt (s_expr_val σ) e) ~~> (P, H', Σ', s_expr_lt (s_expr_val σ) e')
| RStepCtxEq1 : forall P H H' Σ Σ' e e' e1,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_eq e e1) ~~> (P, H', Σ', s_expr_eq e' e1)
| RStepCtxEq2 : forall P H H' Σ Σ' e e' σ,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_eq (s_expr_val σ) e) ~~> (P, H', Σ', s_expr_eq (s_expr_val σ) e')
| RStepCtxInstanceof : forall P H H' Σ Σ' e e' c,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_instanceof e c) ~~> (P, H', Σ', s_expr_instanceof e' c)
| RStepCtxIf : forall P H H' Σ Σ' e e' e1 e2,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_if e e1 e2) ~~> (P, H', Σ', s_expr_if e' e1 e2)
| RStepCtxInvoke1 : forall P H H' Σ Σ' e e' e1 m,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_invoke e m e1) ~~> (P, H', Σ', s_expr_invoke e' m e1)
| RStepCtxInvoke2 : forall P H H' Σ Σ' e e' σ m,
  (P, H, Σ, e) ~~> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_invoke (s_expr_val σ) m e) ~~> (P, H', Σ', s_expr_invoke (s_expr_val σ) m e')
where " x '~~>' y " := (rstep x y).

(* Reflexive-transitive closure of the refinement 
   step relation ~~>* *)

Reserved Notation " x '~~>*' y " (at level 50, left associativity).

Inductive rstep_star : config -> config -> Prop :=
| RStepStarZero : forall J, J ~~>* J
| RStepStarNext : forall J J' J'', J ~~> J' -> J' ~~>* J'' -> J ~~>* J''
where " x '~~>*' y " := (rstep_star x y).

(* Computation step relation --> and step relation ==> *)

Reserved Notation " x '-->' y " (at level 50, left associativity).

Reserved Notation " x '==>' y " (at level 50, left associativity).

Inductive cstep : config -> config -> Prop :=
| CStepNew : forall P H H' Σ e e' c C o u,
  e = s_expr_new c -> 
  cdecl P c = Some C ->
  new_obj P c o ->
  (H', u) = add_obj H o ->
  e' = s_expr_val (s_val_ref_c u) ->
  (P, H, Σ, e) --> (P, H', Σ, e')
| CStepGetfield1 : forall P H Σ e e' f l n o σ,
  e = s_expr_getfield (s_expr_val (s_val_ref_c l)) f ->
  l = s_ref_c_loc (s_loc_l n) ->
  has_obj H l o ->
  get o f = Some σ ->
  e' = s_expr_val σ ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepGetfield2 : forall P H Σ e e' f Y s o σ,
  e = s_expr_getfield (s_expr_val (s_val_ref_c Y)) f ->
  Y = s_ref_c_symb s ->
  has_obj H Y o ->
  get o f = Some σ ->
  ~(σ = s_val_unassumed) ->
  e' = s_expr_val σ ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepGetfield3 : forall P H H' H1' Σ Σ' Σ1' Σ2' e e' f σ σ1 σ2 σ1' σ2',
  (P, H, Σ, (s_expr_getfield (s_expr_val σ1) f)) ==> (P, H1', Σ1', (s_expr_val σ1')) ->
  (P, H1', Σ, (s_expr_getfield (s_expr_val σ2) f)) ==> (P, H', Σ2', (s_expr_val σ2')) ->
  Σ' = merge_pc σ Σ1' Σ2' ->
  e = s_expr_getfield (s_expr_val (s_val_ite σ σ1 σ2)) f ->
  e' = s_expr_val (s_val_ite σ σ1' σ2') ->
  (P, H, Σ, e) --> (P, H', Σ', e')
| CStepPutfield1 : forall P H H' Σ e e' σ f l n o o',
  e' = s_expr_val σ ->
  e = s_expr_putfield (s_expr_val (s_val_ref_c l)) f e' ->
  l = s_ref_c_loc (s_loc_l n) ->
  has_obj H l o ->
  o' = upd_obj o f σ ->
  H' = repl_obj H l o' ->
  (P, H, Σ, e) --> (P, H', Σ, e')
| CStepPutfield2 : forall P H HRefined H' Σ e e' σ σ' f Y s o o',
  e' = s_expr_val σ ->
  e = s_expr_putfield (s_expr_val (s_val_ref_c Y)) f e' ->
  Y = s_ref_c_symb s ->
  has_obj H Y o ->
  get o f = Some σ' ->
  update f Y σ H HRefined ->
  o' = upd_obj o f σ ->
  H' = repl_obj HRefined Y o' ->
  (P, H, Σ, e) --> (P, H', Σ, e')
| CStepPutfield3 : forall P H H' H1' H2' Σ Σ' Σ1' Σ2' Σetc e e' f σ σ1 σ2 σ',
  e' = s_expr_val σ' ->
  (P, H, Σ, s_expr_putfield (s_expr_val σ1) f e') ==> (P, H1', Σ1', e') ->
  (P, H, Σ, s_expr_putfield (s_expr_val σ2) f e') ==> (P, H2', Σ2', e') ->
  e = s_expr_putfield (s_expr_val (s_val_ite σ σ1 σ2)) f e' ->
  merge H1' H2' H' H f σ ->
  merge_clauses H1' H2' f = Some Σetc ->
  Σ' = (merge_pc σ Σ1' Σ2') ++ Σetc ->
  (P, H, Σ, e) --> (P, H', Σ', e')
| CStepLet : forall P H Σ e e' e1 x σ,
  e = s_expr_let x (s_expr_val σ) e1 ->
  e' = repl_var e1 x (s_expr_val σ) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepAdd1 : forall P H Σ e e' n1 n2,
  e = s_expr_add (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n1)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n2)))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l (n1 + n2)))) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepAdd2 : forall P H Σ e e' n σ1 σ2,
  e = s_expr_add (s_expr_val σ1) (s_expr_val σ2) ->
  (σ1 <> s_val_prim_c (s_prim_c_int (s_int_l n)) \/ σ2 <> s_val_prim_c (s_prim_c_int (s_int_l n))) ->
  e' = s_expr_val (s_val_add σ1 σ2) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepSub1 : forall P H Σ e e' n1 n2,
  e = s_expr_sub (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n1)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n2)))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l (n1 - n2)))) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepSub2 : forall P H Σ e e' n σ1 σ2,
  e = s_expr_sub (s_expr_val σ1) (s_expr_val σ2) ->
  (σ1 <> s_val_prim_c (s_prim_c_int (s_int_l n)) \/ σ2 <> s_val_prim_c (s_prim_c_int (s_int_l n))) ->
  e' = s_expr_val (s_val_sub σ1 σ2) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepLt1 : forall P H Σ e e' n1 n2,
  e = s_expr_lt (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n1)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n2)))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool (if Nat.ltb n1 n2 then s_bool_true else s_bool_false))) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepLt2 : forall P H Σ e e' n σ1 σ2,
  e = s_expr_lt (s_expr_val σ1) (s_expr_val σ2) ->
  (σ1 <> s_val_prim_c (s_prim_c_int (s_int_l n)) \/ σ2 <> s_val_prim_c (s_prim_c_int (s_int_l n))) ->
  e' = s_expr_val (s_val_lt σ1 σ2) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepAnd1 : forall P H Σ e e',
  e = s_expr_and (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepAnd2 : forall P H Σ e e',
  e = s_expr_and (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepAnd3 : forall P H Σ e e',
  e = s_expr_and (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepAnd4 : forall P H Σ e e',
  e = s_expr_and (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepAnd5 : forall P H Σ e e' b σ1 σ2,
  e = s_expr_and (s_expr_val σ1) (s_expr_val σ2) ->
  (σ1 <> s_val_prim_c (s_prim_c_bool b) \/ σ2 <> s_val_prim_c (s_prim_c_bool b)) ->
  e' = s_expr_val (s_val_and σ1 σ2) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepOr1 : forall P H Σ e e',
  e = s_expr_or (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepOr2 : forall P H Σ e e',
  e = s_expr_or (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepOr3 : forall P H Σ e e',
  e = s_expr_or (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepOr4 : forall P H Σ e e',
  e = s_expr_or (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepOr5 : forall P H Σ e e' b σ1 σ2,
  e = s_expr_or (s_expr_val σ1) (s_expr_val σ2) ->
  (σ1 <> s_val_prim_c (s_prim_c_bool b) \/ σ2 <> s_val_prim_c (s_prim_c_bool b)) ->
  e' = s_expr_val (s_val_or σ1 σ2) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepNot1 : forall P H Σ e e',
  e = s_expr_not (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepNot2 : forall P H Σ e e',
  e = s_expr_not (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepNot3 : forall P H Σ e e' b σ,
  e = s_expr_not (s_expr_val σ) ->
  σ <> s_val_prim_c (s_prim_c_bool b) ->
  e' = s_expr_val (s_val_not σ) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq1 : forall P H Σ e e' n1 n2,
  e = s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n1)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n2)))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool (if Nat.eqb n1 n2 then s_bool_true else s_bool_false))) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq2 : forall P H Σ e e',
  e = s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq3 : forall P H Σ e e',
  e = s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq4 : forall P H Σ e e',
  e = s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq5 : forall P H Σ e e',
  e = s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq6 : forall P H Σ e e',
  e = s_expr_eq (s_expr_val (s_val_ref_c s_ref_c_null)) (s_expr_val (s_val_ref_c s_ref_c_null)) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq7 : forall P H Σ e e' l,
  e = s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_loc l))) (s_expr_val (s_val_ref_c s_ref_c_null)) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq8 : forall P H Σ e e' l,
  e = s_expr_eq (s_expr_val (s_val_ref_c s_ref_c_null)) (s_expr_val (s_val_ref_c (s_ref_c_loc l))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq9 : forall P H Σ e e' n1 n2,
  e = s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_loc (s_loc_l n1)))) (s_expr_val (s_val_ref_c (s_ref_c_loc (s_loc_l n2)))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool (if Nat.eqb n1 n2 then s_bool_true else s_bool_false))) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq10 : forall P H Σ e e' l s,
  e = s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_loc l))) (s_expr_val (s_val_ref_c (s_ref_c_symb s))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq11 : forall P H Σ e e' l s,
  e = s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_symb s))) (s_expr_val (s_val_ref_c (s_ref_c_loc l))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq12 : forall P H Σ e e' l σ1 σ2 σ3,
  e = s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_loc l))) (s_expr_val (s_val_ite σ1 σ2 σ3)) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq13 : forall P H Σ e e' l σ1 σ2 σ3,
  e = s_expr_eq (s_expr_val (s_val_ite σ1 σ2 σ3)) (s_expr_val (s_val_ref_c (s_ref_c_loc l))) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepEq14 : forall P H Σ e e' n b l s σ1 σ2 σ3 σ4 σ5,
  e = s_expr_eq (s_expr_val σ1) (s_expr_val σ2) ->
  ((σ1 <> s_val_prim_c (s_prim_c_int (s_int_l n)) /\ σ1 <> s_val_prim_c (s_prim_c_bool b) /\
  σ1 <> s_val_ref_c s_ref_c_null /\ σ1 <> s_val_ref_c (s_ref_c_loc (s_loc_l n))) \/
  (σ2 <> s_val_prim_c (s_prim_c_int (s_int_l n)) /\ σ2 <> s_val_prim_c (s_prim_c_bool b) /\
  σ2 <> s_val_ref_c s_ref_c_null /\ σ2 <> s_val_ref_c (s_ref_c_loc (s_loc_l n)))) ->
  ~(σ1 = (s_val_ref_c (s_ref_c_loc l)) /\ σ2 = (s_val_ref_c (s_ref_c_symb s))) ->
  ~(σ2 = (s_val_ref_c (s_ref_c_loc l)) /\ σ1 = (s_val_ref_c (s_ref_c_symb s))) ->
  ~(σ1 = (s_val_ref_c (s_ref_c_loc l)) /\ σ2 = (s_val_ite σ3 σ4 σ5)) ->
  ~(σ2 = (s_val_ref_c (s_ref_c_loc l)) /\ σ1 = (s_val_ite σ3 σ4 σ5)) ->
  e' = s_expr_val (s_val_eq σ1 σ2) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepInstanceof1 : forall P H Σ e e' c,
  e = s_expr_instanceof (s_expr_val (s_val_ref_c s_ref_c_null)) c ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepInstanceof2 : forall P H Σ e e' l n c c',
  e = s_expr_instanceof (s_expr_val (s_val_ref_c l)) c ->
  l = s_ref_c_loc (s_loc_l n) ->
  obj_class_at H l = Some c' ->
  subclass P c' c ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepInstanceof3 : forall P H Σ e e' l n c c',
  e = s_expr_instanceof (s_expr_val (s_val_ref_c l)) c ->
  l = s_ref_c_loc (s_loc_l n) ->
  obj_class_at H l = Some c' ->
  ~(subclass P c' c) ->
  e' = s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepInstanceof4 : forall P H Σ e e' Y s c,
  e = s_expr_instanceof (s_expr_val (s_val_ref_c Y)) c ->
  Y = s_ref_c_symb s ->
  e' = s_expr_val (s_val_subtype (s_val_ref_c Y) (s_ty_class c)) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepInstanceof5 : forall P H Σ e e' σ c σ1 σ2 σ1' σ2',
  (P, H, Σ, s_expr_instanceof (s_expr_val σ1) c) ==> (P, H, Σ, (s_expr_val σ1')) ->
  (P, H, Σ, s_expr_instanceof (s_expr_val σ2) c) ==> (P, H, Σ, (s_expr_val σ2')) ->
  e = s_expr_instanceof (s_expr_val (s_val_ite σ σ1 σ2)) c ->
  e' = s_expr_val (s_val_ite σ σ1' σ2') ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepIf1 : forall P H Σ e e1 e2,
  e = s_expr_if (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) e1 e2 ->
  (P, H, Σ, e) --> (P, H, Σ, e1)
| CStepIf2 : forall P H Σ e e1 e2,
  e = s_expr_if (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) e1 e2 ->
  (P, H, Σ, e) --> (P, H, Σ, e2)
| CStepIf3 : forall P H Σ Σ' e e1 e2 σ,
  e = s_expr_if (s_expr_val σ) e1 e2 ->
  Σ' = Σ ++ [σ] ->
  (P, H, Σ, e) --> (P, H, Σ', e1)
| CStepIf4 : forall P H Σ Σ' e e1 e2 σ,
  e = s_expr_if (s_expr_val σ) e1 e2 ->
  Σ' = Σ ++ [s_val_not σ] ->
  (P, H, Σ, e) --> (P, H, Σ', e2)
| CStepInvoke1 : forall P H Σ e e' l n m σ o c c' t1 t2 xM eM,
  e = s_expr_invoke (s_expr_val (s_val_ref_c l)) m (s_expr_val σ) ->
  l = s_ref_c_loc (s_loc_l n) ->
  has_obj H l o ->
  o_class_name o = c ->
  recv_method P m c c' ->
  mdecl P c' m = Some (s_dc_m_l t1 m (s_dc_v_l t2 xM) eM) ->
  e' = repl_var (repl_var eM "this" (s_expr_val (s_val_ref_c l))) xM (s_expr_val σ) ->
  (P, H, Σ, e) --> (P, H, Σ, e')
| CStepInvoke2 : forall P H Σ Σ' e e' eM Y s m σ c' t1 t2 xM O σ1' σ2',
  e = s_expr_invoke (s_expr_val (s_val_ref_c Y)) m (s_expr_val σ) ->
  Y = s_ref_c_symb s ->
  mdecl P c' m = Some (s_dc_m_l t1 m (s_dc_v_l t2 xM) eM) ->
  forall c, (In c O <-> overrides P m c c') ->
  σ1' = s_val_not (s_val_eq (s_val_ref_c Y) (s_val_ref_c s_ref_c_null)) -> (* TODO redundant? *)
  σ2' = s_val_subtype (s_val_ref_c Y) (s_ty_class c') ->
  Σ' = Σ ++ [σ1' ; σ2'] ++ map (fun c => s_val_not (s_val_subtype (s_val_ref_c Y) (s_ty_class c))) O ->
  e' = repl_var (repl_var eM "this" (s_expr_val (s_val_ref_c Y))) xM (s_expr_val σ) ->
  (P, H, Σ, e) --> (P, H, Σ', e')
| CStepInvoke3 : forall P H Σ Σ' Σ1' m e e1' σ σ' σ1 σ2,
  (P, H, Σ, s_expr_invoke (s_expr_val σ1) m (s_expr_val σ')) ==> (P, H, Σ1', e1') ->
  e = s_expr_invoke (s_expr_val (s_val_ite σ σ1 σ2)) m (s_expr_val σ') ->
  Σ' = Σ1' ++ [σ] ->
  (P, H, Σ, e) --> (P, H, Σ', e1')
| CStepInvoke4 : forall P H Σ Σ' Σ2' m e e2' σ σ' σ1 σ2,
  (P, H, Σ, s_expr_invoke (s_expr_val σ2) m (s_expr_val σ')) ==> (P, H, Σ2', e2') ->
  e = s_expr_invoke (s_expr_val (s_val_ite σ σ1 σ2)) m (s_expr_val σ') ->
  Σ' = Σ2' ++ [s_val_not σ] ->
  (P, H, Σ, e) --> (P, H, Σ', e2')
| CStepCtxGetfield : forall P H H' Σ Σ' e e' f,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_getfield e f) --> (P, H', Σ', s_expr_getfield e' f)
| CStepCtxPutfield1 : forall P H H' Σ Σ' e e' e1 f,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_putfield e f e1) --> (P, H', Σ', s_expr_putfield e' f e1)
| CStepCtxPutfield2 : forall P H H' Σ Σ' e e' σ f,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_putfield (s_expr_val σ) f e) --> (P, H', Σ', s_expr_putfield (s_expr_val σ) f e')
| CStepCtxLet : forall P H H' Σ Σ' e e' e1 x,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_let x e e1) --> (P, H', Σ', s_expr_let x e' e1)
| CStepCtxAdd1 : forall P H H' Σ Σ' e e' e1,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_add e e1) --> (P, H', Σ', s_expr_add e' e1)
| CStepCtxAdd2 : forall P H H' Σ Σ' e e' σ,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_add (s_expr_val σ) e) --> (P, H', Σ', s_expr_add (s_expr_val σ) e')
| CStepCtxSub1 : forall P H H' Σ Σ' e e' e1,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_sub e e1) --> (P, H', Σ', s_expr_sub e' e1)
| CStepCtxSub2 : forall P H H' Σ Σ' e e' σ,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_sub (s_expr_val σ) e) --> (P, H', Σ', s_expr_sub (s_expr_val σ) e')
| CStepCtxLt1 : forall P H H' Σ Σ' e e' e1,
  (P, H, Σ, e) --> (P, H', Σ', e') ->
  (P, H, Σ, s_expr_lt e e1) --> (P, H', Σ', s_expr_lt e' e1)
| CStepCtxLt2 : forall P H H' Σ Σ' e e' σ,
  (P, H, Σ, e) --> (P, H', Σ', e') ->
  (P, H, Σ, s_expr_lt (s_expr_val σ) e) --> (P, H', Σ', s_expr_lt (s_expr_val σ) e')
| CStepCtxEq1 : forall P H H' Σ Σ' e e' e1,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_eq e e1) --> (P, H', Σ', s_expr_eq e' e1)
| CStepCtxEq2 : forall P H H' Σ Σ' e e' σ,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_eq (s_expr_val σ) e) --> (P, H', Σ', s_expr_eq (s_expr_val σ) e')
| CStepCtxInstanceof : forall P H H' Σ Σ' e e' c,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_instanceof e c) --> (P, H', Σ', s_expr_instanceof e' c)
| CStepCtxIf : forall P H H' Σ Σ' e e' e1 e2,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_if e e1 e2) --> (P, H', Σ', s_expr_if e' e1 e2)
| CStepCtxInvoke1 : forall P H H' Σ Σ' e e' e1 m,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_invoke e m e1) --> (P, H', Σ', s_expr_invoke e' m e1)
| CStepCtxInvoke2 : forall P H H' Σ Σ' e e' σ m,
  (P, H, Σ, e) --> (P, H', Σ', e') ->  
  (P, H, Σ, s_expr_invoke (s_expr_val σ) m e) --> (P, H', Σ', s_expr_invoke (s_expr_val σ) m e')
with step : config -> config -> Prop :=
| Step : forall J J' J'', J ~~>* J' -> J' --> J'' -> J ==> J''
where " x '-->' y " := (cstep x y)
and " x '==>' y " := (step x y).

