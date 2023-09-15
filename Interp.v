From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Program.Wf.
From Hammer Require Import Tactics.
From POSE Require Import Syntax.
From POSE Require Import SemanticsTypes.
From POSE Require Import SemanticsAux.

Extraction Language Haskell.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(********* Computable operational semantics (aka interpreter) ***********)

(* Coinductive definition of computation as an
   infinite stream of lists of configurations, 
   where each list is the output of the previous 
   computation step and the input to the next
   computation step *)

Definition computation : Type := Stream (list config).

Section StepDefs.

(* Measure function for expressions *)

Let Fixpoint height_s_val (σ : s_val) : nat :=
  match σ with
  | s_val_unassumed
  | s_val_prim_c _
  | s_val_ref_c _ => 0
  | s_val_add σ1 σ2 => S (Nat.max (height_s_val σ1) (height_s_val σ2))
  | s_val_sub σ1 σ2 => S (Nat.max (height_s_val σ1) (height_s_val σ2))
  | s_val_lt σ1 σ2 => S (Nat.max (height_s_val σ1) (height_s_val σ2))
  | s_val_and σ1 σ2 => S (Nat.max (height_s_val σ1) (height_s_val σ2))
  | s_val_or σ1 σ2 => S (Nat.max (height_s_val σ1) (height_s_val σ2))
  | s_val_not σ1 => S (height_s_val σ1)
  | s_val_eq σ1 σ2 => S (Nat.max (height_s_val σ1) (height_s_val σ2))
  | s_val_subtype σ1 t => S (height_s_val σ1)
  | s_val_field _ _ _ => 0
  | s_val_ite σ1 σ2 σ3 => S (Nat.max (height_s_val σ1) (Nat.max (height_s_val σ2) (height_s_val σ3)))
  end.

Let Fixpoint height_s_expr (e : s_expr) : nat :=
  match e with
  | s_expr_var _ => 0
  | s_expr_val σ  => height_s_val σ
  | s_expr_new _ => 0
  | s_expr_getfield e1 _ => S (height_s_expr e1)
  | s_expr_putfield e1 _ e2 => S (height_s_expr e1) + height_s_expr e2
  | s_expr_let _ e1 _ => S (height_s_expr e1)
  | s_expr_add e1 e2 => S (height_s_expr e1) + height_s_expr e2
  | s_expr_sub e1 e2 => S (height_s_expr e1) + height_s_expr e2
  | s_expr_lt e1 e2 => S (height_s_expr e1) + height_s_expr e2
  | s_expr_and e1 e2 => S (height_s_expr e1) + height_s_expr e2
  | s_expr_or e1 e2 => S (height_s_expr e1) + height_s_expr e2
  | s_expr_not e1 => S (height_s_expr e1)
  | s_expr_eq e1 e2 => S (height_s_expr e1) + height_s_expr e2
  | s_expr_instanceof e1 c => S (height_s_expr e1)
  | s_expr_if e1 _ _ => S (height_s_expr e1)
  | s_expr_invoke e1 _ e2 => S (height_s_expr e1) + height_s_expr e2
  end.

(* Some useful lemmas *)

Lemma maxl : forall n1 n2, n1 <= Nat.max n1 n2.
Proof.
sauto.
Qed.

Lemma maxr : forall n1 n2, n2 <= Nat.max n1 n2.
Proof.
sauto.
Qed.

Lemma add_l : forall a b, S (a + b) = S a + b.
Proof.
auto.
Qed.

Lemma leq_canc : forall a b c, a + c <= b + c <-> a <= b.
Proof.
sauto.
Qed.

(* The refinement step function *)

Fixpoint rstep_c (P : s_prg) (H : heap) (Σ : path_condition) (e : s_expr) : option (heap * path_condition) :=
  match e with
  | s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb s))) f =>
    let Y := s_ref_c_symb s in
    if unresolved_c H s then
    match class_with_field P f with
    | Some C => 
      let c := class_name C in
      let o := new_obj_symb_c P c in
      let H' := add_obj_symb H s o in
      let cl1 := s_val_not (s_val_eq (s_val_ref_c Y) (s_val_ref_c s_ref_c_null)) in (*TODO redundant? *)
      let cl2 := s_val_subtype (s_val_ref_c Y) (s_ty_class c) in
      let Σ' := Σ ++ [cl1 ; cl2] in
      Some (H', Σ')
    | _ => None (* error: no class in P has field f *)
    end
    else match obj_at H Y with
    | Some o => match get o f with
      | None => match class_with_field P f with
        | Some C' =>
          let c' := class_name C' in
          let o' := refine_obj_symb_c P c' o in
          let H' := repl_obj H Y o' in
          let cl := s_val_subtype (s_val_ref_c Y) (s_ty_class c') in
          let Σ' := Σ ++ [cl] in
          Some (H', Σ')
        | _ => None (* error: no class exists with field f *)
        end
      | Some s_val_unassumed => match class_with_field P f with
        | Some C' =>
          match fdecl C' f with
          | Some F =>              
            let t := field_type F in
            if is_type_primitive t then
              match assume_c_num H Y f with
              | Some (σ, s_prim_c_symb s') =>
                let o' := upd_obj o f σ in
                let H' := repl_obj H Y o' in
                let cl := s_val_field s f s' in
                let Σ' := Σ ++ [cl] in
                Some (H', Σ')
              | _ => None
              end
            else
              match assume_c_ref H Y f with
              | Some (σ, s_ref_c_symb s') =>
                let o' := upd_obj o f σ in
                let H' := repl_obj H Y o' in
                let cl := s_val_field s f s' in
                let Σ' := Σ ++ [cl] in
                Some (H', Σ')
              | _ => None
              end
          | _ => None (* error (internal): class C' has no field f *)
          end
        | _ => None (* error (internal): no class exists with field f *)
        end
      | _ => None (* error: the symbolic object's field was refined before *)
      end
    | _ => None (* error: symbolic reference is resolved but no associated symbolic object is in the heap *)
    end
  | s_expr_putfield (s_expr_val (s_val_ref_c (s_ref_c_symb s))) f (s_expr_val σ) =>
    let Y := s_ref_c_symb s in
    if unresolved_c H s then
    match class_with_field P f with
    | Some C => 
      let c := class_name C in
      let o := new_obj_symb_c P c in
      let H' := add_obj_symb H s o in
      let cl1 := s_val_not (s_val_eq (s_val_ref_c Y) (s_val_ref_c s_ref_c_null)) in (*TODO redundant? *)
      let cl2 := s_val_subtype (s_val_ref_c Y) (s_ty_class c) in
      let Σ' := Σ ++ [cl1 ; cl2] in
      Some (H', Σ')
    | _ => None
    end
    else match obj_at H Y with
    | Some o => match get o f with
      | None => match class_with_field P f with
        | Some C' =>
          let c' := class_name C' in
          let o' := refine_obj_symb_c P c' o in
          let H' := repl_obj H Y o' in
          let cl := s_val_subtype (s_val_ref_c Y) (s_ty_class c') in
          let Σ' := Σ ++ [cl] in
          Some (H', Σ')
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | s_expr_getfield e1 f => rstep_c P H Σ e1
  | s_expr_putfield (s_expr_val _) f e1 => rstep_c P H Σ e1
  | s_expr_putfield e1 f e2 => rstep_c P H Σ e1
  | s_expr_let x e1 e2 => rstep_c P H Σ e1
  | s_expr_add (s_expr_val _) e1 => rstep_c P H Σ e1
  | s_expr_add e1 e2 => rstep_c P H Σ e1
  | s_expr_sub (s_expr_val _) e1 => rstep_c P H Σ e1
  | s_expr_sub e1 e2 => rstep_c P H Σ e1
  | s_expr_lt (s_expr_val _) e1 => rstep_c P H Σ e1
  | s_expr_lt e1 e2 => rstep_c P H Σ e1
  | s_expr_and (s_expr_val _) e1 => rstep_c P H Σ e1
  | s_expr_and e1 e2 => rstep_c P H Σ e1
  | s_expr_or (s_expr_val _) e1 => rstep_c P H Σ e1
  | s_expr_or e1 e2 => rstep_c P H Σ e1
  | s_expr_not e1 => rstep_c P H Σ e1
  | s_expr_eq (s_expr_val _) e1 => rstep_c P H Σ e1
  | s_expr_eq e1 e2 => rstep_c P H Σ e1
  | s_expr_instanceof e1 c => rstep_c P H Σ e1
  | s_expr_if e1 e2 e3 => rstep_c P H Σ e1
  | s_expr_invoke (s_expr_val _) m e1 => rstep_c P H Σ e1
  | s_expr_invoke e1 m e2 => rstep_c P H Σ e1
  | _ => None
  end.

(* Unwinds to maximum depth the refinement 
   step function. Note that there may be no more than 
   two refinement steps between two computation steps, 
   so step indexing with maximum bound of 2 ensures 
   termination but does not alter the semantics. *)

Let Fixpoint rstep_c_star_bounded (P : s_prg) (H : heap) (Σ : path_condition) (e : s_expr) (n : nat) : option (heap * path_condition) :=
  match rstep_c P H Σ e, n with
  | None, _ => Some (H, Σ)
  | Some (H', Σ'), S n' => rstep_c_star_bounded P H' Σ' e n'
  | _, _ => None
  end.

Definition rstep_c_star  (P : s_prg) (H : heap) (Σ : path_condition) (e : s_expr) : option (heap * path_condition) :=
  rstep_c_star_bounded P H Σ e 2.


(* The result of a computation step - from zero to
   n successors (finitely branching) *)

Let cstep_result : Type := list (heap * path_condition * s_expr).

(* The computation step function *)

Program Fixpoint cstep_c_fp (P : s_prg) (H : heap) (Σ : path_condition) (e : s_expr) {measure (height_s_expr e)}: cstep_result :=
  match e with
  | s_expr_new c => match cdecl P c with
    | Some C => 
      let o := new_obj_c P c in
      let (H', u) := add_obj H o in
      let e' := s_expr_val (s_val_ref_c u) in
      [(H', Σ, e')]
    | _ => []
    end
  | s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_loc (s_loc_l n)))) f =>
    let l := s_ref_c_loc (s_loc_l n) in
    match obj_at H l with
    | Some o => match get o f with
      | Some σ =>
        let e' := s_expr_val σ in
        [(H, Σ, e')]
      | _ => [] (* error: field not present in the concrete object *)
      end
    | _ => [] (* error: no concrete object in the heap corresponding to the concrete reference *)
    end
  | s_expr_getfield (s_expr_val (s_val_ref_c (s_ref_c_symb s))) f =>
    let Y := s_ref_c_symb s in
    match obj_at H Y with
    | Some o => match get o f with
      | Some σ => if negb (s_val_eqb σ s_val_unassumed) then
        let e' := s_expr_val σ in
        [(H, Σ, e')]
        else []
      | _ => []
      end
    | _ => []
    end
  | s_expr_getfield (s_expr_val (s_val_ite σ σ1 σ2)) f =>
    let e1 := s_expr_getfield (s_expr_val σ1) f in
    let e2 := s_expr_getfield (s_expr_val σ2) f in
    match rstep_c_star P H Σ e1 with
    | Some (H1tmp, Σ1tmp) => match cstep_c_fp P H1tmp Σ1tmp e1 with
      | [(H1', Σ1', s_expr_val σ1')] => match rstep_c_star P H1' Σ e2 with
          | Some (Htmp', Σtmp') => match cstep_c_fp P Htmp' Σtmp' e2 with
            | [(H', Σ2', s_expr_val σ2')] => let Σ' := merge_pc σ Σ1' Σ2' in
              [(H', Σ', s_expr_val (s_val_ite σ σ1' σ2'))]
            | _ => []
            end
          | _ => []
          end
      | _ => []
      end
    | _ => []
    end
  | s_expr_putfield (s_expr_val (s_val_ref_c (s_ref_c_loc (s_loc_l n)))) f (s_expr_val σ) =>
    let l := s_ref_c_loc (s_loc_l n) in
    let e' := s_expr_val σ in
    match obj_at H l with
    | Some o => 
      let o' := upd_obj o f σ in
      let H' := repl_obj H l o' in
      [(H', Σ, e')]
    | _ => []
    end
  | s_expr_putfield (s_expr_val (s_val_ref_c (s_ref_c_symb s))) f (s_expr_val σ) =>
    let Y := s_ref_c_symb s in
    let e' := s_expr_val σ in
    match obj_at H Y with
    | Some o => match get o f with
      | Some _ => 
        let o' := upd_obj o f σ in
        let HRefined := update_c f Y σ H in
        let H' := repl_obj HRefined Y o' in
        [(H', Σ, e')]
      | _ => []
      end
    | _ => []
    end
  | s_expr_putfield (s_expr_val (s_val_ite σ σ1 σ2)) f (s_expr_val σ') =>
    let e' := s_expr_val σ' in
    let e1 := s_expr_putfield (s_expr_val σ1) f e' in
    let e2 := s_expr_putfield (s_expr_val σ2) f e' in
    match rstep_c_star P H Σ e1, rstep_c_star P H Σ e2 with
    | Some (H1tmp, Σ1tmp), Some (H2tmp, Σ2tmp) =>
      match cstep_c_fp P H1tmp Σ1tmp e1, cstep_c_fp P H2tmp Σ2tmp e2 with
      | [(H1', Σ1', _)], [(H2', Σ2', _)] =>
        match merge_c H1' H2' f σ, merge_clauses H1' H2' f with
        | Some H', Some Σetc => 
          let Σ' := (merge_pc σ Σ1' Σ2') ++ Σetc in
          [(H', Σ', e')]
        | _, _ => []
        end
      | _, _ => []
      end
    | _, _=> []
    end
  | s_expr_let x (s_expr_val σ) e1 =>
    let e' := repl_var e1 x (s_expr_val σ) in
    [(H, Σ, e')]
  | s_expr_add (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n1)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n2)))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l (n1 + n2)))) in
    [(H, Σ, e')]
  | s_expr_add (s_expr_val σ1) (s_expr_val σ2) =>
    let e' := s_expr_val (s_val_add σ1 σ2) in
    [(H, Σ, e')]
  | s_expr_sub (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n1)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n2)))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l (n1 - n2)))) in
    [(H, Σ, e')]
  | s_expr_sub (s_expr_val σ1) (s_expr_val σ2) =>
    let e' := s_expr_val (s_val_sub σ1 σ2) in
    [(H, Σ, e')]
  | s_expr_lt (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n1)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n2)))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool (if Nat.ltb n1 n2 then s_bool_true else s_bool_false))) in
    [(H, Σ, e')]
  | s_expr_lt (s_expr_val σ1) (s_expr_val σ2) =>
    let e' := s_expr_val (s_val_lt σ1 σ2) in
    [(H, Σ, e')]
  | s_expr_and (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) in
    [(H, Σ, e')]
  | s_expr_and (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_and (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_and (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_and (s_expr_val σ1) (s_expr_val σ2) =>
    let e' := s_expr_val (s_val_and σ1 σ2) in
    [(H, Σ, e')]
  | s_expr_or (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) in
    [(H, Σ, e')]
  | s_expr_or (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) in
    [(H, Σ, e')]
  | s_expr_or (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) in
    [(H, Σ, e')]
  | s_expr_or (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_or (s_expr_val σ1) (s_expr_val σ2) =>
    let e' := s_expr_val (s_val_or σ1 σ2) in
    [(H, Σ, e')]
  | s_expr_not (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_not (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) in
    [(H, Σ, e')]
  | s_expr_not (s_expr_val σ1) =>
    let e' := s_expr_val (s_val_not σ1) in
    [(H, Σ, e')]
  | s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n1)))) (s_expr_val (s_val_prim_c (s_prim_c_int (s_int_l n2)))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool (if Nat.eqb n1 n2 then s_bool_true else s_bool_false))) in
    [(H, Σ, e')]
  | s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)))
  | s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)))
  | s_expr_eq (s_expr_val (s_val_ref_c s_ref_c_null)) (s_expr_val (s_val_ref_c s_ref_c_null)) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)) in
    [(H, Σ, e')]
  | s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)))
  | s_expr_eq (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true)))
  | s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_loc _))) (s_expr_val (s_val_ref_c s_ref_c_null))
  | s_expr_eq (s_expr_val (s_val_ref_c s_ref_c_null)) (s_expr_val (s_val_ref_c (s_ref_c_loc _))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_loc (s_loc_l n1)))) (s_expr_val (s_val_ref_c (s_ref_c_loc (s_loc_l n2)))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool (if Nat.eqb n1 n2 then s_bool_true else s_bool_false))) in
    [(H, Σ, e')]
  | s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_loc l))) (s_expr_val (s_val_ref_c (s_ref_c_symb s))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_symb s))) (s_expr_val (s_val_ref_c (s_ref_c_loc l))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_eq (s_expr_val (s_val_ref_c (s_ref_c_loc l))) (s_expr_val (s_val_ite σ1 σ2 σ3)) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_eq (s_expr_val (s_val_ite σ1 σ2 σ3)) (s_expr_val (s_val_ref_c (s_ref_c_loc l))) =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_eq (s_expr_val σ1) (s_expr_val σ2) =>
    let e' := s_expr_val (s_val_eq σ1 σ2) in
    [(H, Σ, e')]
  | s_expr_instanceof (s_expr_val (s_val_ref_c s_ref_c_null)) c =>
    let e' := s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false)) in
    [(H, Σ, e')]
  | s_expr_instanceof (s_expr_val (s_val_ref_c (s_ref_c_loc (s_loc_l n)))) c =>
    let l := s_ref_c_loc (s_loc_l n) in
    match obj_class_at H l with
    | Some c' => 
      let e' := s_expr_val (s_val_prim_c (s_prim_c_bool (if subclass_c P c' c then s_bool_true else s_bool_false))) in
      [(H, Σ, e')]
    | _ => []
    end
  | s_expr_instanceof (s_expr_val (s_val_ref_c (s_ref_c_symb s))) c =>
    let Y := s_ref_c_symb s in
    let e' := s_expr_val (s_val_subtype (s_val_ref_c Y) (s_ty_class c)) in
    [(H, Σ, e')]
  | s_expr_if (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_true))) e1 e2 =>
    [(H, Σ, e1)]
  | s_expr_if (s_expr_val (s_val_prim_c (s_prim_c_bool s_bool_false))) e1 e2 =>
    [(H, Σ, e2)]
  | s_expr_if (s_expr_val σ) e1 e2 =>
    let Σ1' := Σ ++ [σ] in
    let Σ2' := Σ ++ [s_val_not σ] in
    [(H, Σ1', e1) ; (H, Σ2', e2)]
  | s_expr_invoke (s_expr_val (s_val_ref_c (s_ref_c_loc (s_loc_l n)))) m (s_expr_val σ) =>
    let l := s_ref_c_loc (s_loc_l n) in
    match obj_at H l, obj_class_at H l with
    | Some o, Some c => match method_provider P m c with
      | Some c' => match mdecl P c' m with 
        | Some (s_dc_m_l t1 m (s_dc_v_l t2 xM) eM) =>
          let e' := repl_var (repl_var eM "this" (s_expr_val (s_val_ref_c l))) xM (s_expr_val σ) in
          [(H, Σ, e')]
        | _ => []
        end
      | _ => []
      end
    | _, _ => []
    end
  | s_expr_invoke (s_expr_val (s_val_ref_c (s_ref_c_symb s))) m (s_expr_val σ) =>
    let Y := s_ref_c_symb s in
    let cs' := implementors P m in
    concat (List.map (fun c' =>
      match mdecl P c' m with
      | Some (s_dc_m_l t1 m (s_dc_v_l t2 xM) eM) =>
        let O := overriders P m c' in
        let cl1 := s_val_not (s_val_eq (s_val_ref_c Y) (s_val_ref_c s_ref_c_null)) in (*TODO redundant? *)
        let cl2 := s_val_subtype (s_val_ref_c Y) (s_ty_class c') in
        let Σ' := Σ ++ [cl1 ; cl2] ++ List.map (fun c => s_val_not (s_val_subtype (s_val_ref_c Y) (s_ty_class c))) O in
        let e' := repl_var (repl_var eM "this" (s_expr_val (s_val_ref_c Y))) xM (s_expr_val σ) in
        [(H, Σ', e')]
      | _ => []
      end) cs')
  | s_expr_invoke (s_expr_val (s_val_ite σ σ1 σ2)) m (s_expr_val σ') =>
    let e1 := s_expr_invoke (s_expr_val σ1) m (s_expr_val σ') in
    let e2 := s_expr_invoke (s_expr_val σ2) m (s_expr_val σ') in
    List.map (fun x : heap * path_condition * s_expr => 
      match x with
      | (_, Σ1', e1') => let Σ' := Σ1' ++ [σ] in
        (H, Σ', e1')
      end
    ) (cstep_c_fp P H Σ e1) ++
    List.map (fun x : heap * path_condition * s_expr =>
      match x with
      | (_, Σ2', e2') => let Σ' := Σ2' ++ [s_val_not σ] in
        (H, Σ', e2')
      end
    ) (cstep_c_fp P H Σ e2)
  | s_expr_getfield e1 f => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_getfield e1' f)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_putfield (s_expr_val σ) f e1 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_putfield (s_expr_val σ) f e1')
    end) (cstep_c_fp P H Σ e1)
  | s_expr_putfield e1 f e2 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_putfield e1' f e2)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_let xN e1 e2 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_let xN e1' e2)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_add (s_expr_val σ) e1 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_add (s_expr_val σ) e1')
    end) (cstep_c_fp P H Σ e1)
  | s_expr_add e1 e2 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_add e1' e2)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_sub (s_expr_val σ) e1 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_sub (s_expr_val σ) e1')
    end) (cstep_c_fp P H Σ e1)
  | s_expr_sub e1 e2 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_sub e1' e2)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_lt (s_expr_val σ) e1 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_lt (s_expr_val σ) e1')
    end) (cstep_c_fp P H Σ e1)
  | s_expr_lt e1 e2 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_lt e1' e2)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_and (s_expr_val σ) e1 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_and (s_expr_val σ) e1')
    end) (cstep_c_fp P H Σ e1)
  | s_expr_and e1 e2 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_and e1' e2)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_or (s_expr_val σ) e1 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_or (s_expr_val σ) e1')
    end) (cstep_c_fp P H Σ e1)
  | s_expr_or e1 e2 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_or e1' e2)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_not e1 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_not e1')
    end) (cstep_c_fp P H Σ e1)
  | s_expr_eq (s_expr_val σ) e1 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_eq (s_expr_val σ) e1')
    end) (cstep_c_fp P H Σ e1)
  | s_expr_eq e1 e2 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_eq e1' e2)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_instanceof e1 c => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_instanceof e1' c)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_if e1 e2 e3 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_if e1' e2 e3)
    end) (cstep_c_fp P H Σ e1)
  | s_expr_invoke (s_expr_val σ) m e1 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_invoke (s_expr_val σ) m e1')
    end) (cstep_c_fp P H Σ e1)
  | s_expr_invoke e1 m e2 => List.map (fun x : heap * path_condition * s_expr =>
    match x with
    | (H', Σ', e1') => (H', Σ', s_expr_invoke e1' m e2)
    end) (cstep_c_fp P H Σ e1)
  | _ => []
  end.
Next Obligation.
  unfold lt. unfold height_s_expr. unfold height_s_val. fold height_s_val. apply le_n_S. apply le_n_S.
  assert (height_s_val σ1 <= Nat.max (height_s_val σ1) (height_s_val σ2)) by apply maxl. 
  assert (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) by apply maxr.
  assert ((height_s_val σ1 <=
  Nat.max (height_s_val σ1) (height_s_val σ2)) -> (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) ->
  height_s_val σ1 <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2)))
  by apply Nat.le_trans.
  apply H2 in H0. assumption. assumption.
Qed.
Next Obligation.
  unfold lt. unfold height_s_expr. unfold height_s_val. fold height_s_val. apply le_n_S. apply le_n_S.
  assert (height_s_val σ2 <= Nat.max (height_s_val σ1) (height_s_val σ2)) by apply maxr. 
  assert (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) by apply maxr.
  assert ((height_s_val σ2 <= Nat.max (height_s_val σ1) (height_s_val σ2)) -> 
  (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) ->
  height_s_val σ2 <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2)))
  by apply Nat.le_trans.
  apply H2 in H0. assumption. assumption.
Qed.
Next Obligation.
  unfold lt. unfold height_s_expr. unfold height_s_val. fold height_s_val. rewrite <- add_l. rewrite <- add_l. apply le_n_S. apply le_n_S. apply leq_canc. 
  assert (height_s_val σ1 <= Nat.max (height_s_val σ1) (height_s_val σ2)) by apply maxl. 
  assert (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) by apply maxr.
  assert ((height_s_val σ1 <= Nat.max (height_s_val σ1) (height_s_val σ2)) -> 
  (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) ->
  height_s_val σ1 <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2)))
  by apply Nat.le_trans.
  apply H2 in H0. assumption. assumption.
Qed.
Next Obligation.
  unfold lt. unfold height_s_expr. unfold height_s_val. fold height_s_val. rewrite <- add_l. rewrite <- add_l. apply le_n_S. apply le_n_S. apply leq_canc. 
  assert (height_s_val σ2 <= Nat.max (height_s_val σ1) (height_s_val σ2)) by apply maxr. 
  assert (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) by apply maxr.
  assert ((height_s_val σ2 <= Nat.max (height_s_val σ1) (height_s_val σ2)) -> 
  (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) ->
  height_s_val σ2 <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2)))
  by apply Nat.le_trans.
  apply H2 in H0. assumption. assumption.
Qed.
Next Obligation.
  unfold lt. unfold height_s_expr. unfold height_s_val. fold height_s_val. rewrite <- add_l. rewrite <- add_l. apply le_n_S. apply le_n_S. apply leq_canc. 
  assert (height_s_val σ1 <= Nat.max (height_s_val σ1) (height_s_val σ2)) by apply maxl. 
  assert (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) by apply maxr.
  assert ((height_s_val σ1 <= Nat.max (height_s_val σ1) (height_s_val σ2)) -> 
  (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) ->
  height_s_val σ1 <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2)))
  by apply Nat.le_trans.
  apply H2 in H0. assumption. assumption.
Qed.
Next Obligation.
  unfold lt. unfold height_s_expr. unfold height_s_val. fold height_s_val. rewrite <- add_l. rewrite <- add_l. apply le_n_S. apply le_n_S. apply leq_canc. 
  assert (height_s_val σ2 <= Nat.max (height_s_val σ1) (height_s_val σ2)) by apply maxr. 
  assert (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) by apply maxr.
  assert ((height_s_val σ2 <= Nat.max (height_s_val σ1) (height_s_val σ2)) -> 
  (Nat.max (height_s_val σ1) (height_s_val σ2) <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2))) ->
  height_s_val σ2 <= Nat.max (height_s_val σ) (Nat.max (height_s_val σ1) (height_s_val σ2)))
  by apply Nat.le_trans.
  apply H2 in H0. assumption. assumption.
Qed.
Solve All Obligations with sauto.

Let cstep_c (J : config) : list config :=
  let (AA, e) := J in 
  let (BB, Σ) := AA in
  let (P, H) := BB in
  let next := cstep_c_fp P H Σ e in
  List.map (fun x => match x with 
  | (H', Σ', e') => (P, H', Σ', e')
  end) next.

(* The step function *)

Definition step_c (J : config) : list config :=
  let (AA, e) := J in 
  let (BB, Σ) := AA in
  let (P, H) := BB in
  match rstep_c_star P H Σ e with
  | None => []
  | Some (H', Σ') => cstep_c (P, H', Σ', e)
  end.

Definition is_leaf (J : config) : bool :=
  match step_c J with
  | [] => true
  | _ => false
  end.

End StepDefs.

(************ Full computation of a program ************)

(* Corecursive function that calculates the 
   computation of a program *)

Section ComputeDefs.

Let CoFixpoint do_compute (Js : list config) : computation :=
  Cons Js (do_compute (concat (List.map step_c Js))).

Definition compute (P : s_prg) : computation :=
  let J0 := config_initial P in
  do_compute [J0].

End ComputeDefs.

(* Takes the nth step of a computation *)
Definition step_at (P : s_prg) (n : nat) : list config :=
  Str_nth n (compute P).
