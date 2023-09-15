From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Program.Wf.
From Hammer Require Import Tactics.
From POSE Require Import Aux.
From POSE Require Import Syntax.
From POSE Require Import SemanticsTypes.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(********* Auxiliary definitions in the operational semantics *********)

(* Assume (declarative and computable). *)

Section AssumeDefs.
  
Let Fixpoint assume_fp (Helts : list (s_ref_c * object)) (s : s_symb) (f : string) (σPart : s_val) (σ : s_val) : Prop :=
  match Helts with
  | [] => σ = σPart
  | (s_ref_c_symb s', o') :: other_Helts => if s_symb_eqb s s' then assume_fp other_Helts s f σPart σ
    else match get o' f with
    | None => assume_fp other_Helts s f σPart σ
    | Some σ' => if s_val_eqb σ' s_val_unassumed then
                 assume_fp other_Helts s f σPart σ
                 else
                 assume_fp other_Helts s f (s_val_ite (s_val_eq (s_val_ref_c (s_ref_c_symb s)) (s_val_ref_c (s_ref_c_symb s'))) σ' σPart) σ
    end
  | _ :: other_Helts => assume_fp other_Helts s f σPart σ
  end.

Definition assume_ref (H : heap) (Y : s_ref_c) (f : string) (σ : s_val) (Z : s_ref_c) : Prop := 
  match Y with
  | s_ref_c_symb s => if MapRefC.mem Y H then
    let s' := match s with
              | s_symb_expr n => s_symb_fld n [f]
              | s_symb_fld n l => s_symb_fld n (l ++ [f])
              end in                              
    Z = s_ref_c_symb s' /\ assume_fp (MapRefC.elements H) s f (s_val_ref_c Z) σ
    else False
  | _ => False
  end.

Definition assume_num (H : heap) (Y : s_ref_c) (f : string) (σ : s_val) (Z : s_prim_c) : Prop := 
  match Y with
  | s_ref_c_symb s => if MapRefC.mem Y H then
    let s' := match s with
              | s_symb_expr n => s_symb_fld n [f]
              | s_symb_fld n l => s_symb_fld n (l ++ [f])
              end in                              
    Z = s_prim_c_symb s' /\ assume_fp (MapRefC.elements H) s f (s_val_prim_c Z) σ
    else False
  | _ => False
  end.

Let Fixpoint assume_c_fp (Helts : list (s_ref_c * object)) (s : s_symb) (f : string) (σPart : s_val) : option s_val :=
  match Helts with
  | [] => Some σPart
  | (s_ref_c_symb s', o') :: other_Helts => if s_symb_eqb s s' then assume_c_fp other_Helts s f σPart
    else match get o' f with
    | None => assume_c_fp other_Helts s f σPart
    | Some σ' => if s_val_eqb σ' s_val_unassumed then
                 assume_c_fp other_Helts s f σPart
                 else
                 assume_c_fp other_Helts s f (s_val_ite (s_val_eq (s_val_ref_c (s_ref_c_symb s)) (s_val_ref_c (s_ref_c_symb s'))) σ' σPart)
    end
  | _ :: other_Helts => assume_c_fp other_Helts s f σPart
  end.

Definition assume_c_ref (H : heap) (Y : s_ref_c) (f : string) : option (s_val * s_ref_c) := 
  match Y with
  | s_ref_c_symb s => if MapRefC.mem Y H then
    let s' := match s with
              | s_symb_expr n => s_symb_fld n [f]
              | s_symb_fld n l => s_symb_fld n (l ++ [f])
              end in                              
    let Z := s_ref_c_symb s' in
    option_map (fun σ => (σ, Z)) (assume_c_fp (MapRefC.elements H) s f (s_val_ref_c Z))
    else None
  | _ => None (* error: cannot assume over a concrete reference/object *)
  end.

Definition assume_c_num (H : heap) (Y : s_ref_c) (f : string) : option (s_val * s_prim_c) :=
  match Y with
  | s_ref_c_symb s => if MapRefC.mem Y H then
    let s' := match s with
              | s_symb_expr n => s_symb_fld n [f]
              | s_symb_fld n l => s_symb_fld n (l ++ [f])
              end in                              
    let Z := s_prim_c_symb s' in
    option_map (fun σ => (σ, Z)) (assume_c_fp (MapRefC.elements H) s f (s_val_prim_c Z))
    else None
  | _ => None (* error: cannot assume over a concrete reference/object *)
  end.

End AssumeDefs.

(* Update (declarative and computable). *)

Section UpdateDefs.

Definition update (f : string) (Y : s_ref_c) (σ' : s_val) (H HRefined : heap) : Prop :=
  forall u' : s_ref_c, (MapRefC.In u' H <-> MapRefC.In u' H) /\
  (MapRefC.In u' H -> 
  match obj_at H u', obj_at HRefined u' with
  | Some o', Some oRefined' => match u' with
    | s_ref_c_symb s' =>
      let Y' := s_ref_c_symb s' in
      (exists σ, get o' f = Some σ /\
      (Y <> Y' /\ σ <> s_val_unassumed -> σ <> σ' -> oRefined' = upd_obj o' f (s_val_ite (s_val_eq (s_val_ref_c Y) (s_val_ref_c Y')) σ' σ)) /\
      ((Y = Y' \/ σ = s_val_unassumed \/ σ = σ') -> oRefined' = o')) /\
      (get o' f = None -> oRefined' = o')
    | _ => oRefined' = o'
    end
  | _, _ => False
  end).

Let Fixpoint update_c_fp (f : string) (Y : s_ref_c) (σ' : s_val) (Helts : list (s_ref_c * object)) : heap :=
  match Helts with
  | [] => H0
  | (u', o') :: other_Helts =>
    let other_H := update_c_fp f Y σ' other_Helts in
    match u' with
    | s_ref_c_symb s' =>
      let Y' := s_ref_c_symb s' in
      match get o' f with
      | Some σ =>                   
        if s_ref_c_eqb Y Y' || s_val_eqb σ s_val_unassumed || s_val_eqb σ σ' then
        MapRefC.add u' o' other_H
        else
        let oRefined' := upd_obj o' f (s_val_ite (s_val_eq (s_val_ref_c Y) (s_val_ref_c Y')) σ' σ) in
        MapRefC.add u' oRefined' other_H
      | None => MapRefC.add u' o' other_H
      end
    | _ => MapRefC.add u' o' other_H
    end
  end.

Definition update_c (f : string) (Y : s_ref_c) (σ : s_val) (H : heap): heap :=
  update_c_fp f Y σ (MapRefC.elements H).

End UpdateDefs.

(* Merge *)

Section MergeDefs.
  
Definition merge (H1' H2' H' H : heap) (f : string) (σ : s_val) : Prop :=
  (forall u : s_ref_c,
      (MapRefC.In u H -> (MapRefC.In u H1' /\ MapRefC.In u H2')) /\
      ((MapRefC.In u H1' \/ MapRefC.In u H2') <-> MapRefC.In u H') /\
      (obj_at H1' u = obj_at H2' u -> obj_at H' u = obj_at H1' u) /\
      (forall o1' o2', has_obj H1' u o1' -> has_obj H2' u o2' -> o1' <> o2' -> exists σ1 σ2, (o1' = upd_obj o2' f σ1 /\ o2' = upd_obj o1' f σ2 /\ has_obj H' u (upd_obj o1' f (s_val_ite σ σ1 σ2)))) /\
      (forall o1', has_obj H1' u o1' -> obj_at H2' u = None -> exists n l σ1 Z, (get o1' f = Some σ1 /\ ((u = s_ref_c_symb (s_symb_expr n) /\ l = []) \/ (u = s_ref_c_symb (s_symb_fld n l))) /\ has_obj H' u (upd_obj o1' f (s_val_ite σ σ1 Z)) /\ Z = s_val_ref_c (s_ref_c_symb (s_symb_fld n (l ++ [f]))))) /\
      (forall o2', has_obj H2' u o2' -> obj_at H1' u = None -> exists n l σ2 Z, (get o2' f = Some σ2 /\ ((u = s_ref_c_symb (s_symb_expr n) /\ l = []) \/ (u = s_ref_c_symb (s_symb_fld n l))) /\ has_obj H' u (upd_obj o2' f (s_val_ite σ Z σ2)) /\ Z = s_val_ref_c (s_ref_c_symb (s_symb_fld n (l ++ [f])))))).

(* direct: if true, and H2 has a same object, merge the two objects and add 
   it to H1; if false, and H2 has a same object, don't add it to H1 *)
Fixpoint merge_c_aux (H1elts : list (s_ref_c * object)) (H2 : heap) (f : string) (σ : s_val) (direct : bool) : option heap :=
  match H1elts with
  | [] => Some H0
  | (u, o1) :: other_H1elts =>
    let other_H1 := merge_c_aux other_H1elts H2 f σ direct in
    match obj_at H2 u with
    (* H2 has an object at u *)
    | Some o2 => if direct && object_eqb o1 o2 then
      option_map (fun H' => repl_obj H' u o1) other_H1
      else if direct && negb (object_eqb o1 o2) then
      match get o1 f, get o2 f with
      | Some σ1, Some σ2 => if object_eqb o1 (upd_obj o2 f σ1) then
          let o' := upd_obj o1 f (s_val_ite σ σ1 σ2) in
          option_map (fun H' => repl_obj H' u o') other_H1
        else None (* unexpected: differring objects o1 and o2, but they do not differ by f (one object is not obtained by replacing the content of field f of the other) *)
      | _, _ => None (* unexpected: differring objects o1 and o2, but they do not differ by f (one object has the field, the other object has it not) *)
      end
      else other_H1
    (* H2 has no object at u *)
    | None => match get o1 f with
      | Some σ1 => match u with
        | s_ref_c_symb s => 
          let s' := match s with
                    | s_symb_expr n => s_symb_fld n [f]
                    | s_symb_fld n l => s_symb_fld n (l ++ [f])
                    end in                              
          let Z := s_val_ref_c (s_ref_c_symb s') in
          let o' := if direct then upd_obj o1 f (s_val_ite σ σ1 Z) else upd_obj o1 f (s_val_ite σ Z σ1) in
          option_map (fun H' => repl_obj H' u o') other_H1
        | _ => None (* unexpected: if u has no corresponding object in H2, then o1 must be a symbolic object and u must be a symbolic reference *)
        end
      | _ => None (* unexpected: if u has no corresponding object in H2 then o1 must have field f; this because the o1 was introduced by a refinement transition *)
      end
    end
  end.

Definition merge_c (H1' H2' : heap) (f : string) (σ : s_val) : option heap :=
  match merge_c_aux (MapRefC.elements H1') H2' f σ true,
  merge_c_aux (MapRefC.elements H2') H1' f σ false with
  | Some H1'', Some H2'' =>
    Some (MapRefC.map2 (fun x y => match x, y with
    | Some o, None => Some o
    | None, Some o => Some o
    | _, _ => None
    end) H1'' H2'')
  | _, _ => None
  end.

Let Fixpoint merge_clauses_aux (H1elts : list (s_ref_c * object)) (H2 : heap) (f : string) : option path_condition :=
  match H1elts with
  | [] => Some []
  | (u, o) :: other_H1elts =>
    let other_H1 := merge_clauses_aux other_H1elts H2 f in
    match obj_at H2 u with
    | None => match u with 
      | s_ref_c_symb s =>
        let s' := match s with
                   | s_symb_expr n => s_symb_fld n [f]
                   | s_symb_fld n l => s_symb_fld n (l ++ [f])
                   end in                              
        option_map (fun Σ => (s_val_field s f s') :: Σ) other_H1
      | _ => None
      end
    | _ => other_H1
    end
  end.

Definition merge_clauses (H1' H2' : heap) (f : string) : option path_condition :=
  match merge_clauses_aux (MapRefC.elements H1') H2' f, merge_clauses_aux (MapRefC.elements H2') H1' f with
  | Some Σ1, Some Σ2 => Some (Σ1 ++ Σ2)
  | _, _ => None
  end.

Definition height_2pc (Σ1 Σ2 : path_condition) : nat :=
  (length Σ1) + (length Σ2).

Program Fixpoint merge_pc (σ : s_val) (Σ1 Σ2 : path_condition) {measure (height_2pc Σ1 Σ2)} : path_condition :=
  match Σ1, Σ2 with
  | σ1 :: Σ1', σ2 :: Σ2' => if s_val_eqb σ1 σ2 then σ1 :: (merge_pc σ Σ1' Σ2') else (s_val_or (s_val_not σ) σ1) :: (merge_pc σ Σ1' Σ2)
  | [], σ2 :: Σ2' => (s_val_or σ σ2) :: (merge_pc σ [] Σ2')
  | σ1 :: Σ1', [] => (s_val_or (s_val_not σ) σ1) :: (merge_pc σ Σ1' [])
  | [], [] => []
  end.
Next Obligation.
  unfold height_2pc. assert (Datatypes.length (σ1 :: Σ1') = S (Datatypes.length Σ1')) by sauto. rewrite -> H.
  assert (Datatypes.length (σ2 :: Σ2') = S (Datatypes.length Σ2')) by sauto. rewrite -> H0. sauto.
Qed.

End MergeDefs.
