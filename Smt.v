From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From POSE Require Import Aux.
From POSE Require Import Prettyprint.
From POSE Require Import Syntax.
From POSE Require Import SemanticsTypes.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(************************ Emitting SMTLIB ***********************)
Definition LF := from_string (string_of_list_ascii [ascii_of_nat 10]).

Fixpoint class_sibling_number_aux (P : s_prg) (Cs : list s_dc_c) (C : s_dc_c) (c_sup : string) (n: nat) : option nat :=
  match Cs with
  | [] => None
  | C' :: Cs' => if String.eqb (class_name C) (class_name C') then Some n else if String.eqb c_sup (superclass_name C') then class_sibling_number_aux P Cs' C c_sup (Nat.succ n) else class_sibling_number_aux P Cs' C c_sup n
  end.

Definition class_sibling_number (P : s_prg) (C : s_dc_c) : option nat :=
  class_sibling_number_aux P (classes P) C (superclass_name C) 0.

Fixpoint class_to_list_aux (P : s_prg) (C : s_dc_c) (depth : nat) : list nat :=
  match depth with
  | 0 => []
  | S depth' => let c_sup := superclass_name C in
    if String.eqb "" c_sup then [0] else match cdecl P c_sup with
    | None => []
    | Some C_sup => match (class_sibling_number P C) with
      | None => []
      | Some n => (class_to_list_aux P C_sup depth') ++ [n]
      end
    end
  end.

Definition class_to_list (P : s_prg) (C : s_dc_c) : list nat :=
  class_to_list_aux P C 1000. (*TODO dirty escamotage*)

Fixpoint list_nat_to_dsmt (l : list nat) : dstring :=
  match l with
  | [] => from_string "nil"
  | n :: ns => append (append (append (append (from_string "(insert ") (nat_to_dstr n)) (from_string " ")) (list_nat_to_dsmt ns)) (from_string ")")
  end.

Definition ref_c_to_dsmt (u : s_ref_c) : dstring :=
  match u with
  | s_ref_c_null => from_string "_null"
  | s_ref_c_loc l => loc_to_dstr l
  | s_ref_c_symb s => append (from_string "Y") (symb_to_dstr s)
  end.

Definition type_to_dsmt (t : s_ty) : dstring :=
  match t with
  | s_ty_bool => from_string "Bool"
  | s_ty_int => from_string "Int"
  | s_ty_class _ => from_string "SRef"
  end.

Definition field_to_dsmt (F : s_dc_v) : dstring :=
  append (append (append (append (append (from_string "(declare-fun ") (from_string (field_name F))) (from_string " (SRef) ")) (type_to_dsmt (field_type F))) (from_string ")")) LF.

Definition class_to_dsmt (P : s_prg) (C : s_dc_c) : dstring :=
  append (append (append (append (append (append (from_string "(define-fun ") (from_string (class_name C))) (from_string " () SCl ")) (list_nat_to_dsmt (class_to_list P C))) (from_string ")")) LF) (dconcat (from_string "") (List.map field_to_dsmt (fields C))).

Definition smt_decls (P : s_prg) : dstring :=
  append (append (append (append (append (append 
  (append (append (append (append (append (append 
  (from_string "(define-sort SCl () (List Int)) ;the sort of classes") LF) 
  (from_string "(define-fun-rec subclass ((x SCl) (y SCl)) Bool")) LF) 
  (from_string "(ite (= y nil) true (ite (= x nil) false (ite (= (head x) (head y)) (subclass (tail x) (tail y)) false))))")) LF) 
  (from_string "(declare-sort SRef) ;the sort of references")) LF) 
  (from_string "(declare-fun classOf (SRef) SCl)")) LF) 
  (from_string "(declare-fun _null () SRef)")) LF) 
  (dconcat (from_string "") (List.map (class_to_dsmt P) (classes P))).

Fixpoint value_to_dsmt (σ : s_val) : dstring :=
  match σ with
  | s_val_prim_c p => prim_c_to_dstr p
  | s_val_ref_c u => ref_c_to_dsmt u
  | s_val_add σ1 σ2 => append (append (append (append (from_string "(+ ") (value_to_dsmt σ1)) (from_string " ")) (value_to_dsmt σ2)) (from_string ")")
  | s_val_lt σ1 σ2 => append (append (append (append (from_string "(< ") (value_to_dsmt σ1)) (from_string " ")) (value_to_dsmt σ2)) (from_string ")")
  | s_val_eq σ1 σ2 => append (append (append (append (from_string "(= ") (value_to_dsmt σ1)) (from_string " ")) (value_to_dsmt σ2)) (from_string ")")
  | s_val_ite σ1 σ2 σ3 => append (append (append (append (append (append (from_string "(ite ") (value_to_dsmt σ1)) (from_string " ")) (value_to_dsmt σ2)) (from_string " ")) (value_to_dsmt σ3)) (from_string ")")
  | _ => (from_string "")
  end.

Definition clause_to_dsmt (P : s_prg) (σ : s_val) (positive : bool) : dstring :=
  match σ with
  | s_val_prim_c p => prim_c_to_dstr p
  | s_val_ref_c u => ref_c_to_dsmt u
  | s_val_lt σ1 σ2 => append (append (append (append (append (append (append (append (from_string "(assert ") (if positive then (from_string "") else (from_string "(not "))) (from_string "(< ")) (value_to_dsmt σ1)) (from_string " ")) (value_to_dsmt σ2)) (from_string ")")) (if positive then (from_string "") else (from_string ")"))) (from_string ")")
  | s_val_eq σ1 σ2 => append (append (append (append (append (append (append (append (from_string "(assert ") (if positive then (from_string "") else (from_string "(not "))) (from_string "(= ")) (value_to_dsmt σ1)) (from_string " ")) (value_to_dsmt σ2)) (from_string ")")) (if positive then (from_string "") else (from_string ")"))) (from_string ")")
  | s_val_subtype σ t => match t with
    | s_ty_class c => append (append (append (append (append (append (append (append (from_string "(assert ") (if positive then (from_string "") else (from_string "(not "))) (from_string "(subclass (classOf ")) (value_to_dsmt σ)) (from_string ") ")) (from_string c)) (from_string ")")) (if positive then (from_string "") else (from_string ")"))) (from_string ")")
    | _ => from_string ""
    end
  | s_val_field s1 f s2 => append (append (append (append (append (append (append (append (append (append (from_string "(assert ") (if positive then (from_string "") else (from_string "(not "))) (from_string "(= (")) (from_string f)) (from_string " ")) (ref_c_to_dsmt (s_ref_c_symb s1))) (from_string ") ")) 
       (match class_with_field P f with
        | Some C =>
          match fdecl C f with
          | Some F =>              
            let t := field_type F in
            if is_type_primitive t then
              prim_c_to_dstr (s_prim_c_symb s2)
            else
              ref_c_to_dsmt (s_ref_c_symb s2)
          | _ => from_string "" (* error (internal): class C' has no field f *)
          end         
        | _ => from_string "" (* error: no class exists with field f *)
        end)) (from_string ")")) (if positive then (from_string "") else (from_string ")"))) (from_string ")")
  | s_val_ite σ1 σ2 σ3 => append (append (append (append (append (append (append (append (append (append (from_string "(assert ") (if positive then (from_string "") else (from_string "(not "))) (from_string "(ite ")) (value_to_dsmt σ1)) (from_string " ")) (value_to_dsmt σ2)) (from_string " ")) (value_to_dsmt σ3)) (from_string ")")) (if positive then (from_string "") else (from_string ")"))) (from_string ")")
  | _ => from_string ""
  end.

Fixpoint clauses_to_dsmt (P : s_prg) (Σ : path_condition) : dstring :=
  match Σ with
  | [] => from_string ""
  | cl :: Σ' => append (match cl with
    | clause_pos σ => append (clause_to_dsmt P σ true) LF 
    | clause_neg σ => append (clause_to_dsmt P σ false) LF 
    end) (clauses_to_dsmt P Σ')
  end.

Fixpoint add_vars (ss : SetSymb.t) (σ : s_val) : SetSymb.t :=
  match σ with
  | s_val_prim_c p => match p with
    | s_prim_c_symb s => SetSymb.add s ss
    | _ => ss
    end
  | s_val_ref_c u => match u with
    | s_ref_c_symb s => SetSymb.add s ss
    | _ => ss
    end
  | s_val_lt σ1 σ2 => add_vars (add_vars ss σ1) σ2
  | s_val_eq σ1 σ2 => add_vars (add_vars ss σ1) σ2
  | s_val_subtype σ t => add_vars ss σ
  | s_val_field s1 f s2 => SetSymb.add s2 (SetSymb.add s1 ss)
  | s_val_ite σ1 σ2 σ3 => add_vars (add_vars (add_vars ss σ1) σ2) σ3
  | _ => ss
  end.

Fixpoint declare_vars_clause (P : s_prg) (σ : s_val) (ss : SetSymb.t) : dstring :=
  match σ with
  | s_val_prim_c p => match p with
    | s_prim_c_symb s => if SetSymb.mem s ss then (from_string "") else append (append (append (from_string "(declare-fun ") (prim_c_to_dstr (s_prim_c_symb s))) (from_string " () Int)")) LF
    | _ => from_string ""
    end
  | s_val_ref_c u => match u with
    | s_ref_c_symb s => if SetSymb.mem s ss then (from_string "") else append (append (append (from_string "(declare-fun ") (ref_c_to_dsmt (s_ref_c_symb s))) (from_string " () SRef)")) LF
    | _ => from_string ""
    end
  | s_val_lt σ1 σ2 => append (declare_vars_clause P σ1 ss) (declare_vars_clause P σ2 (add_vars ss σ1))
  | s_val_eq σ1 σ2 => append (declare_vars_clause P σ1 ss) (declare_vars_clause P σ2 (add_vars ss σ1))
  | s_val_subtype σ t => declare_vars_clause P σ ss
  | s_val_field s1 f s2 => append (if SetSymb.mem s1 ss then (from_string "") else append (append (append (from_string "(declare-fun ") (ref_c_to_dsmt (s_ref_c_symb s1))) (from_string " () SRef)")) LF) (if SetSymb.mem s2 ss then (from_string "") else
     (match class_with_field P f with
        | Some C =>
          match fdecl C f with
          | Some F =>              
            let t := field_type F in
            if is_type_primitive t then
              append (append (append (from_string "(declare-fun ") (prim_c_to_dstr (s_prim_c_symb s2))) (from_string " () Int)")) LF
            else
              append (append (append (from_string "(declare-fun ") (ref_c_to_dsmt (s_ref_c_symb s2))) (from_string " () SRef)")) LF
          | _ => from_string "" (* error (internal): class C' has no field f *)
          end         
        | _ => from_string "" (* error: no class exists with field f *)
        end))
  | s_val_ite σ1 σ2 σ3 => append (append (declare_vars_clause P σ1 ss) (declare_vars_clause P σ2 (add_vars ss σ1))) (declare_vars_clause P σ3 (add_vars (add_vars ss σ1) σ2))
  | _ => from_string ""
  end.

Fixpoint declare_vars (P : s_prg) (Σ : path_condition) (ss : SetSymb.t) : dstring :=
  match Σ with
  | [] => from_string ""
  | cl :: Σ' => match cl with
    | clause_pos σ => append (declare_vars_clause P σ ss) (declare_vars P Σ' (add_vars ss σ))
    | clause_neg σ => append (declare_vars_clause P σ ss) (declare_vars P Σ' (add_vars ss σ))
    end
  end.

Definition path_condition_to_dsmt (P : s_prg) (Σ : path_condition) : dstring :=
  append (declare_vars P Σ SetSymb.empty) (clauses_to_dsmt P Σ).

Definition config_to_dsmt (J : config) : dstring :=
  let (AA, _) := J in 
  let (BB, Σ) := AA in
  let (P, _) := BB in
  append (smt_decls P) (path_condition_to_dsmt P Σ).

Definition step_to_dsmt (Js : list config) : list dstring :=
   map config_to_dsmt Js.

(* Direct translation to string: use only with small configs. *)

Definition config_to_smt (J : config) : string :=
  to_string (config_to_dsmt J).

Definition step_to_smt (Js : list config) : list string :=
   map config_to_smt Js.
