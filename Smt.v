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
Definition LF := string_of_list_ascii [ascii_of_nat 10].

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

Fixpoint smt_list_nat (l : list nat) : string :=
  match l with
  | [] => "nil"
  | n :: ns => "(insert " ++ nat_to_str n ++ " " ++ smt_list_nat ns ++ ")"
  end.

Definition ref_c_to_smt (u : s_ref_c) : string :=
  match u with
  | s_ref_c_null => "_null"
  | s_ref_c_loc l => loc_to_str l
  | s_ref_c_symb s => "Y" ++  symb_to_str s
  end.

Definition type_to_smt (t : s_ty) : string :=
  match t with
  | s_ty_bool => "Bool"
  | s_ty_int => "Int"
  | s_ty_class _ => "SRef"
  end.

Definition field_to_smt (F : s_dc_v) : string :=
  "(declare-fun " ++ field_name F ++ " (SRef) " ++ type_to_smt (field_type F) ++ ")" ++ LF.

Definition class_to_smt (P : s_prg) (C : s_dc_c) : string :=
  "(define-fun " ++ class_name C ++ " () SCl " ++ smt_list_nat (class_to_list P C) ++ ")" ++ LF ++ (String.concat "" (List.map field_to_smt (fields C))).

Definition smt_decls (P : s_prg) : string :=
  "(define-sort SCl () (List Int)) ;the sort of classes" ++ LF ++
  "(define-fun-rec subclass ((x SCl) (y SCl)) Bool" ++ LF ++
  "(ite (= y nil) true (ite (= x nil) false (ite (= (head x) (head y)) (subclass (tail x) (tail y)) false))))" ++ LF ++
  "(declare-sort SRef) ;the sort of references" ++ LF ++
  "(declare-fun classOf (SRef) SCl)" ++ LF ++
  "(declare-fun _null () SRef)" ++ LF ++
  (String.concat "" (List.map (class_to_smt P) (classes P))).

Fixpoint value_to_smt (σ : s_val) : string :=
  match σ with
  | s_val_prim_c p => prim_c_to_str p
  | s_val_ref_c u => ref_c_to_smt u
  | s_val_add σ1 σ2 => "(+ " ++ value_to_smt σ1 ++ " " ++ value_to_smt σ2 ++ ")"
  | s_val_lt σ1 σ2 => "(< " ++ value_to_smt σ1 ++ " " ++ value_to_smt σ2 ++ ")"
  | s_val_eq σ1 σ2 => "(= " ++ value_to_smt σ1 ++ " " ++ value_to_smt σ2 ++ ")"
  | s_val_ite σ1 σ2 σ3 => "(ite " ++ value_to_smt σ1 ++ " " ++ value_to_smt σ2 ++ " " ++ value_to_smt σ3 ++ ")"
  | _ => ""
  end.

Definition clause_to_smt (P : s_prg) (σ : s_val) (positive : bool) : string :=
  match σ with
  | s_val_prim_c p => prim_c_to_str p
  | s_val_ref_c u => ref_c_to_smt u
  | s_val_lt σ1 σ2 => "(assert " ++ (if positive then "" else "(not ") ++ "(< " ++ value_to_smt σ1 ++ " " ++ value_to_smt σ2 ++ ")" ++ (if positive then "" else ")") ++ ")"
  | s_val_eq σ1 σ2 => "(assert " ++ (if positive then "" else "(not ") ++ "(= " ++ value_to_smt σ1 ++ " " ++ value_to_smt σ2 ++ ")" ++ (if positive then "" else ")") ++ ")"
  | s_val_subtype σ t => match t with
    | s_ty_class c => "(assert " ++ (if positive then "" else "(not ") ++ "(subclass (classOf " ++ value_to_smt σ ++ ") " ++ c ++ ")" ++ (if positive then "" else ")") ++ ")"
    | _ => ""
    end
  | s_val_field s1 f s2 => "(assert " ++ (if positive then "" else "(not ") ++ "(= (" ++ f ++ " " ++ ref_c_to_smt (s_ref_c_symb s1) ++ ") " ++
       (match class_with_field P f with
        | Some C =>
          match fdecl C f with
          | Some F =>              
            let t := field_type F in
            if is_type_primitive t then
              prim_c_to_str (s_prim_c_symb s2)
            else
              ref_c_to_smt (s_ref_c_symb s2)
          | _ => "" (* error (internal): class C' has no field f *)
          end         
        | _ => "" (* error: no class exists with field f *)
        end) ++ ")" ++ (if positive then "" else ")") ++ ")"
  | s_val_ite σ1 σ2 σ3 => "(assert " ++ (if positive then "" else "(not ") ++ "(ite " ++ value_to_smt σ1 ++ " " ++ value_to_smt σ2 ++ " " ++ value_to_smt σ3 ++ ")" ++ (if positive then "" else ")") ++ ")"
  | _ => ""
  end.

Fixpoint clauses_to_smt (P : s_prg) (Σ : path_condition) : string :=
  match Σ with
  | [] => ""
  | cl :: Σ' => match cl with
    | clause_pos σ => clause_to_smt P σ true ++ LF 
    | clause_neg σ => clause_to_smt P σ false ++ LF 
    end ++ clauses_to_smt P Σ'
  end.

Fixpoint add_vars (ss : list s_symb) (σ : s_val) : list s_symb :=
  match σ with
  | s_val_prim_c p => match p with
    | s_prim_c_symb s => ss ++ [s]
    | _ => ss
    end
  | s_val_ref_c u => match u with
    | s_ref_c_symb s => ss ++ [s]
    | _ => ss
    end
  | s_val_lt σ1 σ2 => add_vars (add_vars ss σ1) σ2
  | s_val_eq σ1 σ2 => add_vars (add_vars ss σ1) σ2
  | s_val_subtype σ t => add_vars ss σ
  | s_val_field s1 f s2 => ss ++ [s1 ; s2]
  | s_val_ite σ1 σ2 σ3 => add_vars (add_vars (add_vars ss σ1) σ2) σ3
  | _ => ss
  end.

Fixpoint contains (ss : list s_symb) (s : s_symb) : bool :=
  match ss with
  | [] => false
  | s' :: ss' => s_symb_eqb s s' ||| contains ss' s
  end.

Fixpoint declare_vars_clause (P : s_prg) (σ : s_val) (ss : list s_symb) : string :=
  match σ with
  | s_val_prim_c p => match p with
    | s_prim_c_symb s => if contains ss s then "" else "(declare-fun " ++ prim_c_to_str (s_prim_c_symb s) ++ " () Int)" ++ LF
    | _ => ""
    end
  | s_val_ref_c u => match u with
    | s_ref_c_symb s => if contains ss s then "" else "(declare-fun " ++ ref_c_to_smt (s_ref_c_symb s) ++ " () SRef)" ++ LF
    | _ => ""
    end
  | s_val_lt σ1 σ2 => declare_vars_clause P σ1 ss ++ declare_vars_clause P σ2 (add_vars ss σ1)
  | s_val_eq σ1 σ2 => declare_vars_clause P σ1 ss ++ declare_vars_clause P σ2 (add_vars ss σ1)
  | s_val_subtype σ t => declare_vars_clause P σ ss
  | s_val_field s1 f s2 => (if contains ss s1 then "" else "(declare-fun " ++ ref_c_to_smt (s_ref_c_symb s1) ++ " () SRef)" ++ LF) ++ (if contains ss s2 then "" else
     (match class_with_field P f with
        | Some C =>
          match fdecl C f with
          | Some F =>              
            let t := field_type F in
            if is_type_primitive t then
              "(declare-fun " ++ prim_c_to_str (s_prim_c_symb s2) ++ " () Int)"
            else
              "(declare-fun " ++ ref_c_to_smt (s_ref_c_symb s2) ++ " () SRef)"
          | _ => "" (* error (internal): class C' has no field f *)
          end         
        | _ => "" (* error: no class exists with field f *)
        end) ++ LF) 
  | s_val_ite σ1 σ2 σ3 => declare_vars_clause P σ1 ss ++ declare_vars_clause P σ2 (add_vars ss σ1) ++ declare_vars_clause P σ3 (add_vars (add_vars ss σ1) σ2)
  | _ => ""
  end.

Fixpoint declare_vars (P : s_prg) (Σ : path_condition) (ss : list s_symb) : string :=
  match Σ with
  | [] => ""
  | cl :: Σ' => match cl with
    | clause_pos σ => declare_vars_clause P σ ss ++ declare_vars P Σ' (add_vars ss σ)
    | clause_neg σ => declare_vars_clause P σ ss ++ declare_vars P Σ' (add_vars ss σ)
    end
  end.

Definition path_condition_to_smt (P : s_prg) (Σ : path_condition) : string :=
  declare_vars P Σ [] ++ clauses_to_smt P Σ.

Definition config_to_smt (J : config) : string :=
  let (AA, _) := J in 
  let (BB, Σ) := AA in
  let (P, _) := BB in
  smt_decls P ++ path_condition_to_smt P Σ.

Definition step_to_smt (Js : list config) : list string :=
   map config_to_smt Js.
