From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From POSE Require Import Aux.
From POSE Require Import Syntax.
From POSE Require Import SemanticsTypes.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(****************************** Prettyprinting **************************)

Definition ty_to_dstr (t : s_ty) : dstring :=
  match t with
  | s_ty_bool => from_string "bool"
  | s_ty_int => from_string "int"
  | s_ty_class c => from_string c
  end.

Definition bool_to_dstr (b : s_bool) : dstring :=
  match b with
  | s_bool_true => from_string "true"
  | s_bool_false => from_string "false"
  end.

Definition nat_to_digit (n : nat) : string :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Fixpoint nat_to_dstr_aux (n k : nat) : dstring :=
  match n, k with
  | 0, 0    => from_string "0"
  | 1, 1    => from_string "1"
  | 0, S _
  | _, 0    => from_string ""
  | _, S k' => append (nat_to_dstr_aux (div n 10) k') (from_string (nat_to_digit (n mod 10)))
  end.

Definition nat_to_dstr (n : nat) : dstring := nat_to_dstr_aux n n.
  
Definition int_to_dstr (n : s_int) : dstring :=
  match n with
  | s_int_l n' => nat_to_dstr n'
  end.

Definition loc_to_dstr (l : s_loc) : dstring :=
  match l with
  | s_loc_l n => append (from_string "L") (nat_to_dstr n)
  end.

Definition symb_to_dstr (s : s_symb) : dstring :=
  match s with
  | s_symb_expr n => nat_to_dstr n 
  | s_symb_fld n l => append (append (nat_to_dstr n) (from_string "_")) (dconcat (from_string "_") (map from_string l))
  end.

Definition prim_c_to_dstr (p : s_prim_c) : dstring :=
  match p with
  | s_prim_c_bool b => bool_to_dstr b
  | s_prim_c_int n => int_to_dstr n
  | s_prim_c_symb s => append (from_string "X") (symb_to_dstr s)
  end.

Definition ref_c_to_dstr (u : s_ref_c) : dstring :=
  match u with
  | s_ref_c_null => from_string "null"
  | s_ref_c_loc l => loc_to_dstr l
  | s_ref_c_symb s => append (from_string "Y") (symb_to_dstr s)
  end.

Fixpoint val_to_dstr (σ : s_val) : dstring :=
  match σ with
  | s_val_unassumed => from_string "BOT"
  | s_val_prim_c p => prim_c_to_dstr p
  | s_val_ref_c u => ref_c_to_dstr u
  | s_val_add σ1 σ2 => append (append (append (append (from_string "(") (val_to_dstr σ1)) (from_string " + ")) (val_to_dstr σ2)) (from_string ")")
  | s_val_sub σ1 σ2 => append (append (append (append (from_string "(") (val_to_dstr σ1)) (from_string " - ")) (val_to_dstr σ2)) (from_string ")")
  | s_val_lt σ1 σ2 => append (append (append (append (from_string "(") (val_to_dstr σ1)) (from_string " < ")) (val_to_dstr σ2)) (from_string ")")
  | s_val_and σ1 σ2 => append (append (append (append (from_string "(") (val_to_dstr σ1)) (from_string " && ")) (val_to_dstr σ2)) (from_string ")")
  | s_val_or σ1 σ2 => append (append (append (append (from_string "(") (val_to_dstr σ1)) (from_string " || ")) (val_to_dstr σ2)) (from_string ")")
  | s_val_not σ1 => append (append (from_string "(~") (val_to_dstr σ1)) (from_string ")")
  | s_val_eq σ1 σ2 => append (append (append (append (from_string "(") (val_to_dstr σ1)) (from_string " = ")) (val_to_dstr σ2)) (from_string ")")
  | s_val_subtype σ t => append (append (append (append (from_string "(") (val_to_dstr σ)) (from_string " <: ")) (ty_to_dstr t)) (from_string ")")
  | s_val_field s1 fname s2 => append (append (append (append (append (append (from_string "(Y") (symb_to_dstr s1)) (from_string ".")) (from_string fname)) (from_string " = Z")) (symb_to_dstr s2)) (from_string ")")
  | s_val_ite σ1 σ2 σ3 => append (append (append (append (append (append (from_string "ite(") (val_to_dstr σ1)) (from_string ", ")) (val_to_dstr σ2)) (from_string ", ")) (val_to_dstr σ3)) (from_string ")")
  end.

Fixpoint expr_to_dstr (e : s_expr) : dstring :=
  match e with
  | s_expr_var x => (from_string x)
  | s_expr_val σ => val_to_dstr σ
  | s_expr_new c => append (from_string "new ") (from_string c)
  | s_expr_getfield e1 fname => append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string ".")) (from_string fname)) (from_string ")")
  | s_expr_putfield e1 fname e2 => append (append (append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string ".")) (from_string fname)) (from_string " := ")) (expr_to_dstr e2)) (from_string ")")
  | s_expr_let x e1 e2 => append (append (append (append (append (from_string "let ") (from_string x)) (from_string " := ")) (expr_to_dstr e1)) (from_string " in ")) (expr_to_dstr e2)
  | s_expr_add e1 e2 => append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string " + ")) (expr_to_dstr e2)) (from_string ")")
  | s_expr_sub e1 e2 => append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string " - ")) (expr_to_dstr e2)) (from_string ")")
  | s_expr_lt e1 e2 => append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string " < ")) (expr_to_dstr e2)) (from_string ")")
  | s_expr_and e1 e2 => append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string " && ")) (expr_to_dstr e2)) (from_string ")")
  | s_expr_or e1 e2 => append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string " || ")) (expr_to_dstr e2)) (from_string ")")
  | s_expr_not e1 => append (append (from_string "(~") (expr_to_dstr e1)) (from_string ")")
  | s_expr_eq e1 e2 => append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string " = ")) (expr_to_dstr e2)) (from_string ")")
  | s_expr_instanceof e1 c =>  append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string " instanceof ")) (from_string c)) (from_string ")")
  | s_expr_if e1 e2 e3 => append (append (append (append (append (from_string "if ") (expr_to_dstr e1)) (from_string " then ")) (expr_to_dstr e2)) (from_string " else ")) (expr_to_dstr e3)
  | s_expr_invoke e1 m e2 => append (append (append (append (append (append (from_string "(") (expr_to_dstr e1)) (from_string ".")) (from_string m)) (from_string "[")) (expr_to_dstr e2)) (from_string "])")
  end.

Definition dc_v_to_dstr (semicolon : bool) (F : s_dc_v) : dstring :=
  match F with
  | s_dc_v_l t x => append (append (append (ty_to_dstr t) (from_string " ")) (from_string x)) (from_string (if semicolon then ";" else ""))
  end.

Definition dc_m_to_dstr (D : s_dc_m) : dstring :=
  match D with
  | s_dc_m_l t m v e => append (append (append (append (append (append (append (ty_to_dstr t) (from_string " ")) (from_string m)) (from_string "(")) (dc_v_to_dstr false v)) (from_string ") := ")) (expr_to_dstr e)) (from_string ";")
  end.

Definition dc_c_to_dstr (C : s_dc_c) : dstring :=
  match C with
  | s_dc_c_l c csup Fs Ds => append (append (append (append (append (append (append (from_string "class ") (from_string c)) (from_string (if String.eqb csup "" then "" else (" extends " ++ csup)))) (from_string " { ")) (dconcat (from_string " ") (List.map (dc_v_to_dstr true) Fs))) (from_string " ")) (dconcat (from_string " ") (List.map dc_m_to_dstr Ds))) (from_string "}")
  end.

Definition prg_to_dstr (P : s_prg) : dstring :=
  match P with
  | s_prg_l Cs e => append (append (dconcat (from_string " ") (List.map dc_c_to_dstr Cs)) (from_string " ")) (expr_to_dstr e)
  end.

Section ObjectToStr.

Let Fixpoint object_to_dstr_aux (elts : list (string * s_val)) : dstring :=
  match elts with
  | [] => (from_string "")
  | (f, σ) :: other_elts => append (append (append (append (from_string f) (from_string ":")) (val_to_dstr σ)) (from_string ", ")) (object_to_dstr_aux other_elts)
  end.

Definition object_to_dstr (o : object) : dstring :=
  append (append (append (append (from_string "{class ") (from_string (o_class_name o))) (from_string ", ")) (object_to_dstr_aux (MapString.elements (o_memory o)))) (from_string "}").

End ObjectToStr.

Definition heap_to_dstr (H : heap) : dstring :=
  append (append (from_string "<") (dconcat (from_string ", ")
                                      (List.map (fun x => match x with
                                                          | (u, o) => append (append (ref_c_to_dstr u) (from_string " -> ")) (object_to_dstr o)
                                                          end)
                                         (MapRefC.elements H))))
    (from_string ">").

Fixpoint path_condition_to_dstr (Σ : path_condition) : dstring :=
  match Σ with
  | [] => (from_string "true")
  | σ :: other_Σ => append (append (val_to_dstr σ) (from_string " && ")) (path_condition_to_dstr other_Σ)
  end.

Definition config_to_dstr (J : config) : dstring :=
  match J with
  | (P, H, Σ, e) => append (append (append (append (append (append (append (append (from_string "[") (prg_to_dstr P)) (from_string ", ")) (heap_to_dstr H)) (from_string ", ")) (path_condition_to_dstr Σ)) (from_string ", ")) (expr_to_dstr e)) (from_string "]")
  end.

Definition step_to_dstr (Js : list config) : list dstring :=
   map config_to_dstr Js.

(* Direct translation to string: use only with small configs. *)

Definition prg_to_str (P : s_prg) : string :=
  to_string (prg_to_dstr P).

Definition config_to_str (J : config) : string :=
  to_string (config_to_dstr J).

Definition step_to_str (Js : list config) : list string :=
   map config_to_str Js.
