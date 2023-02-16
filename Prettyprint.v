From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From BOSE Require Import Aux.
From BOSE Require Import Syntax.
From BOSE Require Import SemanticsTypes.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(****************************** Prettyprinting **************************)

Definition ty_to_str (t : s_ty) : string :=
  match t with
  | s_ty_bool => "boolean"
  | s_ty_int => "int"
  | s_ty_class c => c
  end.

Definition bool_to_str (b : s_bool) : string :=
  match b with
  | s_bool_true => "true"
  | s_bool_false => "false"
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

Fixpoint nat_to_str_aux (n k : nat) : string :=
  match n, k with
  | 0, 0    => "0"
  | 1, 1    => "1"
  | 0, S _
  | _, 0    => ""
  | _, S k' => nat_to_str_aux (div n 10) k' ++ nat_to_digit (n mod 10)
  end.

Definition nat_to_str (n : nat) : string := nat_to_str_aux n n.
  
Definition int_to_str (n : s_int) : string :=
  match n with
  | s_int_l n' => nat_to_str n'
  end.

Definition loc_to_str (l : s_loc) : string :=
  match l with
  | s_loc_l n => "L" ++ nat_to_str n
  end.

Fixpoint symb_to_str (s : s_symb) : string :=
  match s with
  | s_symb_expr n => nat_to_str n 
  | s_symb_fld s fname => symb_to_str s ++ "_" ++ fname
  end.

Definition prim_c_to_str (p : s_prim_c) : string :=
  match p with
  | s_prim_c_bool b => bool_to_str b
  | s_prim_c_int n => int_to_str n
  | s_prim_c_symb s => "X" ++  symb_to_str s
  end.

Definition ref_c_to_str (u : s_ref_c) : string :=
  match u with
  | s_ref_c_null => "null"
  | s_ref_c_loc l => loc_to_str l
  | s_ref_c_symb s => "Y" ++  symb_to_str s
  end.

Fixpoint val_to_str (σ : s_val) : string :=
  match σ with
  | s_val_unassumed => "BOT"
  | s_val_prim_c p => prim_c_to_str p
  | s_val_ref_c u => ref_c_to_str u
  | s_val_add σ1 σ2 => "(" ++ val_to_str σ1 ++ " + " ++ val_to_str σ2 ++ ")"
  | s_val_eq σ1 σ2 => "(" ++ val_to_str σ1 ++ " = " ++ val_to_str σ2 ++ ")"
  | s_val_subtype σ t => "(" ++ val_to_str σ ++ " <: " ++ ty_to_str t ++ ")"
  | s_val_field s1 fname s2 => "(Y" ++ symb_to_str s1 ++ "." ++  fname ++ " = Y" ++ symb_to_str s2 ++ ")"
  | s_val_ite σ1 σ2 σ3 => "ite(" ++ val_to_str σ1 ++ ", " ++ val_to_str σ2 ++ ", " ++ val_to_str σ3 ++ ")"
  end.

Fixpoint expr_to_str (e : s_expr) : string :=
  match e with
  | s_expr_var x => x
  | s_expr_val σ => val_to_str σ
  | s_expr_new c => "(new " ++ c ++ ")"
  | s_expr_getfield e1 fname => "(" ++ expr_to_str e1 ++ "." ++ fname ++ ")"
  | s_expr_putfield e1 fname e2 => "(" ++ expr_to_str e1 ++ "." ++ fname ++ " := " ++ expr_to_str e2 ++ ")"
  | s_expr_let x e1 e2 => "let " ++ x ++ " := " ++ expr_to_str e1 ++ " in " ++ expr_to_str e2
  | s_expr_add e1 e2 => "(" ++ expr_to_str e1 ++ " + " ++ expr_to_str e2 ++ ")"
  | s_expr_eq e1 e2 => "(" ++ expr_to_str e1 ++ " = " ++ expr_to_str e2 ++ ")"
  | s_expr_instanceof e1 c =>  expr_to_str e1 ++ " instanceof " ++ c
  | s_expr_if e1 e2 e3 => "if " ++ expr_to_str e1 ++ " then " ++expr_to_str e2 ++ " else " ++ expr_to_str e3
  | s_expr_invoke e1 m e2 => "(" ++ expr_to_str e1 ++ "." ++ m ++ "[" ++ expr_to_str e2 ++ "])"
  end.

Definition dc_v_to_str (F : s_dc_v) : string :=
  match F with
  | s_dc_v_l t x => ty_to_str t ++ " " ++ x
  end.

Definition dc_m_to_str (D : s_dc_m) : string :=
  match D with
  | s_dc_m_l t m v e => ty_to_str t ++ " " ++ m ++ "(" ++ dc_v_to_str v ++ ") := " ++ expr_to_str e
  end.

Definition dc_c_to_str (C : s_dc_c) : string :=
  match C with
  | s_dc_c_l c csup Fs Ds => "class " ++ c ++ (if String.eqb csup "" then "" else (" extends " ++ csup)) ++ " { " ++ (String.concat "; " (List.map dc_v_to_str Fs)) ++ " " ++ (String.concat "; " (List.map dc_m_to_str Ds)) ++ "}"
  end.

Definition prg_to_str (P : s_prg) : string :=
  match P with
  | s_prg_l Cs e => (String.concat " " (List.map dc_c_to_str Cs)) ++ " " ++ expr_to_str e
  end.

Section ObjectToStr.

Let Fixpoint object_to_str_aux (elts : list (string * s_val)) : string :=
  match elts with
  | [] => ""
  | (f, σ) :: other_elts => f ++ ":" ++ val_to_str σ ++ ", " ++ object_to_str_aux other_elts
  end.

Definition object_to_str (o : object) : string :=
  "{class " ++ o_class_name o ++ ", " ++ object_to_str_aux (MapString.elements (o_memory o)) ++ "}".

End ObjectToStr.

Definition heap_to_str (H : heap) : string :=
  "<" ++ String.concat ", " (List.map (fun x => match x with
                                                | (u, o) => append (ref_c_to_str u) (append " -> " (object_to_str o))
                                                end) (MapRefC.elements H)) ++ ">".

Fixpoint path_condition_to_str (Σ : path_condition) : string :=
  match Σ with
  | [] => "true"
  | clause_pos σ :: other_Σ => (val_to_str σ) ++ " && " ++ (path_condition_to_str other_Σ)
  | clause_neg σ :: other_Σ => "~" ++ (val_to_str σ) ++ " && " ++ (path_condition_to_str other_Σ)
  end.

Definition config_to_str (J : config) : string :=
  match J with
  | (P, H, Σ, e) => "[" ++ prg_to_str P ++ ", " ++ heap_to_str H ++ ", " ++ path_condition_to_str Σ ++ ", " ++ expr_to_str e ++ "]"
  end.

Definition step_to_str (Js : list config) : list string :=
   map config_to_str Js.
