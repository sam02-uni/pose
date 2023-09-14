From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(******************************** Syntax ***************************)

(* Types *)
Inductive s_ty : Type :=
| s_ty_bool : s_ty
| s_ty_int : s_ty 
| s_ty_class : string -> s_ty.

(* Boolean literals *)
Inductive s_bool : Type :=
| s_bool_true : s_bool
| s_bool_false : s_bool.

(* Integer literals (actually natural) *)
Inductive s_int : Type :=
| s_int_l : nat -> s_int.

(* Locations *)
Inductive s_loc : Type :=
| s_loc_l : nat -> s_loc.

(* Symbols *)
Inductive s_symb : Type :=
(* 'Top-level' symbols, they may be used in 
   user-defined expressions; they signify
   an unknown input *) 
| s_symb_expr : nat -> s_symb 
(* Symbols introduced by refinements actions
   during execution; they signify the initial
   value of a field of an input object *)
| s_symb_fld : nat -> list string -> s_symb.

(* Constants with primitive type *)
Inductive s_prim_c : Type :=
(* A concrete constant with bool type *)
| s_prim_c_bool : s_bool -> s_prim_c
(* A concrete constant with int type *) 
| s_prim_c_int : s_int -> s_prim_c
(* A symbolic constant (i.e., a symbol) *)
| s_prim_c_symb : s_symb -> s_prim_c.

(* Constants with reference type *)
Inductive s_ref_c : Type :=
(* The null reference constant *)
| s_ref_c_null : s_ref_c
(* A location constant *)
| s_ref_c_loc : s_loc -> s_ref_c
(* A symbolic constant (i.e., a symbol) *)
| s_ref_c_symb : s_symb -> s_ref_c.

(* Values; they cannot be further reduced *)
Inductive s_val : Type :=
(* An unspecified value of any type *)
| s_val_unassumed : s_val
(* A constant with primitive type *)
| s_val_prim_c : s_prim_c -> s_val
(* A constant with reference type *)
| s_val_ref_c : s_ref_c -> s_val
(* A symbolic term for an addition operation *)
| s_val_add : s_val -> s_val -> s_val
(* A symbolic term for a subtraction operation *)
| s_val_sub : s_val -> s_val -> s_val
(* A symbolic term for a less-than relation *)
| s_val_lt : s_val -> s_val -> s_val
(* A symbolic term for a logical and *)
| s_val_and : s_val -> s_val -> s_val
(* A symbolic term for a logical or *)
| s_val_or : s_val -> s_val -> s_val
(* A symbolic term for a logical not *)
| s_val_not : s_val -> s_val
(* A symbolic term for an equality relation *)
| s_val_eq : s_val -> s_val -> s_val
(* A symbolic term for a subtype relation *)
| s_val_subtype : s_val -> s_ty -> s_val
(* A symbolic term for a field relation (i.e., 
     Y.f = Z, with Y and Z symbols  *)
| s_val_field : s_symb -> string -> s_symb -> s_val
(* An if-then-else term *)
| s_val_ite : s_val -> s_val -> s_val -> s_val.

(* Expressions; note that we do not distinguish
   syntactically the expressions that may be formed
   by users when writing programs from the full range
   of the expressions that may be formed during 
   execution by the abstract interpreter. *)
Inductive s_expr : Type :=
(* A variable (used in 'let' bindings) *)
| s_expr_var : string -> s_expr
(* A value *)
| s_expr_val : s_val -> s_expr
(* Reference to a new object *)
| s_expr_new : string -> s_expr
(* The value in an object's field *)
| s_expr_getfield : s_expr -> string -> s_expr
(* Sets the value of an object's field *)
| s_expr_putfield : s_expr -> string -> s_expr -> s_expr
(* A 'let' binding *)
| s_expr_let : string -> s_expr -> s_expr -> s_expr
(* Addition of two expressions *)
| s_expr_add : s_expr -> s_expr -> s_expr
(* Subtraction of two expressions *)
| s_expr_sub : s_expr -> s_expr -> s_expr
(* Less-than comparison of two expressions *)
| s_expr_lt : s_expr -> s_expr -> s_expr
(* Logical and of two expression *)
| s_expr_and : s_expr -> s_expr -> s_expr
(* Logical or of two expressions *)
| s_expr_or : s_expr -> s_expr -> s_expr
(* Logical not of an expression *)
| s_expr_not : s_expr -> s_expr
(* Equality of two expressions *)
| s_expr_eq : s_expr -> s_expr -> s_expr
(* Dynamic subclass check *)
| s_expr_instanceof : s_expr -> string -> s_expr
(* A conditional expression *)
| s_expr_if : s_expr -> s_expr -> s_expr -> s_expr
(* Method invocation *)
| s_expr_invoke : s_expr -> string -> s_expr -> s_expr.

(* A variable declaration (for fields and methods 
   formal parameters *)
Inductive s_dc_v : Type :=
| s_dc_v_l : s_ty -> string -> s_dc_v.

(* A method declaration *)
Inductive s_dc_m : Type :=
| s_dc_m_l : s_ty -> string -> s_dc_v -> s_expr -> s_dc_m.

(* A class declaration *)
Inductive s_dc_c : Type :=
| s_dc_c_l : string -> string -> list s_dc_v -> list s_dc_m -> s_dc_c.

(* A program; It is a set of class declarations plus
   a 'main' expression *)
Inductive s_prg : Type :=
| s_prg_l : list s_dc_c -> s_expr -> s_prg.

(* The 'Object' class *)
Definition CObject : s_dc_c := s_dc_c_l "Object" "" [] [].

(***************** Syntax-related functions and predicate  ****************)

(* Various getters for the defined types *)

Definition classes (P : s_prg) : list s_dc_c :=
  match P with
  | s_prg_l Cs _ => Cs 
  end.

Definition expression (P : s_prg) : s_expr :=
  match P with
  | s_prg_l _ e => e
  end.

Definition class_name (C : s_dc_c) : string :=
  match C with
  | s_dc_c_l c _ _ _ => c 
  end.

Definition superclass_name (C : s_dc_c) : string :=
  match C with
  | s_dc_c_l _ s _ _ => s 
  end.

Definition fields (C : s_dc_c) : list s_dc_v :=
  match C with
  | s_dc_c_l _ _ Fs _ => Fs 
  end.

Definition methods (C : s_dc_c) : list s_dc_m :=
  match C with
  | s_dc_c_l _ _ _ Ds => Ds 
  end.

Definition method_name (D : s_dc_m) : string :=
  match D with
  | s_dc_m_l _ m _ _ => m
  end.

Definition field_type (F : s_dc_v) : s_ty :=
  match F with
  | s_dc_v_l t _ => t
  end.

Definition field_name (F : s_dc_v) : string :=
  match F with
  | s_dc_v_l _ n => n
  end.

(* Computable equalities on types *)

Definition s_bool_eqb (b1 b2 : s_bool) : bool :=
  match b1, b2 with
  | s_bool_true, s_bool_true => true
  | s_bool_false, s_bool_false => true
  | _, _ => false
  end.

Definition s_int_eqb (n1 n2 : s_int) : bool :=
  match n1, n2 with
  | s_int_l i1, s_int_l i2 => Nat.eqb i1 i2
  end.

Fixpoint list_string_eqb (l1 l2 : list string) : bool :=
  match l1, l2 with
  | [], [] => true
  | s1 :: l1', s2 :: l2' => andb (String.eqb s1 s2) (list_string_eqb l1' l2')
  | _, _ => false
  end.

Definition s_symb_eqb (s1 s2 : s_symb) : bool :=
  match s1, s2 with
  | s_symb_expr n1, s_symb_expr n2 => Nat.eqb n1 n2
  | s_symb_fld n1 l1, s_symb_fld n2 l2 => andb (Nat.eqb n1 n2) (list_string_eqb l1 l2)
  | _, _ => false
  end.

Definition s_prim_c_eqb (p1 p2 : s_prim_c) : bool :=
  match p1, p2 with
  | s_prim_c_bool b1, s_prim_c_bool b2 => s_bool_eqb b1 b2
  | s_prim_c_int n1, s_prim_c_int n2 => s_int_eqb n1 n2
  | s_prim_c_symb s1, s_prim_c_symb s2 => s_symb_eqb s1 s2
  | _, _ => false
  end.

Definition s_loc_eqb (l1 l2 : s_loc) : bool :=
  match l1, l2 with
  | s_loc_l l1, s_loc_l l2 => Nat.eqb l1 l2
  end.

Definition s_ref_c_eqb (u1 u2 : s_ref_c) : bool :=
  match u1, u2 with
  | s_ref_c_null, s_ref_c_null => true
  | s_ref_c_loc l1, s_ref_c_loc l2 => s_loc_eqb l1 l2
  | s_ref_c_symb s1, s_ref_c_symb s2 => s_symb_eqb s1 s2
  | _, _ => false
  end.

Definition s_ty_eqb (t1 t2 : s_ty) : bool :=
  match t1, t2 with
  | s_ty_bool, s_ty_bool => true
  | s_ty_int, s_ty_int => true 
  | s_ty_class c1, s_ty_class c2 => String.eqb c1 c2
  | _, _ => false
  end.

Fixpoint s_val_eqb (σ1 σ2 : s_val) : bool := 
  match σ1, σ2 with
  | s_val_unassumed, s_val_unassumed => true
  | s_val_prim_c p1, s_val_prim_c p2 => s_prim_c_eqb p1 p2
  | s_val_ref_c u1, s_val_ref_c u2 => s_ref_c_eqb u1 u2
  | s_val_add σ11 σ12, s_val_add σ21 σ22 => andb (s_val_eqb σ11 σ21) (s_val_eqb σ12 σ22)
  | s_val_lt σ11 σ12, s_val_lt σ21 σ22 => andb (s_val_eqb σ11 σ21) (s_val_eqb σ12 σ22)
  | s_val_and σ11 σ12, s_val_and σ21 σ22 => andb (s_val_eqb σ11 σ21) (s_val_eqb σ12 σ22)
  | s_val_or σ11 σ12, s_val_or σ21 σ22 => andb (s_val_eqb σ11 σ21) (s_val_eqb σ12 σ22)
  | s_val_not σ1, s_val_not σ2 => s_val_eqb σ1 σ2
  | s_val_eq σ11 σ12, s_val_eq σ21 σ22 => andb (s_val_eqb σ11 σ21) (s_val_eqb σ12 σ22)
  | s_val_subtype σ11 t1, s_val_subtype σ21 t2 => andb (s_val_eqb σ11 σ21) (s_ty_eqb t1 t2)
  | s_val_field s11 f1 s12, s_val_field s21 f2 s22 => andb (s_symb_eqb s11 s21) (andb (String.eqb f1 f2) (s_symb_eqb s12 s22))
  | s_val_ite σ11 σ12 σ13, s_val_ite σ21 σ22 σ23 => andb (s_val_eqb σ11 σ21) (andb (s_val_eqb σ12 σ22) (s_val_eqb σ13 σ23))
  | _, _ => false
  end.

(* Is a type a reference? *)
Definition is_type_reference (t : s_ty) : bool :=
  match t with
  | s_ty_class _ => true
  | _ => false
  end.

Definition is_type_primitive (t : s_ty) : bool :=
  match t with
  | s_ty_class _ => false
  | _ => true
  end.
  

(* Is a value a reference? *)
Fixpoint is_reference (σ : s_val) : bool :=
  match σ with
  | s_val_unassumed => false (* imprecise, not meant to be used on it *)
  | s_val_prim_c _ => false
  | s_val_ref_c  _ => true 
  | s_val_add _ _ => false
  | s_val_sub _ _ => false
  | s_val_lt _ _ => false
  | s_val_and _ _ => false
  | s_val_or _ _ => false
  | s_val_not _ => false
  | s_val_eq _ _ => false
  | s_val_subtype _ _ => false
  | s_val_field _ _ _ => false
  | s_val_ite _ σ' _ => is_reference σ'
  end.

(* Initialization values for language types *)
Definition ini (t : s_ty) : s_val :=
  match t with
  | s_ty_bool => s_val_prim_c (s_prim_c_bool s_bool_false)
  | s_ty_int => s_val_prim_c (s_prim_c_int (s_int_l 0))
  | s_ty_class _ => s_val_ref_c s_ref_c_null
  end.

(* Substitution of variable with name x with expression 
   e' in another expression e *)
Fixpoint repl_var (e : s_expr) (x : string) (e' : s_expr) : s_expr :=
  match e with
  | s_expr_var x' => if (String.eqb x x') then e' else (s_expr_var x')
  | s_expr_val σ => s_expr_val σ
  | s_expr_new cname => s_expr_new cname
  | s_expr_getfield e1 f =>  s_expr_getfield (repl_var e1 x e') f
  | s_expr_putfield e1 f e2 => s_expr_putfield (repl_var e1 x e') f (repl_var e2 x e')
  | s_expr_let x' e1 e2 => if (String.eqb x x') then (s_expr_let x' e1 e2) else (s_expr_let x' (repl_var e1 x e') (repl_var e2 x e'))
  | s_expr_add e1 e2 => s_expr_add (repl_var e1 x e') (repl_var e2 x e')
  | s_expr_sub e1 e2 => s_expr_sub (repl_var e1 x e') (repl_var e2 x e')
  | s_expr_lt e1 e2 => s_expr_lt (repl_var e1 x e') (repl_var e2 x e')
  | s_expr_and e1 e2 => s_expr_and (repl_var e1 x e') (repl_var e2 x e')
  | s_expr_or e1 e2 => s_expr_or (repl_var e1 x e') (repl_var e2 x e')
  | s_expr_not e => s_expr_not (repl_var e x e')
  | s_expr_eq e1 e2 => s_expr_eq (repl_var e1 x e') (repl_var e2 x e')
  | s_expr_instanceof e1 c => s_expr_instanceof (repl_var e1 x e') c
  | s_expr_if e1 e2 e3 => s_expr_if (repl_var e1 x e') (repl_var e2 x e') (repl_var e3 x e')
  | s_expr_invoke e1 m e2 => s_expr_invoke (repl_var e1 x e') m (repl_var e2 x e')
  end.

