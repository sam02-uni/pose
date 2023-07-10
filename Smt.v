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

(************************ Emitting SMTLIB ***********************)

Definition classes_to_smt (Cs : list s_dc_c) : string :=
  match Cs with
  | [] => EmptyString
  | _ => EmptyString
  end.
