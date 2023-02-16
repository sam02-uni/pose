From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.
From BOSE Require Import Syntax.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(****************************** Parsing **************************)

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (Nat.eqb n 32) (* space *)
           (Nat.eqb n 9)) (* tab *)
      (orb (Nat.eqb n 10) (* linefeed *)
           (Nat.eqb n 13)). (* Carriage return. *)

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (Nat.leb 97 n) (Nat.leb n 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (Nat.leb 65 n) (Nat.leb n 90))
        (andb (Nat.leb 97 n) (Nat.leb n 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (Nat.leb 48 n) (Nat.leb n 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "(" =>
      tk ++ ["("] :: (tokenize_helper other [] xs')
    | _, _, ")" =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _ =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize_ex1 :
    tokenize "abc12=3 223*(3+(a+c))" %string
  = ["abc"; "12"; "="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed.

