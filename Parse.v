From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.
From POSE Require Import Syntax.

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
    | digit,alpha,x =>
      tokenize_helper alpha (x::acc) xs'
    | alpha,digit,x =>
      tokenize_helper digit (x::acc) xs'
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

Inductive optionE (X : Type) : Type :=
| SomeE : X -> optionE X
| NoneE : string -> optionE X.

Definition optionE_map (X Y : Type) (f : X -> Y) (u : optionE X) : optionE Y :=
  match u with
  | SomeE x => SomeE (f x)
  | NoneE s => NoneE Y s
  end.

Definition parser (T : Type) := list token -> list token * optionE T.

Definition any_token : parser string :=
  fun toks : list token =>
    match toks with
    | token :: toks' => (toks', SomeE token)
    | [] => ([], NoneE string "Expected a token, found end of stream")
    end.

Definition match_token (s : string) : parser string :=
  fun toks : list token =>
    match toks with
    | token :: toks' => if (String.eqb token s) then (toks', SomeE s) else (toks', NoneE string ("Expected " ++ s ++ ", found " ++ token))
    | [] => ([], NoneE string ("Expected " ++ s ++ ", found end of stream"))
    end.

Notation " ' s " := (match_token s) (at level 55).

Definition eos : parser unit :=
  fun toks : list token =>
    match toks with
    | token :: toks' => (toks', NoneE unit ("Expected end of stream, found " ++ token))
    | [] => ([], SomeE tt)
    end.

Definition and_then (T U : Type) (p : parser T) (f : T -> parser U) : parser U :=
  fun toks : list token =>
    match p toks with
    | (toks', SomeE t) => f t toks'
    | (toks', NoneE s) => (toks', NoneE U s)
    end.

Notation " p <*> q " := (and_then p q) (at level 60, right associativity, q at next level).

Definition alt (T : Type) (p q : parser T) : parser T :=
  fun toks : list token =>
    match p toks with
    | (toks', SomeE t) => (toks', SomeE t)
    | (toks', NoneE _) => q toks
    end.

Notation " p <|> q " := (alt p q) (at level 65, left associativity).

Fixpoint star_bounded_aux (T : Type) (p : parser T) (n : nat) (toks : list token) (l : list T) : list token * optionE (list T) :=
  match p toks with
  | (toks', NoneE _) => (toks, SomeE (rev l))
  | (toks', SomeE t) =>
      match n with
      | 0 => (toks, NoneE (list T) "Too many matches, exhausted bound")
      | S n' => star_bounded_aux p n' toks' (t :: l)
      end
  end.

Definition star_bounded (T : Type) (p : parser T) (n : nat) : parser (list T) :=
  fun toks : list token => star_bounded_aux p n toks [].

Definition transform (T U : Type) (p : parser T) (f : T -> U) : parser U :=
  fun toks : list token => let (toks, result) := p toks in (toks, optionE_map f result).

Notation " p '==>' f " := (transform p f) (at level 57).

Definition b : parser s_bool :=
  fun toks : list token =>
    match toks with
    | token :: toks' => if String.eqb token "true" then (toks', SomeE s_bool_true)
                        else if String.eqb token "false" then (toks', SomeE s_bool_false)
                             else (toks', NoneE s_bool ("Expected boolean, found " ++ token))
    | [] => ([], NoneE s_bool "Expected boolean, found end of stream")
    end.

Definition string_to_nat (token : string) : nat :=
  fold_left
     (fun n d =>
        10 * n + (nat_of_ascii d -
                    nat_of_ascii "0"%char))
     (list_of_string token) 0.

Definition nat_token : parser string :=
  fun toks : list token =>
    match toks with
    | token :: toks' => if forallb isDigit (list_of_string token) then
                          (toks', SomeE token)
                        else (toks', NoneE string ("Expected natural number, found " ++ token))
    | [] => ([], NoneE string "Expected natural number, found end of stream.")
    end.

Definition n : parser s_int := nat_token ==> (fun x => s_int_l (string_to_nat x)).

Definition char_nat_token (char : ascii) : parser nat :=
  fun toks : list token =>
    match toks with
    | token :: toks' =>
        match list_of_string token with
        | c :: ltoken' => if andb (Nat.eqb (nat_of_ascii c) (nat_of_ascii char)) (forallb isDigit ltoken') then
                            (toks', SomeE (string_to_nat (string_of_list ltoken')))
                          else (toks', NoneE nat ("Expected char " ++ (String char EmptyString) ++ " plus natural number, found " ++ token))
        | [] => (toks', NoneE nat ("Expected char " ++ (String char EmptyString) ++ " plus natural number, found empty token"))
        end
    | [] => ([], NoneE nat ("Expected char " ++ (String char EmptyString) ++ " plus natural number, found end of stream."))
    end.

Definition l : parser s_loc :=
  char_nat_token "L"%char ==> (fun x => s_loc_l x).

Definition X : parser s_symb :=
  char_nat_token "X"%char ==> (fun x => s_symb_expr x).

Definition Y : parser s_symb :=
  char_nat_token "Y"%char ==> (fun x => s_symb_expr x).

Definition σ : parser s_val :=
  ' "BOT"  ==> (fun _ => s_val_unassumed)                <|>
  b        ==> (fun x => s_val_prim_c (s_prim_c_bool x)) <|>
  n        ==> (fun x => s_val_prim_c (s_prim_c_int x))  <|>
  X        ==> (fun x => s_val_prim_c (s_prim_c_symb x)) <|>
  ' "null" ==> (fun _ => s_val_ref_c s_ref_c_null)       <|>
  l        ==> (fun x => s_val_ref_c (s_ref_c_loc x))    <|>
  Y        ==> (fun x => s_val_ref_c (s_ref_c_symb x)).

Definition identifier : parser string :=
  fun toks : list token =>
    match toks with
    | token :: toks' => if isAlpha (hd "0"%char (list_of_string token)) then
                          (toks', SomeE token)
                        else (toks', NoneE string ("Expected identifier, found " ++ token))
    | [] => ([], NoneE string "Expected identifier, found end of stream.")
    end.

Definition max_expr := 100.
  
Fixpoint expr (n : nat) : parser s_expr :=
  match n with
  | S n' =>
      σ                         ==> (fun x => s_expr_val x)           <|>
      (' "new" <*>
        fun _ => identifier     ==> (fun x => s_expr_new x))          <|>
      (' "let" <*>
        fun _ => identifier <*>
        fun x => ' ":=" <*>
        fun _ => expr n' <*>
        fun y => ' "in" <*>
        fun _ => expr n'        ==> (fun z => s_expr_let x y z))      <|>
      (' "if" <*>
        fun _ => expr n' <*>
        fun x => ' "then" <*>
        fun _ => expr n' <*>
        fun y => ' "else" <*>
        fun _ => expr n'        ==> (fun z => s_expr_if x y z))       <|>
      (identifier               ==> (fun x => s_expr_var x))          <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "+" <*>
        fun _ => expr n' <*>
        fun y => ' ")"          ==> (fun _ => s_expr_add x y))        <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "-" <*>
        fun _ => expr n' <*>
        fun y => ' ")"          ==> (fun _ => s_expr_sub x y))        <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "<" <*>
        fun _ => expr n' <*>
        fun y => ' ")"          ==> (fun _ => s_expr_lt x y))         <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "&&" <*>
        fun _ => expr n' <*>
        fun y => ' ")"          ==> (fun _ => s_expr_and x y))        <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "||" <*>
        fun _ => expr n' <*>
        fun y => ' ")"          ==> (fun _ => s_expr_or x y))         <|>
      (' "(" <*>
        fun _ => ' "~" <*>
        fun _ => expr n' <*>
        fun x => ' ")"          ==> (fun _ => s_expr_not x))          <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "=" <*>
        fun _ => expr n' <*>
        fun y => ' ")"          ==> (fun _ => s_expr_eq x y))         <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "instanceof" <*>
        fun _ => identifier <*>
        fun y => ' ")"          ==> (fun _ => s_expr_instanceof x y)) <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "." <*>
        fun _ => identifier <*>
        fun y => ' "[" <*>
        fun _ => expr n' <*>
        fun z => ' "]" <*>
        fun _ => ' ")"          ==> (fun _ => s_expr_invoke x y z))   <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "." <*>
        fun _ => identifier <*>
        fun y => ' ":=" <*>
        fun _ => expr n' <*>
        fun z => ' ")"          ==> (fun _ => s_expr_putfield x y z)) <|>
      (' "(" <*>
        fun _ => expr n' <*>
        fun x => ' "." <*>
        fun _ => identifier <*>
        fun y => ' ")"          ==> (fun _ => s_expr_getfield x y))
  | 0 => fun toks : list token => (toks, NoneE s_expr "Exhausted subexpression recursion bound")
  end.

Definition t : parser s_ty :=
  (' "bool"   ==> (fun _ => s_ty_bool)) <|>
  (' "int"    ==> (fun _ => s_ty_int))  <|>
  (identifier ==> (fun x => s_ty_class x)).

Definition D : parser s_dc_m :=
  t <*>
  fun type_m => identifier <*>
  fun name_m => ' "(" <*>
  fun _ => t <*>
  fun type_p => identifier <*>
  fun name_p => ' ")" <*>                                      
  fun _ => ' ":=" <*>
  fun _ => expr max_expr ==> (fun body => s_dc_m_l type_m name_m (s_dc_v_l type_p name_p) body).

Definition max_fields := 50.

Definition max_methods := 50.

Definition C : parser s_dc_c :=
  ' "class" <*>
  fun _ => identifier <*>
  fun name_c => star_bounded (
    ' "extends" <*>
    fun _ => identifier) 1 <*>
  fun name_super => ' "{" <*>
  fun _ => star_bounded (
    t <*>
    fun type_fld => identifier <*>
    fun name_fld => ' ";" ==> (fun _ => s_dc_v_l type_fld name_fld)) max_fields <*>
  fun flds => star_bounded (                        
    D <*>
    fun meth => ' ";" ==> (fun _ => meth)) max_methods <*>
  fun meths => ' "}" ==> (fun _ => s_dc_c_l name_c (String.concat "" name_super) flds meths).

Definition max_classes := 50.

Definition P : parser s_prg :=
  star_bounded C max_classes <*>
  fun classes => expr max_expr ==> (fun body => s_prg_l classes body).

Definition parse (s : string) := P (tokenize s).
