From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From POSE Require Import Syntax.
From POSE Require Import SemanticsTypes.
From POSE Require Import SemanticsAux.
From POSE Require Import Interp.
From POSE Require Import Parse.
From POSE Require Import Prettyprint.
From POSE Require Import Smt.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

From POSE Require Import Aux.

(***************************** Examples ***************************)

(* Computes 2 + 3 *)

Definition P1 : s_prg := match parse "class Object {  } (2 + 3)" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P1 0).
Compute step_to_str (step_at P1 1).
Compute step_to_str (step_at P1 2).

(* Computes 2 + 3 via method call *)

Definition P2 : s_prg := match parse "class Object {  } class Class1 extends Object {  int m(int x) := (2 + x); } (new Class1.m[3])" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P2 0).
Compute step_to_str (step_at P2 1).
Compute step_to_str (step_at P2 2).
Compute step_to_str (step_at P2 3).
Compute step_to_str (step_at P2 4).

(* Computes let x := X0 in if x = 2 then true else false *)

Definition P3 : s_prg := match parse "class Object {  } let x := X0 in if (x = 2) then true else false" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P3 0).
Compute step_to_str (step_at P3 1).
Compute step_to_str (step_at P3 2).
Compute step_to_str (step_at P3 3).
Compute step_to_str (step_at P3 4).

(* Computes Y0.f; Class1 has field f. *)

Definition P4 : s_prg := match parse "class Object {  } class Class1 extends Object { int f; } (Y0.f)" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P4 0).
Compute step_to_str (step_at P4 1).
Compute step_to_str (step_at P4 2).

(* Computes Y0.f + Y0.g; Class1 has field f and Class2 <: Class1 has field g. *)

Definition P5 : s_prg := match parse "class Object {  } class Class1 extends Object { int f; } class Class2 extends Class1 { int g; } let x := (Y0.f) in (x + (Y0.g))" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P5 0).
Compute step_to_str (step_at P5 1).
Compute step_to_str (step_at P5 2).
Compute step_to_str (step_at P5 3).
Compute step_to_str (step_at P5 4).
Compute step_to_str (step_at P5 5).

(* Computes Y0.f + Y1.f; Class1 has field f. *)

Definition P6 : s_prg := match parse "class Object {  } class Class1 extends Object { int f; } let x := (Y0.f) in (x + (Y1.f))" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P6 0).
Compute step_to_str (step_at P6 1).
Compute step_to_str (step_at P6 2).
Compute step_to_str (step_at P6 3).
Compute step_to_str (step_at P6 4).
Compute step_to_str (step_at P6 5).

(* Computes Y0.f + (Y1.f + Y2.f); Class1 has field f. *)

Definition P7 : s_prg := match parse "class Object {  } class Class1 extends Object { int f; } let x := (Y0.f) in let y := (Y1.f) in (x + (y + (Y2.f)))" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P7 0).
Compute step_to_str (step_at P7 1).
Compute step_to_str (step_at P7 2).
Compute step_to_str (step_at P7 3).
Compute step_to_str (step_at P7 4).
Compute step_to_str (step_at P7 5).
Compute step_to_str (step_at P7 6).
Compute step_to_str (step_at P7 7).
Compute step_to_str (step_at P7 8).

(* Computes Y0.f.g; Class1 has field f, Class2 has field g. *)

Definition P8 : s_prg := match parse "class Object {  } class Class1 extends Object { Class2 f; } class Class2 extends Object { int g; } ((Y0.f).g)" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P8 0).
Compute step_to_str (step_at P8 1).
Compute step_to_str (step_at P8 2).
Compute step_to_str (step_at P8 3).

(* Computes Y0.f.g; Class1 has fields f and g. *)

Definition P9 : s_prg := match parse "class Object {  } class Class1 extends Object { Class1 f; int g; } ((Y0.f).g)" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P9 0).
Compute step_to_str (step_at P9 1).
Compute step_to_str (step_at P9 2).
Compute step_to_str (step_at P9 3).

(* Computes Y1.f := Y0.f, with Y1.f evaluated after Y0.f; Class1 has field f. *)

Definition P10 : s_prg := match parse "class Object {  } class Class1 extends Object { Class1 f; } let x := (Y0.f) in (Y1.f := x)" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P10 0).
Compute step_to_str (step_at P10 1).
Compute step_to_str (step_at P10 2).
Compute step_to_str (step_at P10 3).
Compute step_to_str (step_at P10 4).

(* Computes Y0.f.f := Y1.f, with Y1.f evaluated before Y0.f (so Y0.f contains an ite); Class1 has field f. *)

Definition P11 : s_prg := match parse "class Object {  } class Class1 extends Object { Class1 f; } let x := (Y1.f) in let y := (Y0.f) in (y.f := x)" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P11 0).
Compute step_to_str (step_at P11 1).
Compute step_to_str (step_at P11 2).
Compute step_to_str (step_at P11 3).
Compute step_to_str (step_at P11 4).
Compute step_to_str (step_at P11 5).
Compute step_to_str (step_at P11 6).

(* Figure 1a from paper *)

Definition P12 : s_prg := match parse "
class Object { } 

class Void extends Object { } 

class Container extends Object {
  Object data;

  Void swap(Container c) := 
    if (c = null) then new Void 
    else 
      let e := (this.data) in 
      let foo := (this.data := (c.data)) in 
      let baz := (c.data := e) in 
      new Void; 
} 

let y0 := Y0 in 
let y1 := Y1 in 
(y0.swap[y1])" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P12 0).
Compute step_to_str (step_at P12 1).
Compute step_to_str (step_at P12 2).
Compute step_to_str (step_at P12 3).
Compute step_to_str (step_at P12 4).
Compute step_to_str (step_at P12 5).
Compute step_to_str (step_at P12 6).
Compute step_to_str (step_at P12 7).
Compute step_to_str (step_at P12 8).
Compute step_to_str (step_at P12 9).
Compute step_to_str (step_at P12 10).
Compute step_to_str (step_at P12 11).
Compute step_to_str (step_at P12 12).
Compute step_to_str (step_at P12 13).
Compute step_to_str (step_at P12 14).

(* Figure 1b from the paper *)

Definition P13 : s_prg := match parse "
class Object { } 

class Void extends Object { } 

class Node extends Object {
  int val;
  Node c0;
  Node c1;
  Node c2;

  int sum(Void foo) := 
    let s1 := (this.val) in 
    let s2 := (s1 + ((this.c0).val)) in 
    let s3 := (s2 + ((this.c1).val)) in 
    let s4 := (s3 + ((this.c2).val)) in 
    s4; 
} 

let y := Y0 in (y.sum[new Void])" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P13 0).
Compute step_to_str (step_at P13 1).
Compute step_to_str (step_at P13 2).
Compute step_to_str (step_at P13 3).
Compute step_to_str (step_at P13 4).
Compute step_to_str (step_at P13 5).
Compute step_to_str (step_at P13 6).
Compute step_to_str (step_at P13 7).
Compute step_to_str (step_at P13 8).
Compute step_to_str (step_at P13 9).
Compute step_to_str (step_at P13 10).
Compute step_to_str (step_at P13 11).
Compute step_to_str (step_at P13 12).
Compute step_to_str (step_at P13 13).
Compute step_to_str (step_at P13 14).
Compute step_to_str (step_at P13 15).
Compute step_to_str (step_at P13 16).
Compute step_to_str (step_at P13 17).
Compute step_to_str (step_at P13 18).

(* Figure 1c from the paper *)

Definition P14 : s_prg := match parse "
class Object { } 

class Void extends Object { } 

class LoopFrame extends Object { 
  Node n; 
  int i; 
} 

class Node extends Object { 
  int max; 
  Node next; 
  bool hasNullWithin(Void foo1) := 
    let f := new LoopFrame in 
    let foo2 := (f.n := (this.next)) in 
    let foo3 := (f.i := 1) in 
    let fPost := (this.doLoop[f]) in 
    ((fPost.n) = null); 

  LoopFrame doLoop(LoopFrame f) := 
    if ((f.n) = null) then f 
    else if ((this.max) < (f.i)) then f 
    else 
      let foo4 := (f.n := ((f.n).next)) in 
      let foo5 := (f.i := ((f.i) + 1)) in 
      (this.doLoop[f]); 
} 

let y := Y0 in 
let foo6 := (y.max := 4) in 
(y.hasNullWithin[new Void])" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P14 0).
Compute step_to_str (step_at P14 1).
Compute step_to_str (step_at P14 2).
Compute step_to_str (step_at P14 3).
Compute step_to_str (step_at P14 4).
Compute step_to_str (step_at P14 5).
Compute step_to_str (step_at P14 6).
Compute step_to_str (step_at P14 7).
Compute step_to_str (step_at P14 8).
Compute step_to_str (step_at P14 9).
Compute step_to_str (step_at P14 10).
Compute step_to_str (step_at P14 11).
Compute step_to_str (step_at P14 12).
Compute step_to_str (step_at P14 13).
Compute step_to_str (step_at P14 14).
Compute step_to_str (step_at P14 15).
Compute step_to_str (step_at P14 16).
Compute step_to_str (step_at P14 17).
Compute step_to_str (step_at P14 18).
Compute step_to_str (step_at P14 19).
Compute step_to_str (step_at P14 20).
Compute step_to_str (step_at P14 21).
Compute step_to_str (step_at P14 22).
Compute step_to_str (step_at P14 23).
Compute step_to_str (step_at P14 24).
Compute step_to_str (step_at P14 25).
Compute step_to_str (step_at P14 26).
Compute step_to_str (step_at P14 27).
Compute step_to_str (step_at P14 28).
Compute step_to_str (step_at P14 29).
Compute step_to_str (step_at P14 30).
Compute step_to_str (step_at P14 31).
Compute step_to_str (step_at P14 32).
Compute step_to_str (step_at P14 33).
Compute step_to_str (step_at P14 34).
Compute step_to_str (step_at P14 35).
Compute step_to_str (step_at P14 36).
Compute step_to_str (step_at P14 37).
Compute step_to_str (step_at P14 38).
Compute step_to_str (step_at P14 39).
Compute step_to_str (step_at P14 40).
Compute step_to_str (step_at P14 41).
Compute step_to_str (step_at P14 42).
Compute step_to_str (step_at P14 43).
Compute step_to_str (step_at P14 44).
Compute step_to_str (step_at P14 45).
Compute step_to_str (step_at P14 46).
Compute step_to_str (step_at P14 47).
Compute step_to_str (step_at P14 48).
Compute step_to_str (step_at P14 49).
Compute step_to_str (step_at P14 50).
Compute step_to_str (step_at P14 51).
Compute step_to_str (step_at P14 52).
Compute step_to_str (step_at P14 53).
Compute step_to_str (step_at P14 54).
Compute step_to_str (step_at P14 55).
Compute step_to_str (step_at P14 56).
Compute step_to_str (step_at P14 57).
Compute step_to_str (step_at P14 58).
Compute step_to_str (step_at P14 59).
Compute step_to_str (step_at P14 60).
Compute step_to_str (step_at P14 61).
Compute step_to_str (step_at P14 62).
Compute step_to_str (step_at P14 63).
Compute step_to_str (step_at P14 64).
Compute step_to_str (step_at P14 65).
Compute step_to_str (step_at P14 66).
Compute step_to_str (step_at P14 67).
Compute step_to_str (step_at P14 68).
Compute step_to_str (step_at P14 69).
Compute step_to_str (step_at P14 70).
Compute step_to_str (step_at P14 71).
Compute step_to_str (step_at P14 72).
Compute step_to_str (step_at P14 73).
Compute step_to_str (step_at P14 74).
Compute step_to_str (step_at P14 75).
Compute step_to_str (step_at P14 76).
Compute step_to_str (step_at P14 77).
Compute step_to_str (step_at P14 78).
Compute step_to_str (step_at P14 79).
Compute step_to_str (step_at P14 80).
Compute step_to_str (step_at P14 81).
Compute step_to_str (step_at P14 82).
Compute step_to_str (step_at P14 83).
Compute step_to_str (step_at P14 84).
Compute step_to_str (step_at P14 85).
Compute step_to_str (step_at P14 86).
Compute step_to_str (step_at P14 87).
Compute step_to_str (step_at P14 88).

(* Check for correctness... *)
Definition P15 : s_prg := match parse "class Object { } class N extends Object { N n; } let a := Y0 in let b := (a.n) in let foo := (a.n := null) in let c := (b.n) in c" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P15 0).
Compute step_to_str (step_at P15 1).
Compute step_to_str (step_at P15 2).
Compute step_to_str (step_at P15 3).
Compute step_to_str (step_at P15 4).
Compute step_to_str (step_at P15 5).
Compute step_to_str (step_at P15 6).
Compute step_to_str (step_at P15 7).
Compute step_to_str (step_at P15 8).

Compute (step_at P15 7).

(* Check for correctness... *)
Definition P16 : s_prg :=  match parse "class Object { } class N extends Object { N n; } let a := Y0 in let b := Y1 in let foo := (a.n := null) in let c := (b.n) in c" with
| ([], SomeE prg) => prg
| _ => s_prg_l [] (s_expr_var "")
end.

Compute step_to_str (step_at P16 0).
Compute step_to_str (step_at P16 1).
Compute step_to_str (step_at P16 2).
Compute step_to_str (step_at P16 3).
Compute step_to_str (step_at P16 4).
Compute step_to_str (step_at P16 5).
Compute step_to_str (step_at P16 6).
Compute step_to_str (step_at P16 7).
