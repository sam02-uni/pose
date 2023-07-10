From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import FSets.FMapWeakList.
From Coq Require Import Structures.DecidableType.
From Coq Require Import Structures.DecidableTypeEx.
From Hammer Require Import Tactics.
From POSE Require Import Syntax.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(************************** Auxiliary definitions **********************)

Module String_as_MDT <: MiniDecidableType.
  Definition t := string.
  Definition eq_dec := string_dec.
End String_as_MDT.

Module String_as_UDT <: UsualDecidableType := Make_UDT(String_as_MDT).
Module String_as_DT <: DecidableType := UDT_to_DT(String_as_UDT).

Module RefC_as_MDT <: MiniDecidableType.
  Definition t := s_ref_c.

  Lemma eq_symb_dec : forall s1 s2 : s_symb, { s1 = s2 } + { s1 <> s2 }.
  Proof.
    intro s1. induction s1. intro s2; destruct s2.
    - assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. sauto.
    - now right.
    - destruct s2.
      + now right.
      +  assert ({s1 = s2} + {s1 <> s2}) by apply IHs1. assert ({s = s0} + {s <> s0}) by apply string_dec. sauto.
  Defined.
  
  Theorem eq_dec : forall x y : s_ref_c, { x = y } + { x <> y }.
  Proof.
    intro x. destruct x. intro y. destruct y.
    - now left.
    - now right.
    - now right.
    - intro y. destruct y.
      + now right.
      + destruct s. destruct s0. assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. sauto.
      + now right.
    - intro y. destruct y.
      + now right.
      + now right.
      + destruct s. destruct s0.
        * assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. sauto.
        * now right.
        * assert ({s_symb_fld s s1 = s0} + {s_symb_fld s s1<> s0}) by apply eq_symb_dec. sauto.
  Defined.
End RefC_as_MDT.

Module RefC_as_UDT <: UsualDecidableType := Make_UDT(RefC_as_MDT).
Module RefC_as_DT <: DecidableType := UDT_to_DT(RefC_as_UDT).

Module MapString := FMapWeakList.Make(String_as_DT).
Module MapRefC := FMapWeakList.Make(RefC_as_DT).
Module MapNat := FMapWeakList.Make(Nat_as_DT).
