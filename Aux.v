From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import FSets.FMapWeakList.
From Coq Require Import MSets.MSetWeakList.
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

Module ListString_as_MDT <: MiniDecidableType.
  Definition t := list string.
  
  Theorem eq_dec : forall l1 l2 : list string, { l1 = l2 } + { l1 <> l2 }.
  Proof.
    intro l1. induction l1. intro l2. destruct l2. 
    - auto.
    - sauto.
    - intro l2. destruct l2. 
      * sauto. 
      * assert ({a = s} + {a <> s}) by apply string_dec. sauto. 
  Defined.
End ListString_as_MDT.

Module SSymb_as_MDT <:  MiniDecidableType.
  Definition t := s_symb.
  
  Theorem eq_dec : forall s1 s2 : s_symb, { s1 = s2 } + { s1 <> s2 }.
  Proof.
    intro s1. induction s1. intro s2. destruct s2.
    - assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. sauto.
    - sauto.
    - intro s2. destruct s2.
      * assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. sauto.
      * assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. assert ({l = l0} + {l <> l0}) by apply ListString_as_MDT.eq_dec. sauto.
  Defined.
End SSymb_as_MDT.
  
Module RefC_as_MDT <: MiniDecidableType.
  Definition t := s_ref_c.

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
        * assert ({s_symb_fld n l = s0} + {s_symb_fld n l <> s0}) by apply SSymb_as_MDT.eq_dec. sauto.
  Defined.
End RefC_as_MDT.

Module RefC_as_UDT <: UsualDecidableType := Make_UDT(RefC_as_MDT).
Module RefC_as_DT <: DecidableType := UDT_to_DT(RefC_as_UDT).

Module MapString := FMapWeakList.Make(String_as_DT).
Module MapRefC := FMapWeakList.Make(RefC_as_DT).
Module MapNat := FMapWeakList.Make(Nat_as_DT).

From Coq Require Import Structures.Equalities.

Module SSymb_as_DT <: DecidableTypeOrig'.
  Definition t := s_symb.
  Definition eq := @eq s_symb.
  
  Theorem eq_dec : forall s1 s2 : s_symb, { s1 = s2 } + { s1 <> s2 }.
  Proof.
    intro s1. induction s1. intro s2. destruct s2.
    - assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. sauto.
    - sauto.
    - intro s2. destruct s2.
      * assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. sauto.
      * assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. assert ({l = l0} + {l <> l0}) by apply ListString_as_MDT.eq_dec. sauto.
  Defined.

  Theorem eq_equiv : Equivalence eq.
  Proof.
    split. congruence. congruence. congruence.
  Defined.

  Theorem eq_refl : forall s : s_symb, s = s.
  Proof.
    split. 
  Defined.

  Theorem eq_sym : forall s1 s2 : s_symb, s1 = s2 -> s2 = s1.
  Proof.
    intros. destruct s1.
    - destruct s2.
      * inversion H. tauto.
      * auto.
    - destruct s2.
      * auto.
      * inversion H. tauto.
  Defined.

  Theorem eq_trans : forall s1 s2 s3 : s_symb, s1 = s2 -> s2 = s3 -> s1 = s3.
  Proof.
    intros. destruct s1.
    - destruct s2.
      * destruct s3.
        -- inversion H. inversion H0. tauto.
        -- sauto.
      * destruct s3.
        -- sauto.
        -- sauto.
    - destruct s2.
      * destruct s3.
        -- sauto.
        -- sauto.
      * destruct s3. 
        -- sauto.
        -- inversion H. inversion H0. tauto.
  Defined.
        
End SSymb_as_DT.

Module SetSymb := MSetWeakList.Make(SSymb_as_DT).

Module Loc_as_DT <: DecidableTypeOrig'.
  Definition t := s_loc.
  Definition eq := @eq s_loc.
  
  Theorem eq_dec : forall l1 l2 : s_loc, { l1 = l2 } + { l1 <> l2 }.
  Proof.
    intro l1. induction l1. intro l2. destruct l2. assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. sauto.
  Defined.

  Theorem eq_equiv : Equivalence eq.
  Proof.
    split. congruence. congruence. congruence.
  Defined.

  Theorem eq_refl : forall l : s_loc, l = l.
  Proof.
    split. 
  Defined.

  Theorem eq_sym : forall l1 l2 : s_loc, l1 = l2 -> l2 = l1.
  Proof.
    intros. destruct l1.
    - destruct l2.
      * inversion H. tauto.
  Defined.

  Theorem eq_trans : forall l1 l2 l3 : s_loc, l1 = l2 -> l2 = l3 -> l1 = l3.
  Proof.
    intros. destruct l1.
    - destruct l2.
      * destruct l3.
        -- inversion H. inversion H0. tauto.
  Defined.
        
End Loc_as_DT.

Module SetLoc := MSetWeakList.Make(Loc_as_DT).

(* Difference strings *)
Definition dstring := list string.

Definition from_string (s : string) : dstring := [s].

Fixpoint add_last (f : dstring) (s : string): dstring :=
  match f with
  | [] => [s]
  | [s'] => [String.append s' s]
  | s' :: f' => s' :: (add_last f' s)
  end.
                      
Definition append (f g : dstring) : dstring :=
  match g with
  | [] => f
  | s :: g' => match f with
               | [] => g
               | s' :: f' => if Nat.ltb 30 ((String.length s) + (String.length (last f' ""))) then f ++ g else (add_last f s) ++ g'
               end
  end.

Fixpoint dconcat (s : dstring) (l : list dstring) : dstring :=
  match l with
  | [] => from_string ""
  | [f] => f
  | f :: l' => append (append f s) (dconcat s l')
  end.

(* Direct translation to string: use only with short strings. *)
Definition to_string (s : dstring) : string :=
  String.concat "" s.
