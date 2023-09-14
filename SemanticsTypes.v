From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.
From Coq Require Import Relations.Operators_Properties.
From POSE Require Import Aux.
From POSE Require Import Syntax.

Open Scope string_scope.
Open Scope list_scope.
Open Scope lazy_bool_scope.

Set Implicit Arguments.
Set Asymmetric Patterns.

(**************** Types for the operational semantics **************)

(* The object memory is a finite map from field names
   to values. *)
Definition object_memory : Type := MapString.t s_val.

(* An object has a memory and a class name. *)
Definition object : Type := object_memory * string.

(* A heap is a finite map from reference constant
   (excluded null) to objects. *)
Definition heap : Type := MapRefC.t object.

(* A path condition *)
Definition path_condition : Type := list s_val.

(* A configuration of the operational semantics, 
   formed by a program, a heap, a path condition, 
   and the next expression that must be stepped *) 
Definition config : Type := s_prg * heap * path_condition * s_expr.

(* The empty heap *)
Definition H0 : heap := MapRefC.empty object.

(* The empty path condition *)
Definition Σ0 : path_condition := [].

(* The initial configuration of an execution *)
Definition config_initial (P : s_prg) : config :=
  let e0 := expression P in
  (P, H0, Σ0, e0).

(**************** Related functions and predicates **************)

(* Object getters *)

Definition o_memory (o : object) : object_memory := 
  match o with
  | (M, _) => M
  end.

Definition o_class_name (o : object) : string :=
  match o with
  | (_, c) => c
  end.

Definition get (o : object) (f : string) : option s_val :=
  MapString.find f (o_memory o).

(* Heap getters *)

Definition obj_at (H : heap) (u : s_ref_c) : option object :=
  MapRefC.find u H.

Definition obj_class_at (H : heap) (u : s_ref_c) : option string :=
  match obj_at H u with
  | None => None
  | Some o => Some (o_class_name o)
  end.

Definition has_obj (H : heap) (u : s_ref_c) (o : object) : Prop :=
  obj_at H u = Some o.

(* Is a symbol unresolved? A symbol is unresolved 
   when it has no associated symbolic object in 
   the heap. Both declarative and computable versions. *)

Definition unresolved (H : heap) (s : s_symb) : Prop :=
  obj_at H (s_ref_c_symb s) = None.

Definition unresolved_c (H : heap) (s : s_symb) : bool :=
  negb (MapRefC.mem (s_ref_c_symb s) H).

(* Computable object (deep) equality *)

Definition object_eqb (o1 o2 : object) : bool :=
  String.eqb (o_class_name o1) (o_class_name o2) && MapString.equal s_val_eqb (o_memory o1) (o_memory o2).

(* The subclass relation, both declarative and computable *)

Section SubclassDefs.

Definition subclass_immediate (P : s_prg) : relation string :=
  fun c_possible_sub c_possible_sup : string => Exists (fun C : s_dc_c => match C with
  | s_dc_c_l c c_sup _ _ => c_possible_sub = c /\ c_possible_sup = c_sup
  end) (classes P).

Definition subclass (P : s_prg) : relation string := 
  clos_refl_trans string (subclass_immediate P).

Let Fixpoint superclass_immediate_aux (c_sub : string) (Cs : list s_dc_c) : option string :=
  match Cs with
  | [] => None
  | C :: other_Cs => match C with
    | s_dc_c_l c c_sup _ _ => if (String.eqb c_sub c) then Some c_sup else superclass_immediate_aux c_sub other_Cs
    end
  end.

Definition superclass_immediate (P : s_prg) (c_sub : string) : option string :=
  superclass_immediate_aux c_sub (classes P).

Definition subclass_immediate_c (P : s_prg) (c_possible_sub c_possible_sup : string) : bool :=
  match superclass_immediate P c_possible_sub with
  | None => false
  | Some c_sup => String.eqb c_possible_sup c_sup
  end.

Let Fixpoint subclass_c_aux (P : s_prg) (c_possible_sub c_possible_sup : string) (Cs : list s_dc_c) (n : nat) : bool :=
  if (String.eqb c_possible_sub c_possible_sup) then true else
  match n with
  | 0 => false
  | S n' => match superclass_immediate P c_possible_sub with
    | None => false
    | Some c_sup_immediate => subclass_c_aux P c_sup_immediate c_possible_sup Cs n'
    end
  end.

Definition subclass_c (P : s_prg) (c_possible_sub c_possible_sup : string) : bool :=
  subclass_c_aux P c_possible_sub c_possible_sup (classes P) (length (classes P)).

End SubclassDefs.


(* Does class C declare a field with name f? 
   Both declarative and computable versions. *)

Definition class_has_field (C : s_dc_c) (f : string) : Prop :=
  Exists (fun F => field_name F = f) (fields C).

Definition class_has_field_c (C : s_dc_c) (f : string) : bool :=
  existsb (fun F => String.eqb (field_name F) f) (fields C).

(* Does class C declare a method with name m? 
   Both declarative and computable versions. *)

Definition class_has_method (C : s_dc_c) (m : string) : Prop :=
  Exists (fun D => method_name D = m) (methods C).

Definition class_has_method_c (C : s_dc_c) (m : string) : bool :=
  existsb (fun D => String.eqb (method_name D) m) (methods C).

(* Does class with name c declare a method with name m?
   Both declarative and computable versions. *)

Section HasMethodDefs.
  
Let Fixpoint has_method_aux (Cs : list s_dc_c) (c : string) (m : string) : Prop :=
  match Cs with
  | [] => False
  | C :: other_Cs => (class_name C = c /\ class_has_method C m) \/ has_method_aux other_Cs c m
  end.

Definition has_method (P : s_prg) (c : string) (m : string) : Prop :=
  has_method_aux (classes P) c m.

Let Fixpoint has_method_c_aux (Cs : list s_dc_c) (c : string) (m : string) : bool :=
  match Cs with
  | [] => false
  | C :: other_Cs => (String.eqb (class_name C) c && class_has_method_c C m) || has_method_c_aux other_Cs c m
  end.

Definition has_method_c (P : s_prg) (c : string) (m : string) : bool :=
  has_method_c_aux (classes P) c m.

End HasMethodDefs.


Section XdeclDefs.
  
(* Gets the declaration of the method with name m in 
   class with name c, if such declaration exists in 
   program P. *)
  
Let Fixpoint mdecl_list_dc_m (Ds : list s_dc_m) (m : string) : option s_dc_m :=
  match Ds with
  | [] => None
  | D :: other_Ds => if String.eqb (method_name D) m then Some D else mdecl_list_dc_m other_Ds m
  end.

Let Fixpoint mdecl_list_dc_c (Cs : list s_dc_c) (c m : string) : option s_dc_m :=
  match Cs with
  | [] => None
  | C :: other_Cs => if String.eqb (class_name C) c then mdecl_list_dc_m (methods C) m else mdecl_list_dc_c other_Cs c m
  end.

Definition mdecl (P : s_prg) (c m : string) : option s_dc_m :=
  mdecl_list_dc_c (classes P) c m.

(* Gets from program P the declaration of class with 
   name c, if such declaration exists *)

Let Fixpoint cdecl_list_dc_c (Cs : list s_dc_c) (c : string) : option s_dc_c :=
  match Cs with
  | [] => None
  | C :: other_Cs => if (String.eqb (class_name C) c) then Some C else cdecl_list_dc_c other_Cs c
  end.

Definition cdecl (P : s_prg) (c : string) : option s_dc_c :=
  cdecl_list_dc_c (classes P) c.

(* Gets from class C the declaration of field 
   with name f, if such declaration exists *)

Let Fixpoint fdecl_aux (Fs : list s_dc_v) (f : string) : option s_dc_v :=
  match Fs with
  | [] => None
  | (s_dc_v_l t f') :: other_Fs => if (String.eqb f f') then Some (s_dc_v_l t f') else fdecl_aux other_Fs f
  end.

Definition fdecl (C : s_dc_c) (fname : string) : option s_dc_v :=
  fdecl_aux (fields C) fname. 

End XdeclDefs.

(* The implementation of a method with
   name m from a class with name c_possible_sup 
   is visible to a class c_possible_sub.
   Both declarative and computable versions. *)

Definition sees_method (P : s_prg) (m : string) : relation string :=
  fun (c_possible_sub c_possible_sup : string) => 
    subclass P c_possible_sub c_possible_sup /\ 
    has_method P c_possible_sup m /\
    Forall (fun C => 
      (class_name C) = c_possible_sub \/
      (class_name C) = c_possible_sup \/
      ~(subclass P (class_name C) c_possible_sup) \/
      ~(subclass P c_possible_sub (class_name C)) \/ 
      ~(has_method P (class_name C) m)) (classes P).

Definition sees_method_c (P : s_prg) (m : string) (c_possible_sub c_possible_sup : string) : bool :=
  subclass_c P c_possible_sub c_possible_sup &&
  has_method_c P c_possible_sup m &&
  forallb (fun C => 
    (String.eqb (class_name C) c_possible_sub) ||
    (String.eqb (class_name C) c_possible_sup) ||
    negb (subclass_c P (class_name C) c_possible_sup) ||
    negb (subclass_c P c_possible_sub (class_name C)) || 
    negb (has_method_c P (class_name C) m)) (classes P).

(* Class with name c_possible_sub receives the 
   implementation of method with name m from class 
   with name c_possible_sup (i.e, the implementation 
   is visible to c_possible_sub and c_possible_sub
   does not redefine it). Both declarative and 
   computable versions. *)
Definition recv_method (P : s_prg) (m : string) : relation string :=
  fun (c_possible_sub c_possible_sup : string) => 
    ((~c_possible_sub = c_possible_sup) /\ sees_method P m c_possible_sub c_possible_sup /\ (~has_method P c_possible_sub m)) \/
    (c_possible_sub = c_possible_sup /\ has_method P c_possible_sub m).

Definition recv_method_c (P : s_prg) (m : string) (c_possible_sub c_possible_sup : string) : bool :=
  (negb (String.eqb c_possible_sub c_possible_sup) && sees_method_c P m c_possible_sub c_possible_sup && negb (has_method_c P c_possible_sub m)) ||
  (String.eqb c_possible_sub c_possible_sup && has_method_c P c_possible_sub m).

(* Calculates the class from which another class c 
   receives a method m, if there is one *)
Definition method_provider (P : s_prg) (m : string) (c : string) : option string :=
  option_map class_name (find (fun C' => recv_method_c P m c (class_name C')) (classes P)).

Section ClassWithFieldDefs.

(* Finds the class declared in P which declares a field with name f *)

Let Fixpoint class_with_field_aux (Cs : list s_dc_c) (f : string) : option s_dc_c :=
  match Cs with
  | [] => None
  | C :: other_Cs => if class_has_field_c C f then Some C else class_with_field_aux other_Cs f
  end.

Definition class_with_field (P : s_prg) (f : string) : option s_dc_c := 
  class_with_field_aux (classes P) f.

End ClassWithFieldDefs.

(* Returns the names of all the classes declared in P which declare 
   a method with name m *)
Definition implementors (P : s_prg) (m : string) : list string :=
  map class_name (filter (fun C => class_has_method_c C m) (classes P)).

(* Class c overrides definition of method m in class c', i.e., 
   c differs from c', c sees m from c', and c redefines m. *)
Definition overrides (P : s_prg) (m : string) : relation string :=
  fun (c c' : string) =>
    sees_method P m c c' /\ has_method P m c /\ c <> c'.

(* Returns the names of all the classes that override a method m declared
   in a class with name c' (computable version of overrides. *)
Definition overriders (P : s_prg) (m : string) (c' : string) : list string :=
  map class_name (filter (fun C => sees_method_c P m (class_name C) c' && class_has_method_c C m && negb (String.eqb (class_name C) c')) (classes P)).

Section NewRefineObjDecls.

(* Object o is a new concrete object of class with 
   name c (declarative and computable). *)

Definition new_obj (P : s_prg) (c : string) (o : object) : Prop :=
  forall f C' t, 
    ((exists c', subclass P c c' /\ cdecl P c' = Some C' /\
    fdecl C' f = Some (s_dc_v_l t f)) -> get o f = Some (ini t)) /\
    (~(exists c', subclass P c c' /\ cdecl P c' = Some C' /\
    fdecl C' f = Some (s_dc_v_l t f)) -> get o f = None).

(* Object o is a new symbolic object of class with 
   name c (declarative and computable). *)

Definition new_obj_symb  (P : s_prg) (c : string) (o : object) : Prop :=
  forall f C' t, 
    ((exists c', subclass P c c' /\ cdecl P c' = Some C' /\
    fdecl C' f = Some (s_dc_v_l t f)) -> get o f = Some s_val_unassumed) /\
    (~(exists c', subclass P c c' /\ cdecl P c' = Some C' /\
    fdecl C' f = Some (s_dc_v_l t f)) -> get o f = None).

Let Fixpoint add_fields (M : object_memory) (Fs : list s_dc_v) (symbolic : bool) : object_memory :=
  match Fs with
  | [] => M
  | F :: other_Fs => let M' := add_fields M other_Fs symbolic in
    MapString.add (field_name F) (if symbolic then s_val_unassumed else ini (field_type F)) M'
  end.

Let Fixpoint new_obj_memory (P : s_prg) (c : string) (Cs : list s_dc_c) (symbolic : bool) : object_memory :=
  match Cs with 
  | [] => MapString.empty s_val
  | C :: other_Cs => let M' := new_obj_memory P c other_Cs symbolic in
    if subclass_c P c (class_name C) then add_fields M' (fields C) symbolic else M'
  end.

Definition new_obj_c (P : s_prg) (c : string) : object :=
  (new_obj_memory P c (classes P) false, c).

Definition new_obj_symb_c (P : s_prg) (c : string) : object :=
  (new_obj_memory P c (classes P) true, c).

(* Symbolic object o' of class with name c_sub refines 
   symbolic object o of class with name c (both declarative
   and computable). *)

Definition refine_obj_symb (P : s_prg) (c c_sub: string) (o o' : object) : Prop :=
  forall f C' type, 
    ((exists c', subclass P c c' /\ cdecl P c' = Some C' /\
    fdecl C' f = Some (s_dc_v_l type f)) -> get o f = get o' f) /\
    ((exists c', subclass P c_sub c' /\ subclass P c' c /\ 
    ~(c = c') /\ cdecl P c' = Some C' /\ 
    fdecl C' f = Some (s_dc_v_l type f)) -> get o f = Some s_val_unassumed) /\
    (~(exists c', subclass P c_sub c' /\ cdecl P c' = Some C' /\
    fdecl C' f = Some (s_dc_v_l type f)) -> get o f = None).

Let Fixpoint refine_obj_symb_memory (P : s_prg) (c c_sub : string) (M : object_memory) (Cs : list s_dc_c) : object_memory :=
  match Cs with 
  | [] => M
  | C :: other_Cs => let M' := refine_obj_symb_memory P c c_sub M other_Cs in
    if (subclass_c P (class_name C) c) && (subclass_c P c_sub (class_name C)) && negb (String.eqb (class_name C) c) then add_fields M' (fields C) true else M'
  end.

Definition refine_obj_symb_c (P : s_prg) (c_sub: string) (o : object) : object := 
  (refine_obj_symb_memory P (o_class_name o) c_sub (o_memory o) (classes P), c_sub).

End NewRefineObjDecls.

(* Various modifiers *)

(* Updates the value of a field f in an object o. *)
Definition upd_obj (o : object) (f : string) (σ : s_val) : object :=
  (MapString.add f σ (o_memory o), o_class_name o).

(* Replaces in heap H the object at position pointed 
   by u with an object o. *)
Definition repl_obj (H : heap) (u : s_ref_c) (o : object) : heap :=
  match u with
  | s_ref_c_null => H
  | _ => MapRefC.add u o H
  end.

(* Adds to heap H a concrete object o, returns
   the new heap and the location of the added
   object. *)
Definition add_obj (H : heap) (o : object) : heap * s_ref_c :=
  let next := s_ref_c_loc (s_loc_l (MapRefC.cardinal H)) in
  (MapRefC.add next o H, next).

(* Add to heap H a symbolic object o; the object is pointed 
   by symbol s *)
Definition add_obj_symb (H : heap) (s : s_symb) (o : object) : heap :=
  MapRefC.add (s_ref_c_symb s) o H.

