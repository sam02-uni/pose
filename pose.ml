
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x0, _) -> x0

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y0) -> y0

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l0 m =
  match l0 with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n1 m =
   match n1 with
   | O -> m
   | S p0 -> S (add p0 m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n1 m =
  match n1 with
  | O -> O
  | S p0 -> add m (mul p0 m)

(** val sub : nat -> nat -> nat **)

let rec sub n1 m =
  match n1 with
  | O -> n1
  | S k -> (match m with
            | O -> n1
            | S l0 -> sub k l0)

(** val divmod : nat -> nat -> nat -> nat -> nat * nat **)

let rec divmod x0 y0 q u =
  match x0 with
  | O -> (q, u)
  | S x' ->
    (match u with
     | O -> divmod x' y0 (S q) y0
     | S u' -> divmod x' y0 q u')

(** val div : nat -> nat -> nat **)

let div x0 y0 = match y0 with
| O -> y0
| S y' -> fst (divmod x0 y' O y')

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f x0 y0 =
  f y0 x0

module type DecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type DecidableTypeOrig =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type UsualDecidableTypeOrig =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type MiniDecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module Make_UDT =
 functor (M:MiniDecidableType) ->
 struct
  type t = M.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    M.eq_dec
 end

module Nat =
 struct
  (** val succ : nat -> nat **)

  let succ x0 =
    S x0

  (** val sub : nat -> nat -> nat **)

  let rec sub n1 m =
    match n1 with
    | O -> n1
    | S k -> (match m with
              | O -> n1
              | S l0 -> sub k l0)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n1 m =
    match n1 with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n1 m =
    match n1 with
    | O -> true
    | S n' -> (match m with
               | O -> false
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n1 m =
    leb (S n1) m

  (** val max : nat -> nat -> nat **)

  let rec max n1 m =
    match n1 with
    | O -> m
    | S n' -> (match m with
               | O -> n1
               | S m' -> S (max n' m'))

  (** val divmod : nat -> nat -> nat -> nat -> nat * nat **)

  let rec divmod x0 y0 q u =
    match x0 with
    | O -> (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y0 (S q) y0
       | S u' -> divmod x' y0 q u')

  (** val modulo : nat -> nat -> nat **)

  let modulo x0 = function
  | O -> x0
  | S y' -> sub y' (snd (divmod x0 y' O y'))

  (** val eq_dec : nat -> nat -> bool **)

  let rec eq_dec n1 m =
    match n1 with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n2 -> (match m with
               | O -> false
               | S n3 -> eq_dec n2 n3)
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p0 -> XO (succ p0)
  | XO p0 -> XI p0
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x0 y0 =
    match x0 with
    | XI p0 ->
      (match y0 with
       | XI q -> XO (add_carry p0 q)
       | XO q -> XI (add p0 q)
       | XH -> XO (succ p0))
    | XO p0 ->
      (match y0 with
       | XI q -> XI (add p0 q)
       | XO q -> XO (add p0 q)
       | XH -> XI p0)
    | XH -> (match y0 with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x0 y0 =
    match x0 with
    | XI p0 ->
      (match y0 with
       | XI q -> XI (add_carry p0 q)
       | XO q -> XO (add_carry p0 q)
       | XH -> XI (succ p0))
    | XO p0 ->
      (match y0 with
       | XI q -> XO (add_carry p0 q)
       | XO q -> XI (add p0 q)
       | XH -> XO (succ p0))
    | XH ->
      (match y0 with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x0 y0 =
    match x0 with
    | XI p0 -> add y0 (XO (mul p0 y0))
    | XO p0 -> XO (mul p0 y0)
    | XH -> y0

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p0 a =
    match p0 with
    | XI p1 -> op a (iter_op op p1 (op a a))
    | XO p1 -> iter_op op p1 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x0 =
    iter_op Coq__1.add x0 (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x0 -> succ (of_succ_nat x0)
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n1 m =
    match n1 with
    | N0 -> m
    | Npos p0 -> (match m with
                  | N0 -> n1
                  | Npos q -> Npos (Pos.add p0 q))

  (** val mul : n -> n -> n **)

  let mul n1 m =
    match n1 with
    | N0 -> N0
    | Npos p0 -> (match m with
                  | N0 -> N0
                  | Npos q -> Npos (Pos.mul p0 q))

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p0 -> Pos.to_nat p0

  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')
 end

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| [] -> default
| x0 :: _ -> x0

(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l0 d0 =
  match l0 with
  | [] -> d0
  | a :: l1 -> (match l1 with
                | [] -> a
                | _ :: _ -> last l1 d0)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x0 :: l' -> app (rev l') (x0 :: [])

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x0 :: l1 -> app x0 (concat l1)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t1 -> (f a) :: (map f t1)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l0 a0 =
  match l0 with
  | [] -> a0
  | b0 :: t1 -> fold_left f t1 (f a0 b0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b0 :: t1 -> f b0 (fold_right f a0 t1)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l1 -> (||) (f a) (existsb f l1)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l1 -> (&&) (f a) (forallb f l1)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x0 :: l1 -> if f x0 then x0 :: (filter f l1) else filter f l1

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x0 :: tl0 -> if f x0 then Some x0 else find f tl0

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n1 p0 =
    match n1 with
    | O -> zero
    | S n' ->
      (match p0 with
       | XI p' -> shift true (loop n' p')
       | XO p' -> shift false (loop n' p')
       | XH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p0 -> ascii_of_pos p0

(** val ascii_of_nat : nat -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b0 :: l' ->
  N.add (if b0 then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> nat **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val length0 : string -> nat **)

let rec length0 s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> O)
    (fun _ s' -> S (length0 s'))
    s



type s_ty =
| S_ty_bool
| S_ty_int
| S_ty_class of string

type s_bool =
| S_bool_true
| S_bool_false

type s_int = nat
  (* singleton inductive, whose constructor was s_int_l *)

type s_loc = nat
  (* singleton inductive, whose constructor was s_loc_l *)

type s_symb =
| S_symb_expr of nat
| S_symb_fld of nat * string list

type s_prim_c =
| S_prim_c_bool of s_bool
| S_prim_c_int of s_int
| S_prim_c_symb of s_symb

type s_ref_c =
| S_ref_c_null
| S_ref_c_loc of s_loc
| S_ref_c_symb of s_symb

type s_val =
| S_val_unassumed
| S_val_prim_c of s_prim_c
| S_val_ref_c of s_ref_c
| S_val_add of s_val * s_val
| S_val_lt of s_val * s_val
| S_val_eq of s_val * s_val
| S_val_subtype of s_val * s_ty
| S_val_field of s_symb * string * s_symb
| S_val_ite of s_val * s_val * s_val

type s_expr =
| S_expr_var of string
| S_expr_val of s_val
| S_expr_new of string
| S_expr_getfield of s_expr * string
| S_expr_putfield of s_expr * string * s_expr
| S_expr_let of string * s_expr * s_expr
| S_expr_add of s_expr * s_expr
| S_expr_lt of s_expr * s_expr
| S_expr_eq of s_expr * s_expr
| S_expr_instanceof of s_expr * string
| S_expr_if of s_expr * s_expr * s_expr
| S_expr_invoke of s_expr * string * s_expr

type s_dc_v =
| S_dc_v_l of s_ty * string

type s_dc_m =
| S_dc_m_l of s_ty * string * s_dc_v * s_expr

type s_dc_c =
| S_dc_c_l of string * string * s_dc_v list * s_dc_m list

type s_prg =
| S_prg_l of s_dc_c list * s_expr

(** val cObject : s_dc_c **)

let cObject =
  S_dc_c_l ("Object", "", [], [])

(** val classes : s_prg -> s_dc_c list **)

let classes = function
| S_prg_l (cs, _) -> cs

(** val expression : s_prg -> s_expr **)

let expression = function
| S_prg_l (_, e) -> e

(** val class_name : s_dc_c -> string **)

let class_name = function
| S_dc_c_l (c1, _, _, _) -> c1

(** val superclass_name : s_dc_c -> string **)

let superclass_name = function
| S_dc_c_l (_, s, _, _) -> s

(** val fields : s_dc_c -> s_dc_v list **)

let fields = function
| S_dc_c_l (_, _, fs, _) -> fs

(** val methods : s_dc_c -> s_dc_m list **)

let methods = function
| S_dc_c_l (_, _, _, ds) -> ds

(** val method_name : s_dc_m -> string **)

let method_name = function
| S_dc_m_l (_, m, _, _) -> m

(** val field_type : s_dc_v -> s_ty **)

let field_type = function
| S_dc_v_l (t1, _) -> t1

(** val field_name : s_dc_v -> string **)

let field_name = function
| S_dc_v_l (_, n1) -> n1

(** val s_bool_eqb : s_bool -> s_bool -> bool **)

let s_bool_eqb b1 b2 =
  match b1 with
  | S_bool_true -> (match b2 with
                    | S_bool_true -> true
                    | S_bool_false -> false)
  | S_bool_false ->
    (match b2 with
     | S_bool_true -> false
     | S_bool_false -> true)

(** val s_int_eqb : s_int -> s_int -> bool **)

let s_int_eqb =
  Nat.eqb

(** val list_string_eqb : string list -> string list -> bool **)

let rec list_string_eqb l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | s1 :: l1' ->
    (match l2 with
     | [] -> false
     | s2 :: l2' -> (&&) ((=) s1 s2) (list_string_eqb l1' l2'))

(** val s_symb_eqb : s_symb -> s_symb -> bool **)

let s_symb_eqb s1 s2 =
  match s1 with
  | S_symb_expr n1 ->
    (match s2 with
     | S_symb_expr n2 -> Nat.eqb n1 n2
     | S_symb_fld (_, _) -> false)
  | S_symb_fld (n1, l1) ->
    (match s2 with
     | S_symb_expr _ -> false
     | S_symb_fld (n2, l2) -> (&&) (Nat.eqb n1 n2) (list_string_eqb l1 l2))

(** val s_prim_c_eqb : s_prim_c -> s_prim_c -> bool **)

let s_prim_c_eqb p1 p2 =
  match p1 with
  | S_prim_c_bool b1 ->
    (match p2 with
     | S_prim_c_bool b2 -> s_bool_eqb b1 b2
     | _ -> false)
  | S_prim_c_int n1 ->
    (match p2 with
     | S_prim_c_int n2 -> s_int_eqb n1 n2
     | _ -> false)
  | S_prim_c_symb s1 ->
    (match p2 with
     | S_prim_c_symb s2 -> s_symb_eqb s1 s2
     | _ -> false)

(** val s_loc_eqb : s_loc -> s_loc -> bool **)

let s_loc_eqb =
  Nat.eqb

(** val s_ref_c_eqb : s_ref_c -> s_ref_c -> bool **)

let s_ref_c_eqb u1 u2 =
  match u1 with
  | S_ref_c_null -> (match u2 with
                     | S_ref_c_null -> true
                     | _ -> false)
  | S_ref_c_loc l1 ->
    (match u2 with
     | S_ref_c_loc l2 -> s_loc_eqb l1 l2
     | _ -> false)
  | S_ref_c_symb s1 ->
    (match u2 with
     | S_ref_c_symb s2 -> s_symb_eqb s1 s2
     | _ -> false)

(** val s_ty_eqb : s_ty -> s_ty -> bool **)

let s_ty_eqb t1 t2 =
  match t1 with
  | S_ty_bool -> (match t2 with
                  | S_ty_bool -> true
                  | _ -> false)
  | S_ty_int -> (match t2 with
                 | S_ty_int -> true
                 | _ -> false)
  | S_ty_class c1 -> (match t2 with
                      | S_ty_class c2 -> (=) c1 c2
                      | _ -> false)

(** val s_val_eqb : s_val -> s_val -> bool **)

let rec s_val_eqb _UU03c3_1 _UU03c3_2 =
  match _UU03c3_1 with
  | S_val_unassumed ->
    (match _UU03c3_2 with
     | S_val_unassumed -> true
     | _ -> false)
  | S_val_prim_c p1 ->
    (match _UU03c3_2 with
     | S_val_prim_c p2 -> s_prim_c_eqb p1 p2
     | _ -> false)
  | S_val_ref_c u1 ->
    (match _UU03c3_2 with
     | S_val_ref_c u2 -> s_ref_c_eqb u1 u2
     | _ -> false)
  | S_val_add (_UU03c3_11, _UU03c3_12) ->
    (match _UU03c3_2 with
     | S_val_add (_UU03c3_21, _UU03c3_22) ->
       (&&) (s_val_eqb _UU03c3_11 _UU03c3_21)
         (s_val_eqb _UU03c3_12 _UU03c3_22)
     | _ -> false)
  | S_val_lt (_UU03c3_11, _UU03c3_12) ->
    (match _UU03c3_2 with
     | S_val_lt (_UU03c3_21, _UU03c3_22) ->
       (&&) (s_val_eqb _UU03c3_11 _UU03c3_21)
         (s_val_eqb _UU03c3_12 _UU03c3_22)
     | _ -> false)
  | S_val_eq (_UU03c3_11, _UU03c3_12) ->
    (match _UU03c3_2 with
     | S_val_eq (_UU03c3_21, _UU03c3_22) ->
       (&&) (s_val_eqb _UU03c3_11 _UU03c3_21)
         (s_val_eqb _UU03c3_12 _UU03c3_22)
     | _ -> false)
  | S_val_subtype (_UU03c3_11, t1) ->
    (match _UU03c3_2 with
     | S_val_subtype (_UU03c3_21, t2) ->
       (&&) (s_val_eqb _UU03c3_11 _UU03c3_21) (s_ty_eqb t1 t2)
     | _ -> false)
  | S_val_field (s11, f1, s12) ->
    (match _UU03c3_2 with
     | S_val_field (s21, f2, s22) ->
       (&&) (s_symb_eqb s11 s21) ((&&) ((=) f1 f2) (s_symb_eqb s12 s22))
     | _ -> false)
  | S_val_ite (_UU03c3_11, _UU03c3_12, _UU03c3_13) ->
    (match _UU03c3_2 with
     | S_val_ite (_UU03c3_21, _UU03c3_22, _UU03c3_23) ->
       (&&) (s_val_eqb _UU03c3_11 _UU03c3_21)
         ((&&) (s_val_eqb _UU03c3_12 _UU03c3_22)
           (s_val_eqb _UU03c3_13 _UU03c3_23))
     | _ -> false)

(** val is_type_primitive : s_ty -> bool **)

let is_type_primitive = function
| S_ty_class _ -> false
| _ -> true

(** val ini : s_ty -> s_val **)

let ini = function
| S_ty_bool -> S_val_prim_c (S_prim_c_bool S_bool_false)
| S_ty_int -> S_val_prim_c (S_prim_c_int O)
| S_ty_class _ -> S_val_ref_c S_ref_c_null

(** val repl_var : s_expr -> string -> s_expr -> s_expr **)

let rec repl_var e x0 e' =
  match e with
  | S_expr_var x' -> if (=) x0 x' then e' else S_expr_var x'
  | S_expr_getfield (e1, f) -> S_expr_getfield ((repl_var e1 x0 e'), f)
  | S_expr_putfield (e1, f, e2) ->
    S_expr_putfield ((repl_var e1 x0 e'), f, (repl_var e2 x0 e'))
  | S_expr_let (x', e1, e2) ->
    if (=) x0 x'
    then S_expr_let (x', e1, e2)
    else S_expr_let (x', (repl_var e1 x0 e'), (repl_var e2 x0 e'))
  | S_expr_add (e1, e2) ->
    S_expr_add ((repl_var e1 x0 e'), (repl_var e2 x0 e'))
  | S_expr_lt (e1, e2) -> S_expr_lt ((repl_var e1 x0 e'), (repl_var e2 x0 e'))
  | S_expr_eq (e1, e2) -> S_expr_eq ((repl_var e1 x0 e'), (repl_var e2 x0 e'))
  | S_expr_instanceof (e1, c0) -> S_expr_instanceof ((repl_var e1 x0 e'), c0)
  | S_expr_if (e1, e2, e3) ->
    S_expr_if ((repl_var e1 x0 e'), (repl_var e2 x0 e'), (repl_var e3 x0 e'))
  | S_expr_invoke (e1, m, e2) ->
    S_expr_invoke ((repl_var e1 x0 e'), m, (repl_var e2 x0 e'))
  | x1 -> x1

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Cons of 'a * 'a stream

(** val hd0 : 'a1 stream -> 'a1 **)

let hd0 x0 =
  let Cons (a, _) = Lazy.force x0 in a

(** val tl : 'a1 stream -> 'a1 stream **)

let tl x0 =
  let Cons (_, s) = Lazy.force x0 in s

(** val str_nth_tl : nat -> 'a1 stream -> 'a1 stream **)

let rec str_nth_tl n1 s =
  match n1 with
  | O -> s
  | S m -> str_nth_tl m (tl s)

(** val str_nth : nat -> 'a1 stream -> 'a1 **)

let str_nth n1 s =
  hd0 (str_nth_tl n1 s)

module type Coq_DecidableType =
 DecidableTypeOrig

module KeyDecidableType =
 functor (D:Coq_DecidableType) ->
 struct
 end

module Raw =
 functor (X:Coq_DecidableType) ->
 struct
  module PX = KeyDecidableType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p0 :: l0 -> let (k', _) = p0 in if X.eq_dec k k' then true else mem k l0

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l0) -> f0 s k' _x l0 __ __ __
  | R_mem_2 (s, k', _x, l0, _res, r0) ->
    f1 s k' _x l0 __ __ __ _res r0 (coq_R_mem_rect k f f0 f1 l0 _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l0) -> f0 s k' _x l0 __ __ __
  | R_mem_2 (s, k', _x, l0, _res, r0) ->
    f1 s k' _x l0 __ __ __ _res r0 (coq_R_mem_rec k f f0 f1 l0 _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f f0 f1 s =
    let f2 = f s in
    let f3 = f0 s in
    let f4 = f1 s in
    (match s with
     | [] -> f2 __
     | a :: l0 ->
       let (a0, b0) = a in
       let f5 = f4 a0 b0 l0 __ in
       let f6 = fun _ _ -> let hrec = mem_rect k f f0 f1 l0 in f5 __ __ hrec
       in
       let f7 = f3 a0 b0 l0 __ in if X.eq_dec k a0 then f7 __ __ else f6 __ __)

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y0 _ _ _ -> R_mem_0 y0)
      (fun y0 y1 y2 y3 _ _ _ _ _ -> R_mem_1 (y0, y1, y2, y3))
      (fun y0 y1 y2 y3 _ _ _ y6 _ _ -> R_mem_2 (y0, y1, y2, y3, (mem k y3),
      (y6 (mem k y3) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p0 :: s' ->
    let (k', x0) = p0 in if X.eq_dec k k' then Some x0 else find k s'

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x0, s') -> f0 s k' x0 s' __ __ __
  | R_find_2 (s, k', x0, s', _res, r0) ->
    f1 s k' x0 s' __ __ __ _res r0 (coq_R_find_rect k f f0 f1 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x0, s') -> f0 s k' x0 s' __ __ __
  | R_find_2 (s, k', x0, s', _res, r0) ->
    f1 s k' x0 s' __ __ __ _res r0 (coq_R_find_rec k f f0 f1 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f f0 f1 s =
    let f2 = f s in
    let f3 = f0 s in
    let f4 = f1 s in
    (match s with
     | [] -> f2 __
     | a :: l0 ->
       let (a0, b0) = a in
       let f5 = f4 a0 b0 l0 __ in
       let f6 = fun _ _ -> let hrec = find_rect k f f0 f1 l0 in f5 __ __ hrec
       in
       let f7 = f3 a0 b0 l0 __ in if X.eq_dec k a0 then f7 __ __ else f6 __ __)

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y0 _ _ _ -> R_find_0 y0)
      (fun y0 y1 y2 y3 _ _ _ _ _ -> R_find_1 (y0, y1, y2, y3))
      (fun y0 y1 y2 y3 _ _ _ y6 _ _ -> R_find_2 (y0, y1, y2, y3, (find k y3),
      (y6 (find k y3) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x0 = function
  | [] -> (k, x0) :: []
  | p0 :: l0 ->
    let (k', y0) = p0 in
    if X.eq_dec k k' then (k, x0) :: l0 else (k', y0) :: (add k x0 l0)

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x0 f f0 f1 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y0, l0) -> f0 s k' y0 l0 __ __ __
  | R_add_2 (s, k', y0, l0, _res, r0) ->
    f1 s k' y0 l0 __ __ __ _res r0 (coq_R_add_rect k x0 f f0 f1 l0 _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x0 f f0 f1 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y0, l0) -> f0 s k' y0 l0 __ __ __
  | R_add_2 (s, k', y0, l0, _res, r0) ->
    f1 s k' y0 l0 __ __ __ _res r0 (coq_R_add_rec k x0 f f0 f1 l0 _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x0 f f0 f1 s =
    let f2 = f s in
    let f3 = f0 s in
    let f4 = f1 s in
    (match s with
     | [] -> f2 __
     | a :: l0 ->
       let (a0, b0) = a in
       let f5 = f4 a0 b0 l0 __ in
       let f6 = fun _ _ ->
         let hrec = add_rect k x0 f f0 f1 l0 in f5 __ __ hrec
       in
       let f7 = f3 a0 b0 l0 __ in if X.eq_dec k a0 then f7 __ __ else f6 __ __)

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x0 s _res =
    add_rect k x0 (fun y0 _ _ _ -> R_add_0 y0) (fun y0 y1 y2 y3 _ _ _ _ _ ->
      R_add_1 (y0, y1, y2, y3)) (fun y0 y1 y2 y3 _ _ _ y6 _ _ -> R_add_2 (y0,
      y1, y2, y3, (add k x0 y3), (y6 (add k x0 y3) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k = function
  | [] -> []
  | p0 :: l0 ->
    let (k', x0) = p0 in
    if X.eq_dec k k' then l0 else (k', x0) :: (remove k l0)

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x0, l0) -> f0 s k' x0 l0 __ __ __
  | R_remove_2 (s, k', x0, l0, _res, r0) ->
    f1 s k' x0 l0 __ __ __ _res r0 (coq_R_remove_rect k f f0 f1 l0 _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x0, l0) -> f0 s k' x0 l0 __ __ __
  | R_remove_2 (s, k', x0, l0, _res, r0) ->
    f1 s k' x0 l0 __ __ __ _res r0 (coq_R_remove_rec k f f0 f1 l0 _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f f0 f1 s =
    let f2 = f s in
    let f3 = f0 s in
    let f4 = f1 s in
    (match s with
     | [] -> f2 __
     | a :: l0 ->
       let (a0, b0) = a in
       let f5 = f4 a0 b0 l0 __ in
       let f6 = fun _ _ ->
         let hrec = remove_rect k f f0 f1 l0 in f5 __ __ hrec
       in
       let f7 = f3 a0 b0 l0 __ in if X.eq_dec k a0 then f7 __ __ else f6 __ __)

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y0 _ _ _ -> R_remove_0 y0)
      (fun y0 y1 y2 y3 _ _ _ _ _ -> R_remove_1 (y0, y1, y2, y3))
      (fun y0 y1 y2 y3 _ _ _ y6 _ _ -> R_remove_2 (y0, y1, y2, y3,
      (remove k y3), (y6 (remove k y3) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p0 :: m' -> let (k, e) = p0 in fold f m' (f k e acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0
      (coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0 (coq_R_fold_rec f f0 f1 m' (f k e acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let rec fold_rect f f0 f1 m acc =
    let f2 = f0 m acc in
    let f3 = f1 m acc in
    (match m with
     | [] -> f2 __
     | a :: l0 ->
       let (a0, b0) = a in
       let f4 = f3 a0 b0 l0 __ in
       let hrec = fold_rect f f0 f1 l0 (f a0 b0 acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y0 y1 _ _ _ -> R_fold_0 (y0, y1))
      (fun y0 y1 y2 y3 y4 _ y5 _ _ -> R_fold_1 (y0, y1, y2, y3, y4,
      (fold f y4 (f y2 y3 y1)), (y5 (fold f y4 (f y2 y3 y1)) __))) m acc _res
      __

  (** val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool **)

  let check cmp k e m' =
    match find k m' with
    | Some e' -> cmp e e'
    | None -> false

  (** val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let submap cmp m m' =
    fold (fun k e b0 -> (&&) (check cmp k e m') b0) m true

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    (&&) (submap cmp m m') (submap (fun e' e -> cmp e e') m' m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p0 :: m' -> let (k, e) = p0 in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p0 :: m' -> let (k, e) = p0 in (k, (f k e)) :: (mapi f m')

  (** val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let combine_l m m' =
    mapi (fun k e -> ((Some e), (find k m'))) m

  (** val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let combine_r m m' =
    mapi (fun k e' -> ((find k m), (Some e'))) m'

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3 **)

  let fold_right_pair f =
    fold_right (fun p0 -> f (fst p0) (snd p0))

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let combine m m' =
    let l0 = combine_l m m' in
    let r = combine_r m m' in fold_right_pair add r l0

  (** val at_least_left :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_left o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> None

  (** val at_least_right :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_right o o' = match o' with
  | Some _ -> Some (o, o')
  | None -> None

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l0 =
    match o with
    | Some e -> (k, e) :: l0
    | None -> l0

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2 f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p0 -> f (fst p0) (snd p0)) m0 in
    fold_right_pair option_cons [] m1

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module Make =
 functor (X:Coq_DecidableType) ->
 struct
  module Raw = Raw(X)

  module E = X

  type key = E.t

  type 'elt slist =
    'elt Raw.t
    (* singleton inductive, whose constructor was Build_slist *)

  (** val this : 'a1 slist -> 'a1 Raw.t **)

  let this s =
    s

  type 'elt t = 'elt slist

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x0 e m =
    Raw.add x0 e (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x0 m =
    Raw.find x0 (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x0 m =
    Raw.remove x0 (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x0 m =
    Raw.mem x0 (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> nat **)

  let cardinal m =
    length (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module MakeRaw =
 functor (X:DecidableType) ->
 struct
  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    []

  (** val is_empty : t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : elt -> t -> bool **)

  let rec mem x0 = function
  | [] -> false
  | y0 :: l0 -> if X.eq_dec x0 y0 then true else mem x0 l0

  (** val add : elt -> t -> t **)

  let rec add x0 s = match s with
  | [] -> x0 :: []
  | y0 :: l0 -> if X.eq_dec x0 y0 then s else y0 :: (add x0 l0)

  (** val singleton : elt -> t **)

  let singleton x0 =
    x0 :: []

  (** val remove : elt -> t -> t **)

  let rec remove x0 = function
  | [] -> []
  | y0 :: l0 -> if X.eq_dec x0 y0 then l0 else y0 :: (remove x0 l0)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f =
    fold_left (flip f)

  (** val union : t -> t -> t **)

  let union s =
    fold add s

  (** val diff : t -> t -> t **)

  let diff s s' =
    fold remove s' s

  (** val inter : t -> t -> t **)

  let inter s s' =
    fold (fun x0 s0 -> if mem x0 s' then add x0 s0 else s0) s []

  (** val subset : t -> t -> bool **)

  let subset s s' =
    is_empty (diff s s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    (&&) (subset s s') (subset s' s)

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f = function
  | [] -> []
  | x0 :: l0 -> if f x0 then x0 :: (filter f l0) else filter f l0

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f = function
  | [] -> true
  | x0 :: l0 -> if f x0 then for_all f l0 else false

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f = function
  | [] -> false
  | x0 :: l0 -> if f x0 then true else exists_ f l0

  (** val partition : (elt -> bool) -> t -> t * t **)

  let rec partition f = function
  | [] -> ([], [])
  | x0 :: l0 ->
    let (s1, s2) = partition f l0 in
    if f x0 then ((x0 :: s1), s2) else (s1, (x0 :: s2))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements s =
    s

  (** val choose : t -> elt option **)

  let choose = function
  | [] -> None
  | x0 :: _ -> Some x0

  (** val isok : elt list -> bool **)

  let rec isok = function
  | [] -> true
  | a :: l1 -> (&&) (negb (mem a l1)) (isok l1)
 end

module Coq_Make =
 functor (X:DecidableType) ->
 struct
  module Raw = MakeRaw(X)

  module E =
   struct
    type t = X.t

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t1 =
    t1

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x0 s =
    Raw.mem x0 (this s)

  (** val add : elt -> t -> t **)

  let add x0 s =
    Raw.add x0 (this s)

  (** val remove : elt -> t -> t **)

  let remove x0 s =
    Raw.remove x0 (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p0 = Raw.partition f (this s) in ((fst p0), (snd p0))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b0 = Raw.equal s0 s'0 in if b0 then true else false
 end

module type UsualDecidableType =
 UsualDecidableTypeOrig

module UDT_to_DT =
 functor (U:UsualDecidableType) ->
 U

module type Coq_MiniDecidableType =
 MiniDecidableType

module Coq_Make_UDT =
 functor (M:Coq_MiniDecidableType) ->
 Make_UDT(M)

module String_as_MDT =
 struct
  type t = string

  (** val eq_dec : string -> string -> bool **)

  let eq_dec =
    (=)
 end

module String_as_UDT = Coq_Make_UDT(String_as_MDT)

module String_as_DT = UDT_to_DT(String_as_UDT)

module ListString_as_MDT =
 struct
  (** val eq_dec : string list -> string list -> bool **)

  let rec eq_dec l0 l2 =
    match l0 with
    | [] -> (match l2 with
             | [] -> true
             | _ :: _ -> false)
    | y0 :: l1 ->
      (match l2 with
       | [] -> false
       | a :: l3 -> let h = (=) y0 a in if h then eq_dec l1 l3 else false)
 end

module SSymb_as_MDT =
 struct
  (** val eq_dec : s_symb -> s_symb -> bool **)

  let eq_dec s1 s2 =
    match s1 with
    | S_symb_expr n1 ->
      (match s2 with
       | S_symb_expr n2 -> Nat.eq_dec n1 n2
       | S_symb_fld (_, _) -> false)
    | S_symb_fld (n1, l0) ->
      (match s2 with
       | S_symb_expr _ -> false
       | S_symb_fld (n2, l1) ->
         let h = Nat.eq_dec n1 n2 in
         let h1 = ListString_as_MDT.eq_dec l0 l1 in if h1 then h else false)
 end

module RefC_as_MDT =
 struct
  type t = s_ref_c

  (** val eq_dec : s_ref_c -> s_ref_c -> bool **)

  let eq_dec x0 y0 =
    match x0 with
    | S_ref_c_null -> (match y0 with
                       | S_ref_c_null -> true
                       | _ -> false)
    | S_ref_c_loc s ->
      (match y0 with
       | S_ref_c_loc s0 -> Nat.eq_dec s s0
       | _ -> false)
    | S_ref_c_symb s ->
      (match y0 with
       | S_ref_c_symb s0 ->
         (match s with
          | S_symb_expr n1 ->
            (match s0 with
             | S_symb_expr n2 -> Nat.eq_dec n1 n2
             | S_symb_fld (_, _) -> false)
          | S_symb_fld (n1, l0) ->
            SSymb_as_MDT.eq_dec (S_symb_fld (n1, l0)) s0)
       | _ -> false)
 end

module RefC_as_UDT = Coq_Make_UDT(RefC_as_MDT)

module RefC_as_DT = UDT_to_DT(RefC_as_UDT)

module MapString = Make(String_as_DT)

module MapRefC = Make(RefC_as_DT)

module SSymb_as_DT =
 struct
  type t = s_symb

  (** val eq_dec : s_symb -> s_symb -> bool **)

  let eq_dec s1 s2 =
    match s1 with
    | S_symb_expr n1 ->
      (match s2 with
       | S_symb_expr n2 -> Nat.eq_dec n1 n2
       | S_symb_fld (_, _) -> false)
    | S_symb_fld (n1, l0) ->
      (match s2 with
       | S_symb_expr _ -> false
       | S_symb_fld (n2, l1) ->
         let h = Nat.eq_dec n1 n2 in
         let h1 = ListString_as_MDT.eq_dec l0 l1 in if h1 then h else false)
 end

module SetSymb = Coq_Make(SSymb_as_DT)

type dstring = string list

(** val from_string : string -> dstring **)

let from_string s =
  s :: []

(** val add_last : dstring -> string -> dstring **)

let rec add_last f s =
  match f with
  | [] -> s :: []
  | s' :: f' ->
    (match f' with
     | [] -> ((^) s' s) :: []
     | _ :: _ -> s' :: (add_last f' s))

(** val append : dstring -> dstring -> dstring **)

let append f g = match g with
| [] -> f
| s :: g' ->
  (match f with
   | [] -> g
   | _ :: f' ->
     if Nat.ltb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))
          (add (length0 s) (length0 (last f' "")))
     then app f g
     else app (add_last f s) g')

(** val dconcat : dstring -> dstring list -> dstring **)

let rec dconcat s = function
| [] -> from_string ""
| f :: l' ->
  (match l' with
   | [] -> f
   | _ :: _ -> append (append f s) (dconcat s l'))

type object_memory = s_val MapString.t

type object0 = object_memory * string

type heap = object0 MapRefC.t

type clause =
| Clause_pos of s_val
| Clause_neg of s_val

type path_condition = clause list

type config = ((s_prg * heap) * path_condition) * s_expr

(** val h0 : heap **)

let h0 =
  MapRefC.empty

(** val _UU03a3_0 : path_condition **)

let _UU03a3_0 =
  []

(** val config_initial : s_prg -> config **)

let config_initial p0 =
  let e0 = expression p0 in (((p0, h0), _UU03a3_0), e0)

(** val o_memory : object0 -> object_memory **)

let o_memory = function
| (m, _) -> m

(** val o_class_name : object0 -> string **)

let o_class_name = function
| (_, c0) -> c0

(** val get : object0 -> string -> s_val option **)

let get o f =
  MapString.find f (o_memory o)

(** val obj_at : heap -> s_ref_c -> object0 option **)

let obj_at h u =
  MapRefC.find u h

(** val obj_class_at : heap -> s_ref_c -> string option **)

let obj_class_at h u =
  match obj_at h u with
  | Some o -> Some (o_class_name o)
  | None -> None

(** val unresolved_c : heap -> s_symb -> bool **)

let unresolved_c h s =
  negb (MapRefC.mem (S_ref_c_symb s) h)

(** val object_eqb : object0 -> object0 -> bool **)

let object_eqb o1 o2 =
  (&&) ((=) (o_class_name o1) (o_class_name o2))
    (MapString.equal s_val_eqb (o_memory o1) (o_memory o2))

(** val superclass_immediate : s_prg -> string -> string option **)

let superclass_immediate =
  let superclass_immediate_aux =
    let rec superclass_immediate_aux c_sub = function
    | [] -> None
    | c0 :: other_Cs ->
      let S_dc_c_l (c1, c_sup, _, _) = c0 in
      if (=) c_sub c1
      then Some c_sup
      else superclass_immediate_aux c_sub other_Cs
    in superclass_immediate_aux
  in
  (fun p0 c_sub -> superclass_immediate_aux c_sub (classes p0))

(** val subclass_c : s_prg -> string -> string -> bool **)

let subclass_c =
  let subclass_c_aux =
    let rec subclass_c_aux p0 c_possible_sub c_possible_sup cs n1 =
      if (=) c_possible_sub c_possible_sup
      then true
      else (match n1 with
            | O -> false
            | S n' ->
              (match superclass_immediate p0 c_possible_sub with
               | Some c_sup_immediate ->
                 subclass_c_aux p0 c_sup_immediate c_possible_sup cs n'
               | None -> false))
    in subclass_c_aux
  in
  (fun p0 c_possible_sub c_possible_sup ->
  subclass_c_aux p0 c_possible_sub c_possible_sup (classes p0)
    (length (classes p0)))

(** val class_has_field_c : s_dc_c -> string -> bool **)

let class_has_field_c c0 f =
  existsb (fun f0 -> (=) (field_name f0) f) (fields c0)

(** val class_has_method_c : s_dc_c -> string -> bool **)

let class_has_method_c c0 m =
  existsb (fun d0 -> (=) (method_name d0) m) (methods c0)

(** val has_method_c : s_prg -> string -> string -> bool **)

let has_method_c =
  let has_method_c_aux =
    let rec has_method_c_aux cs c0 m =
      match cs with
      | [] -> false
      | c1 :: other_Cs ->
        (||) ((&&) ((=) (class_name c1) c0) (class_has_method_c c1 m))
          (has_method_c_aux other_Cs c0 m)
    in has_method_c_aux
  in
  (fun p0 c0 m -> has_method_c_aux (classes p0) c0 m)

(** val mdecl : s_prg -> string -> string -> s_dc_m option **)

let mdecl =
  let mdecl_list_dc_m =
    let rec mdecl_list_dc_m ds m =
      match ds with
      | [] -> None
      | d0 :: other_Ds ->
        if (=) (method_name d0) m then Some d0 else mdecl_list_dc_m other_Ds m
    in mdecl_list_dc_m
  in
  let mdecl_list_dc_c =
    let rec mdecl_list_dc_c cs c0 m =
      match cs with
      | [] -> None
      | c1 :: other_Cs ->
        if (=) (class_name c1) c0
        then mdecl_list_dc_m (methods c1) m
        else mdecl_list_dc_c other_Cs c0 m
    in mdecl_list_dc_c
  in
  (fun p0 c0 m -> mdecl_list_dc_c (classes p0) c0 m)

(** val cdecl : s_prg -> string -> s_dc_c option **)

let cdecl =
  let cdecl_list_dc_c =
    let rec cdecl_list_dc_c cs c0 =
      match cs with
      | [] -> None
      | c1 :: other_Cs ->
        if (=) (class_name c1) c0
        then Some c1
        else cdecl_list_dc_c other_Cs c0
    in cdecl_list_dc_c
  in
  (fun p0 c0 -> cdecl_list_dc_c (classes p0) c0)

(** val fdecl : s_dc_c -> string -> s_dc_v option **)

let fdecl =
  let fdecl_aux =
    let rec fdecl_aux fs f =
      match fs with
      | [] -> None
      | s :: other_Fs ->
        let S_dc_v_l (t1, f') = s in
        if (=) f f' then Some (S_dc_v_l (t1, f')) else fdecl_aux other_Fs f
    in fdecl_aux
  in
  (fun c0 fname -> fdecl_aux (fields c0) fname)

(** val sees_method_c : s_prg -> string -> string -> string -> bool **)

let sees_method_c p0 m c_possible_sub c_possible_sup =
  (&&)
    ((&&) (subclass_c p0 c_possible_sub c_possible_sup)
      (has_method_c p0 c_possible_sup m))
    (forallb (fun c0 ->
      (||)
        ((||)
          ((||)
            ((||) ((=) (class_name c0) c_possible_sub)
              ((=) (class_name c0) c_possible_sup))
            (negb (subclass_c p0 (class_name c0) c_possible_sup)))
          (negb (subclass_c p0 c_possible_sub (class_name c0))))
        (negb (has_method_c p0 (class_name c0) m))) (classes p0))

(** val recv_method_c : s_prg -> string -> string -> string -> bool **)

let recv_method_c p0 m c_possible_sub c_possible_sup =
  (||)
    ((&&)
      ((&&) (negb ((=) c_possible_sub c_possible_sup))
        (sees_method_c p0 m c_possible_sub c_possible_sup))
      (negb (has_method_c p0 c_possible_sub m)))
    ((&&) ((=) c_possible_sub c_possible_sup)
      (has_method_c p0 c_possible_sub m))

(** val method_provider : s_prg -> string -> string -> string option **)

let method_provider p0 m c0 =
  option_map class_name
    (find (fun c' -> recv_method_c p0 m c0 (class_name c')) (classes p0))

(** val class_with_field : s_prg -> string -> s_dc_c option **)

let class_with_field =
  let class_with_field_aux =
    let rec class_with_field_aux cs f =
      match cs with
      | [] -> None
      | c0 :: other_Cs ->
        if class_has_field_c c0 f
        then Some c0
        else class_with_field_aux other_Cs f
    in class_with_field_aux
  in
  (fun p0 f -> class_with_field_aux (classes p0) f)

(** val implementors : s_prg -> string -> string list **)

let implementors p0 m =
  map class_name (filter (fun c0 -> class_has_method_c c0 m) (classes p0))

(** val overriders : s_prg -> string -> string -> string list **)

let overriders p0 m c' =
  map class_name
    (filter (fun c0 ->
      (&&)
        ((&&) (sees_method_c p0 m (class_name c0) c')
          (class_has_method_c c0 m)) (negb ((=) (class_name c0) c')))
      (classes p0))

(** val new_obj_c : s_prg -> string -> object0 **)

let new_obj_c =
  let add_fields =
    let rec add_fields m fs symbolic =
      match fs with
      | [] -> m
      | f :: other_Fs ->
        let m' = add_fields m other_Fs symbolic in
        MapString.add (field_name f)
          (if symbolic then S_val_unassumed else ini (field_type f)) m'
    in add_fields
  in
  let new_obj_memory =
    let rec new_obj_memory p0 c0 cs symbolic =
      match cs with
      | [] -> MapString.empty
      | c1 :: other_Cs ->
        let m' = new_obj_memory p0 c0 other_Cs symbolic in
        if subclass_c p0 c0 (class_name c1)
        then add_fields m' (fields c1) symbolic
        else m'
    in new_obj_memory
  in
  (fun p0 c0 -> ((new_obj_memory p0 c0 (classes p0) false), c0))

(** val new_obj_symb_c : s_prg -> string -> object0 **)

let new_obj_symb_c =
  let add_fields =
    let rec add_fields m fs symbolic =
      match fs with
      | [] -> m
      | f :: other_Fs ->
        let m' = add_fields m other_Fs symbolic in
        MapString.add (field_name f)
          (if symbolic then S_val_unassumed else ini (field_type f)) m'
    in add_fields
  in
  let new_obj_memory =
    let rec new_obj_memory p0 c0 cs symbolic =
      match cs with
      | [] -> MapString.empty
      | c1 :: other_Cs ->
        let m' = new_obj_memory p0 c0 other_Cs symbolic in
        if subclass_c p0 c0 (class_name c1)
        then add_fields m' (fields c1) symbolic
        else m'
    in new_obj_memory
  in
  (fun p0 c0 -> ((new_obj_memory p0 c0 (classes p0) true), c0))

(** val refine_obj_symb_c : s_prg -> string -> object0 -> object0 **)

let refine_obj_symb_c =
  let add_fields =
    let rec add_fields m fs symbolic =
      match fs with
      | [] -> m
      | f :: other_Fs ->
        let m' = add_fields m other_Fs symbolic in
        MapString.add (field_name f)
          (if symbolic then S_val_unassumed else ini (field_type f)) m'
    in add_fields
  in
  let refine_obj_symb_memory =
    let rec refine_obj_symb_memory p0 c0 c_sub m = function
    | [] -> m
    | c1 :: other_Cs ->
      let m' = refine_obj_symb_memory p0 c0 c_sub m other_Cs in
      if (&&)
           ((&&) (subclass_c p0 (class_name c1) c0)
             (subclass_c p0 c_sub (class_name c1)))
           (negb ((=) (class_name c1) c0))
      then add_fields m' (fields c1) true
      else m'
    in refine_obj_symb_memory
  in
  (fun p0 c_sub o ->
  ((refine_obj_symb_memory p0 (o_class_name o) c_sub (o_memory o)
     (classes p0)), c_sub))

(** val upd_obj : object0 -> string -> s_val -> object0 **)

let upd_obj o f _UU03c3_0 =
  ((MapString.add f _UU03c3_0 (o_memory o)), (o_class_name o))

(** val repl_obj : heap -> s_ref_c -> object0 -> heap **)

let repl_obj h u o =
  match u with
  | S_ref_c_null -> h
  | _ -> MapRefC.add u o h

(** val add_obj : heap -> object0 -> heap * s_ref_c **)

let add_obj h o =
  let next = S_ref_c_loc (MapRefC.cardinal h) in
  ((MapRefC.add next o h), next)

(** val add_obj_symb : heap -> s_symb -> object0 -> heap **)

let add_obj_symb h s o =
  MapRefC.add (S_ref_c_symb s) o h

(** val assume_c : heap -> s_ref_c -> string -> (s_val * s_ref_c) option **)

let assume_c =
  let assume_c_fp =
    let rec assume_c_fp helts s f _UU03c3_Part =
      match helts with
      | [] -> Some _UU03c3_Part
      | p0 :: other_Helts ->
        let (s0, o') = p0 in
        (match s0 with
         | S_ref_c_symb s' ->
           if s_symb_eqb s s'
           then assume_c_fp other_Helts s f _UU03c3_Part
           else (match get o' f with
                 | Some _UU03c3_' ->
                   if s_val_eqb _UU03c3_' S_val_unassumed
                   then assume_c_fp other_Helts s f _UU03c3_Part
                   else assume_c_fp other_Helts s f (S_val_ite ((S_val_eq
                          ((S_val_ref_c (S_ref_c_symb s)), (S_val_ref_c
                          (S_ref_c_symb s')))), _UU03c3_', _UU03c3_Part))
                 | None -> assume_c_fp other_Helts s f _UU03c3_Part)
         | _ -> assume_c_fp other_Helts s f _UU03c3_Part)
    in assume_c_fp
  in
  (fun h y0 f ->
  match y0 with
  | S_ref_c_symb s ->
    if MapRefC.mem y0 h
    then let s' =
           match s with
           | S_symb_expr n1 -> S_symb_fld (n1, (f :: []))
           | S_symb_fld (n1, l0) -> S_symb_fld (n1, (app l0 (f :: [])))
         in
         let z = S_ref_c_symb s' in
         option_map (fun _UU03c3_0 -> (_UU03c3_0, z))
           (assume_c_fp (MapRefC.elements h) s f (S_val_ref_c z))
    else None
  | _ -> None)

(** val assume_num : heap -> s_ref_c -> string -> s_prim_c option **)

let assume_num h y0 f =
  match y0 with
  | S_ref_c_symb s ->
    if MapRefC.mem y0 h
    then let s' =
           match s with
           | S_symb_expr n1 -> S_symb_fld (n1, (f :: []))
           | S_symb_fld (n1, l0) -> S_symb_fld (n1, (app l0 (f :: [])))
         in
         Some (S_prim_c_symb s')
    else None
  | _ -> None

(** val update_c : string -> s_ref_c -> s_val -> heap -> heap **)

let update_c =
  let update_c_fp =
    let rec update_c_fp f y0 _UU03c3_' = function
    | [] -> h0
    | p0 :: other_Helts ->
      let (u', o') = p0 in
      let other_H = update_c_fp f y0 _UU03c3_' other_Helts in
      (match u' with
       | S_ref_c_symb s' ->
         let y' = S_ref_c_symb s' in
         (match get o' f with
          | Some _UU03c3_0 ->
            if (||)
                 ((||) (s_ref_c_eqb y0 y')
                   (s_val_eqb _UU03c3_0 S_val_unassumed))
                 (s_val_eqb _UU03c3_0 _UU03c3_')
            then MapRefC.add u' o' other_H
            else let oRefined' =
                   upd_obj o' f (S_val_ite ((S_val_eq ((S_val_ref_c y0),
                     (S_val_ref_c y'))), _UU03c3_', _UU03c3_0))
                 in
                 MapRefC.add u' oRefined' other_H
          | None -> MapRefC.add u' o' other_H)
       | _ -> MapRefC.add u' o' other_H)
    in update_c_fp
  in
  (fun f y0 _UU03c3_0 h -> update_c_fp f y0 _UU03c3_0 (MapRefC.elements h))

(** val merge_c_aux :
    (s_ref_c * object0) list -> heap -> string -> s_val -> bool -> heap option **)

let rec merge_c_aux h1elts h2 f _UU03c3_0 direct =
  match h1elts with
  | [] -> Some h0
  | p0 :: other_H1elts ->
    let (u, o1) = p0 in
    let other_H1 = merge_c_aux other_H1elts h2 f _UU03c3_0 direct in
    (match obj_at h2 u with
     | Some o2 ->
       if (&&) direct (object_eqb o1 o2)
       then option_map (fun h' -> repl_obj h' u o1) other_H1
       else if (&&) direct (negb (object_eqb o1 o2))
            then (match get o1 f with
                  | Some _UU03c3_1 ->
                    (match get o2 f with
                     | Some _UU03c3_2 ->
                       if object_eqb o1 (upd_obj o2 f _UU03c3_1)
                       then let o' =
                              upd_obj o1 f (S_val_ite (_UU03c3_0, _UU03c3_1,
                                _UU03c3_2))
                            in
                            option_map (fun h' -> repl_obj h' u o') other_H1
                       else None
                     | None -> None)
                  | None -> None)
            else other_H1
     | None ->
       (match get o1 f with
        | Some _UU03c3_1 ->
          (match u with
           | S_ref_c_symb s ->
             let s' =
               match s with
               | S_symb_expr n1 -> S_symb_fld (n1, (f :: []))
               | S_symb_fld (n1, l0) -> S_symb_fld (n1, (app l0 (f :: [])))
             in
             let z = S_val_ref_c (S_ref_c_symb s') in
             let o' =
               if direct
               then upd_obj o1 f (S_val_ite (_UU03c3_0, _UU03c3_1, z))
               else upd_obj o1 f (S_val_ite (_UU03c3_0, z, _UU03c3_1))
             in
             option_map (fun h' -> repl_obj h' u o') other_H1
           | _ -> None)
        | None -> None))

(** val merge_c : heap -> heap -> string -> s_val -> heap option **)

let merge_c h1' h2' f _UU03c3_0 =
  match merge_c_aux (MapRefC.elements h1') h2' f _UU03c3_0 true with
  | Some h1'' ->
    (match merge_c_aux (MapRefC.elements h2') h1' f _UU03c3_0 false with
     | Some h2'' ->
       Some
         (MapRefC.map2 (fun x0 y0 ->
           match x0 with
           | Some o -> (match y0 with
                        | Some _ -> None
                        | None -> Some o)
           | None -> y0) h1'' h2'')
     | None -> None)
  | None -> None

(** val merge_clauses : heap -> heap -> string -> path_condition option **)

let merge_clauses =
  let merge_clauses_aux =
    let rec merge_clauses_aux h1elts h2 f =
      match h1elts with
      | [] -> Some []
      | p0 :: other_H1elts ->
        let (u, _) = p0 in
        let other_H1 = merge_clauses_aux other_H1elts h2 f in
        (match obj_at h2 u with
         | Some _ -> other_H1
         | None ->
           (match u with
            | S_ref_c_symb s ->
              let s' =
                match s with
                | S_symb_expr n1 -> S_symb_fld (n1, (f :: []))
                | S_symb_fld (n1, l0) -> S_symb_fld (n1, (app l0 (f :: [])))
              in
              option_map (fun _UU03a3_ -> (Clause_pos (S_val_field (s, f,
                s'))) :: _UU03a3_) other_H1
            | _ -> None))
    in merge_clauses_aux
  in
  (fun h1' h2' f ->
  match merge_clauses_aux (MapRefC.elements h1') h2' f with
  | Some _UU03a3_1 ->
    (match merge_clauses_aux (MapRefC.elements h2') h1' f with
     | Some _UU03a3_2 -> Some (app _UU03a3_1 _UU03a3_2)
     | None -> None)
  | None -> None)

type computation = config list stream

(** val rstep_c :
    s_prg -> heap -> path_condition -> s_expr -> (heap * path_condition)
    option **)

let rec rstep_c p0 h _UU03a3_ = function
| S_expr_getfield (e1, f) ->
  (match e1 with
   | S_expr_val s0 ->
     (match s0 with
      | S_val_ref_c s1 ->
        (match s1 with
         | S_ref_c_symb s ->
           let y0 = S_ref_c_symb s in
           if unresolved_c h s
           then (match class_with_field p0 f with
                 | Some c0 ->
                   let c1 = class_name c0 in
                   let o = new_obj_symb_c p0 c1 in
                   let h' = add_obj_symb h s o in
                   let cl1 = Clause_neg (S_val_eq ((S_val_ref_c y0),
                     (S_val_ref_c S_ref_c_null)))
                   in
                   let cl2 = Clause_pos (S_val_subtype ((S_val_ref_c y0),
                     (S_ty_class c1)))
                   in
                   let _UU03a3_' = app _UU03a3_ (cl1 :: (cl2 :: [])) in
                   Some (h', _UU03a3_')
                 | None -> None)
           else (match obj_at h y0 with
                 | Some o ->
                   (match get o f with
                    | Some s2 ->
                      (match s2 with
                       | S_val_unassumed ->
                         (match class_with_field p0 f with
                          | Some c' ->
                            (match fdecl c' f with
                             | Some f0 ->
                               let t1 = field_type f0 in
                               if is_type_primitive t1
                               then (match assume_num h y0 f with
                                     | Some s3 ->
                                       (match s3 with
                                        | S_prim_c_symb s' ->
                                          let _UU03c3_0 = S_val_prim_c
                                            (S_prim_c_symb s')
                                          in
                                          let o' = upd_obj o f _UU03c3_0 in
                                          let h' = repl_obj h y0 o' in
                                          let cl = Clause_pos (S_val_field
                                            (s, f, s'))
                                          in
                                          let _UU03a3_' =
                                            app _UU03a3_ (cl :: [])
                                          in
                                          Some (h', _UU03a3_')
                                        | _ -> None)
                                     | None -> None)
                               else (match assume_c h y0 f with
                                     | Some p1 ->
                                       let (_UU03c3_0, s3) = p1 in
                                       (match s3 with
                                        | S_ref_c_symb s' ->
                                          let o' = upd_obj o f _UU03c3_0 in
                                          let h' = repl_obj h y0 o' in
                                          let cl = Clause_pos (S_val_field
                                            (s, f, s'))
                                          in
                                          let _UU03a3_' =
                                            app _UU03a3_ (cl :: [])
                                          in
                                          Some (h', _UU03a3_')
                                        | _ -> None)
                                     | None -> None)
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | None ->
                      (match class_with_field p0 f with
                       | Some c' ->
                         let c'0 = class_name c' in
                         let o' = refine_obj_symb_c p0 c'0 o in
                         let h' = repl_obj h y0 o' in
                         let cl = Clause_pos (S_val_subtype ((S_val_ref_c
                           y0), (S_ty_class c'0)))
                         in
                         let _UU03a3_' = app _UU03a3_ (cl :: []) in
                         Some (h', _UU03a3_')
                       | None -> None))
                 | None -> None)
         | _ -> rstep_c p0 h _UU03a3_ e1)
      | _ -> rstep_c p0 h _UU03a3_ e1)
   | _ -> rstep_c p0 h _UU03a3_ e1)
| S_expr_putfield (e1, f, e2) ->
  (match e1 with
   | S_expr_val s0 ->
     (match s0 with
      | S_val_ref_c s1 ->
        (match s1 with
         | S_ref_c_symb s ->
           (match e2 with
            | S_expr_val _ ->
              let y0 = S_ref_c_symb s in
              if unresolved_c h s
              then (match class_with_field p0 f with
                    | Some c0 ->
                      let c1 = class_name c0 in
                      let o = new_obj_symb_c p0 c1 in
                      let h' = add_obj_symb h s o in
                      let cl1 = Clause_neg (S_val_eq ((S_val_ref_c y0),
                        (S_val_ref_c S_ref_c_null)))
                      in
                      let cl2 = Clause_pos (S_val_subtype ((S_val_ref_c y0),
                        (S_ty_class c1)))
                      in
                      let _UU03a3_' = app _UU03a3_ (cl1 :: (cl2 :: [])) in
                      Some (h', _UU03a3_')
                    | None -> None)
              else (match obj_at h y0 with
                    | Some o ->
                      (match get o f with
                       | Some _ -> None
                       | None ->
                         (match class_with_field p0 f with
                          | Some c' ->
                            let c'0 = class_name c' in
                            let o' = refine_obj_symb_c p0 c'0 o in
                            let h' = repl_obj h y0 o' in
                            let cl = Clause_pos (S_val_subtype ((S_val_ref_c
                              y0), (S_ty_class c'0)))
                            in
                            let _UU03a3_' = app _UU03a3_ (cl :: []) in
                            Some (h', _UU03a3_')
                          | None -> None))
                    | None -> None)
            | _ -> rstep_c p0 h _UU03a3_ e2)
         | _ -> rstep_c p0 h _UU03a3_ e2)
      | _ -> rstep_c p0 h _UU03a3_ e2)
   | _ -> rstep_c p0 h _UU03a3_ e1)
| S_expr_let (_, e1, _) -> rstep_c p0 h _UU03a3_ e1
| S_expr_add (e1, e2) ->
  (match e1 with
   | S_expr_val _ -> rstep_c p0 h _UU03a3_ e2
   | _ -> rstep_c p0 h _UU03a3_ e1)
| S_expr_lt (e1, e2) ->
  (match e1 with
   | S_expr_val _ -> rstep_c p0 h _UU03a3_ e2
   | _ -> rstep_c p0 h _UU03a3_ e1)
| S_expr_eq (e1, e2) ->
  (match e1 with
   | S_expr_val _ -> rstep_c p0 h _UU03a3_ e2
   | _ -> rstep_c p0 h _UU03a3_ e1)
| S_expr_instanceof (e1, _) -> rstep_c p0 h _UU03a3_ e1
| S_expr_if (e1, _, _) -> rstep_c p0 h _UU03a3_ e1
| S_expr_invoke (e1, _, e2) ->
  (match e1 with
   | S_expr_val _ -> rstep_c p0 h _UU03a3_ e2
   | _ -> rstep_c p0 h _UU03a3_ e1)
| _ -> None

(** val rstep_c_star :
    s_prg -> heap -> path_condition -> s_expr -> (heap * path_condition)
    option **)

let rstep_c_star =
  let rstep_c_star_bounded =
    let rec rstep_c_star_bounded p0 h _UU03a3_ e n1 =
      match rstep_c p0 h _UU03a3_ e with
      | Some p1 ->
        let (h', _UU03a3_') = p1 in
        (match n1 with
         | O -> None
         | S n' -> rstep_c_star_bounded p0 h' _UU03a3_' e n')
      | None -> Some (h, _UU03a3_)
    in rstep_c_star_bounded
  in
  (fun p0 h _UU03a3_ e -> rstep_c_star_bounded p0 h _UU03a3_ e (S (S O)))

(** val cstep_c_fp_func :
    (s_prg, (heap, (path_condition, s_expr) sigT) sigT) sigT ->
    ((heap * path_condition) * s_expr) list **)

let rec cstep_c_fp_func x0 =
  let p0 = projT1 x0 in
  let h = projT1 (projT2 x0) in
  let _UU03a3_ = projT1 (projT2 (projT2 x0)) in
  let e = projT2 (projT2 (projT2 x0)) in
  let cstep_c_fp0 = fun p1 h1 _UU03a3_1 e0 ->
    cstep_c_fp_func (ExistT (p1, (ExistT (h1, (ExistT (_UU03a3_1, e0))))))
  in
  (match e with
   | S_expr_new c0 ->
     let filtered_var = cdecl p0 c0 in
     (match filtered_var with
      | Some _ ->
        let o = new_obj_c p0 c0 in
        let (h', u) = add_obj h o in
        let e' = S_expr_val (S_val_ref_c u) in ((h', _UU03a3_), e') :: []
      | None -> [])
   | S_expr_getfield (e1, f) ->
     (match e1 with
      | S_expr_val s0 ->
        (match s0 with
         | S_val_ref_c s1 ->
           (match s1 with
            | S_ref_c_null ->
              let e2 = S_expr_val (S_val_ref_c S_ref_c_null) in
              map (fun x1 ->
                let (p1, e1') = x1 in
                let (h', _UU03a3_') = p1 in
                ((h', _UU03a3_'), (S_expr_getfield (e1', f))))
                (cstep_c_fp0 p0 h _UU03a3_ e2)
            | S_ref_c_loc s ->
              let l0 = S_ref_c_loc s in
              let filtered_var = obj_at h l0 in
              (match filtered_var with
               | Some o ->
                 let filtered_var0 = get o f in
                 (match filtered_var0 with
                  | Some _UU03c3_0 ->
                    let e' = S_expr_val _UU03c3_0 in ((h, _UU03a3_), e') :: []
                  | None -> [])
               | None -> [])
            | S_ref_c_symb s ->
              let y0 = S_ref_c_symb s in
              let filtered_var = obj_at h y0 in
              (match filtered_var with
               | Some o ->
                 let filtered_var0 = get o f in
                 (match filtered_var0 with
                  | Some _UU03c3_0 ->
                    if negb (s_val_eqb _UU03c3_0 S_val_unassumed)
                    then let e' = S_expr_val _UU03c3_0 in
                         ((h, _UU03a3_), e') :: []
                    else []
                  | None -> [])
               | None -> []))
         | S_val_ite (_UU03c3_0, _UU03c3_1, _UU03c3_2) ->
           let e2 = S_expr_getfield ((S_expr_val _UU03c3_1), f) in
           let e3 = S_expr_getfield ((S_expr_val _UU03c3_2), f) in
           let filtered_var = rstep_c_star p0 h _UU03a3_ e2 in
           (match filtered_var with
            | Some p1 ->
              let (h1tmp, _UU03a3_1tmp) = p1 in
              let filtered_var0 = cstep_c_fp0 p0 h1tmp _UU03a3_1tmp e2 in
              (match filtered_var0 with
               | [] -> []
               | p2 :: l0 ->
                 let (p3, s) = p2 in
                 let (h1', _UU03a3_1') = p3 in
                 (match s with
                  | S_expr_val _UU03c3_1' ->
                    (match l0 with
                     | [] ->
                       let filtered_var1 = rstep_c_star p0 h1' _UU03a3_1' e3
                       in
                       (match filtered_var1 with
                        | Some p4 ->
                          let (htmp', _UU03a3_tmp') = p4 in
                          let filtered_var2 =
                            cstep_c_fp0 p0 htmp' _UU03a3_tmp' e3
                          in
                          (match filtered_var2 with
                           | [] -> []
                           | p5 :: l1 ->
                             let (p6, s1) = p5 in
                             let (h', _UU03a3_') = p6 in
                             (match s1 with
                              | S_expr_val _UU03c3_2' ->
                                (match l1 with
                                 | [] ->
                                   ((h', _UU03a3_'), (S_expr_val (S_val_ite
                                     (_UU03c3_0, _UU03c3_1',
                                     _UU03c3_2')))) :: []
                                 | _ :: _ -> [])
                              | _ -> []))
                        | None -> [])
                     | _ :: _ -> [])
                  | _ -> []))
            | None -> [])
         | x1 ->
           let e2 = S_expr_val x1 in
           map (fun x2 ->
             let (p1, e1') = x2 in
             let (h', _UU03a3_') = p1 in
             ((h', _UU03a3_'), (S_expr_getfield (e1', f))))
             (cstep_c_fp0 p0 h _UU03a3_ e2))
      | x1 ->
        map (fun x2 ->
          let (p1, e1') = x2 in
          let (h', _UU03a3_') = p1 in
          ((h', _UU03a3_'), (S_expr_getfield (e1', f))))
          (cstep_c_fp0 p0 h _UU03a3_ x1))
   | S_expr_putfield (e1, f, e2) ->
     (match e1 with
      | S_expr_val _UU03c3_0 ->
        (match _UU03c3_0 with
         | S_val_ref_c s0 ->
           (match s0 with
            | S_ref_c_null ->
              let _UU03c3_1 = S_val_ref_c S_ref_c_null in
              map (fun x1 ->
                let (p1, e1') = x1 in
                let (h', _UU03a3_') = p1 in
                ((h', _UU03a3_'), (S_expr_putfield ((S_expr_val _UU03c3_1),
                f, e1')))) (cstep_c_fp0 p0 h _UU03a3_ e2)
            | S_ref_c_loc s ->
              let _UU03c3_1 = S_val_ref_c (S_ref_c_loc s) in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 let l0 = S_ref_c_loc s in
                 let e' = S_expr_val _UU03c3_2 in
                 let filtered_var = obj_at h l0 in
                 (match filtered_var with
                  | Some o ->
                    let o' = upd_obj o f _UU03c3_2 in
                    let h' = repl_obj h l0 o' in ((h', _UU03a3_), e') :: []
                  | None -> [])
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_putfield ((S_expr_val
                   _UU03c3_1), f, e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
            | S_ref_c_symb s ->
              let _UU03c3_1 = S_val_ref_c (S_ref_c_symb s) in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 let y0 = S_ref_c_symb s in
                 let e' = S_expr_val _UU03c3_2 in
                 let filtered_var = obj_at h y0 in
                 (match filtered_var with
                  | Some o ->
                    let filtered_var0 = get o f in
                    (match filtered_var0 with
                     | Some _ ->
                       let o' = upd_obj o f _UU03c3_2 in
                       let hRefined = update_c f y0 _UU03c3_2 h in
                       let h' = repl_obj hRefined y0 o' in
                       ((h', _UU03a3_), e') :: []
                     | None -> [])
                  | None -> [])
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_putfield ((S_expr_val
                   _UU03c3_1), f, e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1)))
         | S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) ->
           let _UU03c3_4 = S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) in
           (match e2 with
            | S_expr_val _UU03c3_' ->
              let e' = S_expr_val _UU03c3_' in
              let e3 = S_expr_putfield ((S_expr_val _UU03c3_2), f, e') in
              let e4 = S_expr_putfield ((S_expr_val _UU03c3_3), f, e') in
              let filtered_var = rstep_c_star p0 h _UU03a3_ e3 in
              let filtered_var0 = rstep_c_star p0 h _UU03a3_ e4 in
              (match filtered_var with
               | Some p1 ->
                 let (h1tmp, _UU03a3_1tmp) = p1 in
                 (match filtered_var0 with
                  | Some p2 ->
                    let (h2tmp, _UU03a3_2tmp) = p2 in
                    let filtered_var1 = cstep_c_fp0 p0 h1tmp _UU03a3_1tmp e3
                    in
                    let filtered_var2 = cstep_c_fp0 p0 h2tmp _UU03a3_2tmp e4
                    in
                    (match filtered_var1 with
                     | [] -> []
                     | p3 :: l0 ->
                       let (p4, _) = p3 in
                       let (h1', _UU03a3_1') = p4 in
                       (match l0 with
                        | [] ->
                          (match filtered_var2 with
                           | [] -> []
                           | p5 :: l1 ->
                             let (p6, _) = p5 in
                             let (h2', _UU03a3_2') = p6 in
                             (match l1 with
                              | [] ->
                                let filtered_var3 =
                                  merge_c h1' h2' f _UU03c3_1
                                in
                                let filtered_var4 = merge_clauses h1' h2' f in
                                (match filtered_var3 with
                                 | Some h' ->
                                   (match filtered_var4 with
                                    | Some _UU03a3_etc ->
                                      let _UU03a3_' =
                                        app _UU03a3_1'
                                          (app _UU03a3_2' _UU03a3_etc)
                                      in
                                      ((h', _UU03a3_'), e') :: []
                                    | None -> [])
                                 | None -> [])
                              | _ :: _ -> []))
                        | _ :: _ -> []))
                  | None -> [])
               | None -> [])
            | x1 ->
              map (fun x2 ->
                let (p1, e1') = x2 in
                let (h', _UU03a3_') = p1 in
                ((h', _UU03a3_'), (S_expr_putfield ((S_expr_val _UU03c3_4),
                f, e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
         | x1 ->
           map (fun x2 ->
             let (p1, e1') = x2 in
             let (h', _UU03a3_') = p1 in
             ((h', _UU03a3_'), (S_expr_putfield ((S_expr_val x1), f, e1'))))
             (cstep_c_fp0 p0 h _UU03a3_ e2))
      | x1 ->
        map (fun x2 ->
          let (p1, e1') = x2 in
          let (h', _UU03a3_') = p1 in
          ((h', _UU03a3_'), (S_expr_putfield (e1', f, e2))))
          (cstep_c_fp0 p0 h _UU03a3_ x1))
   | S_expr_let (xN, e1, e2) ->
     (match e1 with
      | S_expr_val _UU03c3_0 ->
        let e' = repl_var e2 xN (S_expr_val _UU03c3_0) in
        ((h, _UU03a3_), e') :: []
      | x1 ->
        map (fun x2 ->
          let (p1, e1') = x2 in
          let (h', _UU03a3_') = p1 in
          ((h', _UU03a3_'), (S_expr_let (xN, e1', e2))))
          (cstep_c_fp0 p0 h _UU03a3_ x1))
   | S_expr_add (e1, e2) ->
     (match e1 with
      | S_expr_val _UU03c3_0 ->
        (match _UU03c3_0 with
         | S_val_prim_c s ->
           (match s with
            | S_prim_c_int s0 ->
              let _UU03c3_1 = S_val_prim_c (S_prim_c_int s0) in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 (match _UU03c3_2 with
                  | S_val_prim_c s1 ->
                    (match s1 with
                     | S_prim_c_int s2 ->
                       let e' = S_expr_val (S_val_prim_c (S_prim_c_int
                         (add s0 s2)))
                       in
                       ((h, _UU03a3_), e') :: []
                     | x1 ->
                       let _UU03c3_3 = S_val_prim_c x1 in
                       let e' = S_expr_val (S_val_add (_UU03c3_1, _UU03c3_3))
                       in
                       ((h, _UU03a3_), e') :: [])
                  | x1 ->
                    let e' = S_expr_val (S_val_add (_UU03c3_1, x1)) in
                    ((h, _UU03a3_), e') :: [])
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_add ((S_expr_val _UU03c3_1),
                   e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
            | x1 ->
              let _UU03c3_1 = S_val_prim_c x1 in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 let e' = S_expr_val (S_val_add (_UU03c3_1, _UU03c3_2)) in
                 ((h, _UU03a3_), e') :: []
               | x2 ->
                 map (fun x3 ->
                   let (p1, e1') = x3 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_add ((S_expr_val _UU03c3_1),
                   e1')))) (cstep_c_fp0 p0 h _UU03a3_ x2)))
         | x1 ->
           (match e2 with
            | S_expr_val _UU03c3_2 ->
              let e' = S_expr_val (S_val_add (x1, _UU03c3_2)) in
              ((h, _UU03a3_), e') :: []
            | x2 ->
              map (fun x3 ->
                let (p1, e1') = x3 in
                let (h', _UU03a3_') = p1 in
                ((h', _UU03a3_'), (S_expr_add ((S_expr_val x1), e1'))))
                (cstep_c_fp0 p0 h _UU03a3_ x2)))
      | x1 ->
        map (fun x2 ->
          let (p1, e1') = x2 in
          let (h', _UU03a3_') = p1 in
          ((h', _UU03a3_'), (S_expr_add (e1', e2))))
          (cstep_c_fp0 p0 h _UU03a3_ x1))
   | S_expr_lt (e1, e2) ->
     (match e1 with
      | S_expr_val _UU03c3_0 ->
        (match _UU03c3_0 with
         | S_val_prim_c s ->
           (match s with
            | S_prim_c_int s0 ->
              let _UU03c3_1 = S_val_prim_c (S_prim_c_int s0) in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 (match _UU03c3_2 with
                  | S_val_prim_c s1 ->
                    (match s1 with
                     | S_prim_c_int s2 ->
                       let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                         (if Nat.ltb s0 s2 then S_bool_true else S_bool_false)))
                       in
                       ((h, _UU03a3_), e') :: []
                     | x1 ->
                       let _UU03c3_3 = S_val_prim_c x1 in
                       let e' = S_expr_val (S_val_lt (_UU03c3_1, _UU03c3_3))
                       in
                       ((h, _UU03a3_), e') :: [])
                  | x1 ->
                    let e' = S_expr_val (S_val_lt (_UU03c3_1, x1)) in
                    ((h, _UU03a3_), e') :: [])
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_lt ((S_expr_val _UU03c3_1),
                   e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
            | x1 ->
              let _UU03c3_1 = S_val_prim_c x1 in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 let e' = S_expr_val (S_val_lt (_UU03c3_1, _UU03c3_2)) in
                 ((h, _UU03a3_), e') :: []
               | x2 ->
                 map (fun x3 ->
                   let (p1, e1') = x3 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_lt ((S_expr_val _UU03c3_1),
                   e1')))) (cstep_c_fp0 p0 h _UU03a3_ x2)))
         | x1 ->
           (match e2 with
            | S_expr_val _UU03c3_2 ->
              let e' = S_expr_val (S_val_lt (x1, _UU03c3_2)) in
              ((h, _UU03a3_), e') :: []
            | x2 ->
              map (fun x3 ->
                let (p1, e1') = x3 in
                let (h', _UU03a3_') = p1 in
                ((h', _UU03a3_'), (S_expr_lt ((S_expr_val x1), e1'))))
                (cstep_c_fp0 p0 h _UU03a3_ x2)))
      | x1 ->
        map (fun x2 ->
          let (p1, e1') = x2 in
          let (h', _UU03a3_') = p1 in ((h', _UU03a3_'), (S_expr_lt (e1', e2))))
          (cstep_c_fp0 p0 h _UU03a3_ x1))
   | S_expr_eq (e1, e2) ->
     (match e1 with
      | S_expr_val _UU03c3_0 ->
        (match _UU03c3_0 with
         | S_val_prim_c s ->
           (match s with
            | S_prim_c_bool s0 ->
              (match s0 with
               | S_bool_true ->
                 let _UU03c3_1 = S_val_prim_c (S_prim_c_bool S_bool_true) in
                 (match e2 with
                  | S_expr_val _UU03c3_2 ->
                    (match _UU03c3_2 with
                     | S_val_prim_c s1 ->
                       (match s1 with
                        | S_prim_c_bool s2 ->
                          (match s2 with
                           | S_bool_true ->
                             let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                               S_bool_true))
                             in
                             ((h, _UU03a3_), e') :: []
                           | S_bool_false ->
                             let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                               S_bool_false))
                             in
                             ((h, _UU03a3_), e') :: [])
                        | x1 ->
                          let _UU03c3_3 = S_val_prim_c x1 in
                          let e' = S_expr_val (S_val_eq (_UU03c3_1,
                            _UU03c3_3))
                          in
                          ((h, _UU03a3_), e') :: [])
                     | x1 ->
                       let e' = S_expr_val (S_val_eq (_UU03c3_1, x1)) in
                       ((h, _UU03a3_), e') :: [])
                  | x1 ->
                    map (fun x2 ->
                      let (p1, e1') = x2 in
                      let (h', _UU03a3_') = p1 in
                      ((h', _UU03a3_'), (S_expr_eq ((S_expr_val _UU03c3_1),
                      e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
               | S_bool_false ->
                 let _UU03c3_1 = S_val_prim_c (S_prim_c_bool S_bool_false) in
                 (match e2 with
                  | S_expr_val _UU03c3_2 ->
                    (match _UU03c3_2 with
                     | S_val_prim_c s1 ->
                       (match s1 with
                        | S_prim_c_bool s2 ->
                          (match s2 with
                           | S_bool_true ->
                             let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                               S_bool_false))
                             in
                             ((h, _UU03a3_), e') :: []
                           | S_bool_false ->
                             let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                               S_bool_true))
                             in
                             ((h, _UU03a3_), e') :: [])
                        | x1 ->
                          let _UU03c3_3 = S_val_prim_c x1 in
                          let e' = S_expr_val (S_val_eq (_UU03c3_1,
                            _UU03c3_3))
                          in
                          ((h, _UU03a3_), e') :: [])
                     | x1 ->
                       let e' = S_expr_val (S_val_eq (_UU03c3_1, x1)) in
                       ((h, _UU03a3_), e') :: [])
                  | x1 ->
                    map (fun x2 ->
                      let (p1, e1') = x2 in
                      let (h', _UU03a3_') = p1 in
                      ((h', _UU03a3_'), (S_expr_eq ((S_expr_val _UU03c3_1),
                      e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1)))
            | S_prim_c_int s0 ->
              let _UU03c3_1 = S_val_prim_c (S_prim_c_int s0) in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 (match _UU03c3_2 with
                  | S_val_prim_c s1 ->
                    (match s1 with
                     | S_prim_c_int s2 ->
                       let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                         (if Nat.eqb s0 s2 then S_bool_true else S_bool_false)))
                       in
                       ((h, _UU03a3_), e') :: []
                     | x1 ->
                       let _UU03c3_3 = S_val_prim_c x1 in
                       let e' = S_expr_val (S_val_eq (_UU03c3_1, _UU03c3_3))
                       in
                       ((h, _UU03a3_), e') :: [])
                  | x1 ->
                    let e' = S_expr_val (S_val_eq (_UU03c3_1, x1)) in
                    ((h, _UU03a3_), e') :: [])
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_eq ((S_expr_val _UU03c3_1),
                   e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
            | S_prim_c_symb s0 ->
              let _UU03c3_1 = S_val_prim_c (S_prim_c_symb s0) in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 let e' = S_expr_val (S_val_eq (_UU03c3_1, _UU03c3_2)) in
                 ((h, _UU03a3_), e') :: []
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_eq ((S_expr_val _UU03c3_1),
                   e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1)))
         | S_val_ref_c s ->
           (match s with
            | S_ref_c_null ->
              let _UU03c3_1 = S_val_ref_c S_ref_c_null in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 (match _UU03c3_2 with
                  | S_val_ref_c s0 ->
                    (match s0 with
                     | S_ref_c_null ->
                       let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                         S_bool_true))
                       in
                       ((h, _UU03a3_), e') :: []
                     | S_ref_c_loc _ ->
                       let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                         S_bool_false))
                       in
                       ((h, _UU03a3_), e') :: []
                     | S_ref_c_symb s1 ->
                       let _UU03c3_3 = S_val_ref_c (S_ref_c_symb s1) in
                       let e' = S_expr_val (S_val_eq (_UU03c3_1, _UU03c3_3))
                       in
                       ((h, _UU03a3_), e') :: [])
                  | x1 ->
                    let e' = S_expr_val (S_val_eq (_UU03c3_1, x1)) in
                    ((h, _UU03a3_), e') :: [])
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_eq ((S_expr_val _UU03c3_1),
                   e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
            | S_ref_c_loc wildcard' ->
              let _UU03c3_1 = S_val_ref_c (S_ref_c_loc wildcard') in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 (match _UU03c3_2 with
                  | S_val_ref_c s0 ->
                    (match s0 with
                     | S_ref_c_null ->
                       let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                         S_bool_false))
                       in
                       ((h, _UU03a3_), e') :: []
                     | S_ref_c_loc s1 ->
                       let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                         (if Nat.eqb wildcard' s1
                          then S_bool_true
                          else S_bool_false)))
                       in
                       ((h, _UU03a3_), e') :: []
                     | S_ref_c_symb s1 ->
                       let _UU03c3_3 = S_val_ref_c (S_ref_c_symb s1) in
                       let e' = S_expr_val (S_val_eq (_UU03c3_1, _UU03c3_3))
                       in
                       ((h, _UU03a3_), e') :: [])
                  | x1 ->
                    let e' = S_expr_val (S_val_eq (_UU03c3_1, x1)) in
                    ((h, _UU03a3_), e') :: [])
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_eq ((S_expr_val _UU03c3_1),
                   e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
            | S_ref_c_symb s0 ->
              let _UU03c3_1 = S_val_ref_c (S_ref_c_symb s0) in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 let e' = S_expr_val (S_val_eq (_UU03c3_1, _UU03c3_2)) in
                 ((h, _UU03a3_), e') :: []
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_eq ((S_expr_val _UU03c3_1),
                   e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1)))
         | x1 ->
           (match e2 with
            | S_expr_val _UU03c3_2 ->
              let e' = S_expr_val (S_val_eq (x1, _UU03c3_2)) in
              ((h, _UU03a3_), e') :: []
            | x2 ->
              map (fun x3 ->
                let (p1, e1') = x3 in
                let (h', _UU03a3_') = p1 in
                ((h', _UU03a3_'), (S_expr_eq ((S_expr_val x1), e1'))))
                (cstep_c_fp0 p0 h _UU03a3_ x2)))
      | x1 ->
        map (fun x2 ->
          let (p1, e1') = x2 in
          let (h', _UU03a3_') = p1 in ((h', _UU03a3_'), (S_expr_eq (e1', e2))))
          (cstep_c_fp0 p0 h _UU03a3_ x1))
   | S_expr_instanceof (e1, c0) ->
     (match e1 with
      | S_expr_val s0 ->
        (match s0 with
         | S_val_ref_c s1 ->
           (match s1 with
            | S_ref_c_null ->
              let e' = S_expr_val (S_val_prim_c (S_prim_c_bool S_bool_false))
              in
              ((h, _UU03a3_), e') :: []
            | S_ref_c_loc s ->
              let l0 = S_ref_c_loc s in
              let filtered_var = obj_class_at h l0 in
              (match filtered_var with
               | Some c' ->
                 let e' = S_expr_val (S_val_prim_c (S_prim_c_bool
                   (if subclass_c p0 c' c0 then S_bool_true else S_bool_false)))
                 in
                 ((h, _UU03a3_), e') :: []
               | None -> [])
            | S_ref_c_symb s ->
              let y0 = S_ref_c_symb s in
              let e' = S_expr_val (S_val_subtype ((S_val_ref_c y0),
                (S_ty_class c0)))
              in
              ((h, _UU03a3_), e') :: [])
         | x1 ->
           let e2 = S_expr_val x1 in
           map (fun x2 ->
             let (p1, e1') = x2 in
             let (h', _UU03a3_') = p1 in
             ((h', _UU03a3_'), (S_expr_instanceof (e1', c0))))
             (cstep_c_fp0 p0 h _UU03a3_ e2))
      | x1 ->
        map (fun x2 ->
          let (p1, e1') = x2 in
          let (h', _UU03a3_') = p1 in
          ((h', _UU03a3_'), (S_expr_instanceof (e1', c0))))
          (cstep_c_fp0 p0 h _UU03a3_ x1))
   | S_expr_if (e1, e2, e3) ->
     (match e1 with
      | S_expr_val _UU03c3_0 ->
        (match _UU03c3_0 with
         | S_val_prim_c s ->
           (match s with
            | S_prim_c_bool s0 ->
              (match s0 with
               | S_bool_true -> ((h, _UU03a3_), e2) :: []
               | S_bool_false -> ((h, _UU03a3_), e3) :: [])
            | x1 ->
              let _UU03c3_1 = S_val_prim_c x1 in
              let _UU03a3_1' = app _UU03a3_ ((Clause_pos _UU03c3_1) :: []) in
              let _UU03a3_2' = app _UU03a3_ ((Clause_neg _UU03c3_1) :: []) in
              ((h, _UU03a3_1'), e2) :: (((h, _UU03a3_2'), e3) :: []))
         | x1 ->
           let _UU03a3_1' = app _UU03a3_ ((Clause_pos x1) :: []) in
           let _UU03a3_2' = app _UU03a3_ ((Clause_neg x1) :: []) in
           ((h, _UU03a3_1'), e2) :: (((h, _UU03a3_2'), e3) :: []))
      | x1 ->
        map (fun x2 ->
          let (p1, e1') = x2 in
          let (h', _UU03a3_') = p1 in
          ((h', _UU03a3_'), (S_expr_if (e1', e2, e3))))
          (cstep_c_fp0 p0 h _UU03a3_ x1))
   | S_expr_invoke (e1, m, e2) ->
     (match e1 with
      | S_expr_val _UU03c3_0 ->
        (match _UU03c3_0 with
         | S_val_ref_c s0 ->
           (match s0 with
            | S_ref_c_null ->
              let _UU03c3_1 = S_val_ref_c S_ref_c_null in
              map (fun x1 ->
                let (p1, e1') = x1 in
                let (h', _UU03a3_') = p1 in
                ((h', _UU03a3_'), (S_expr_invoke ((S_expr_val _UU03c3_1), m,
                e1')))) (cstep_c_fp0 p0 h _UU03a3_ e2)
            | S_ref_c_loc s ->
              let _UU03c3_1 = S_val_ref_c (S_ref_c_loc s) in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 let l0 = S_ref_c_loc s in
                 let filtered_var = obj_at h l0 in
                 let filtered_var0 = obj_class_at h l0 in
                 (match filtered_var with
                  | Some _ ->
                    (match filtered_var0 with
                     | Some c0 ->
                       let filtered_var1 = method_provider p0 m c0 in
                       (match filtered_var1 with
                        | Some c' ->
                          let filtered_var2 = mdecl p0 c' m in
                          (match filtered_var2 with
                           | Some s1 ->
                             let S_dc_m_l (_, _, s2, eM) = s1 in
                             let S_dc_v_l (_, xM) = s2 in
                             let e' =
                               repl_var
                                 (repl_var eM "this" (S_expr_val (S_val_ref_c
                                   l0))) xM (S_expr_val _UU03c3_2)
                             in
                             ((h, _UU03a3_), e') :: []
                           | None -> [])
                        | None -> [])
                     | None -> [])
                  | None -> [])
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_invoke ((S_expr_val _UU03c3_1),
                   m, e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
            | S_ref_c_symb s ->
              let _UU03c3_1 = S_val_ref_c (S_ref_c_symb s) in
              (match e2 with
               | S_expr_val _UU03c3_2 ->
                 let y0 = S_ref_c_symb s in
                 let cs' = implementors p0 m in
                 concat
                   (map (fun c' ->
                     let filtered_var = mdecl p0 c' m in
                     (match filtered_var with
                      | Some s1 ->
                        let S_dc_m_l (_, m0, s2, eM) = s1 in
                        let S_dc_v_l (_, xM) = s2 in
                        let o = overriders p0 m0 c' in
                        let cl1 = Clause_neg (S_val_eq ((S_val_ref_c y0),
                          (S_val_ref_c S_ref_c_null)))
                        in
                        let cl2 = Clause_pos (S_val_subtype ((S_val_ref_c
                          y0), (S_ty_class c')))
                        in
                        let _UU03a3_' =
                          app _UU03a3_
                            (app (cl1 :: (cl2 :: []))
                              (map (fun c0 -> Clause_neg (S_val_subtype
                                ((S_val_ref_c y0), (S_ty_class c0)))) o))
                        in
                        let e' =
                          repl_var
                            (repl_var eM "this" (S_expr_val (S_val_ref_c y0)))
                            xM (S_expr_val _UU03c3_2)
                        in
                        ((h, _UU03a3_'), e') :: []
                      | None -> [])) cs')
               | x1 ->
                 map (fun x2 ->
                   let (p1, e1') = x2 in
                   let (h', _UU03a3_') = p1 in
                   ((h', _UU03a3_'), (S_expr_invoke ((S_expr_val _UU03c3_1),
                   m, e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1)))
         | S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) ->
           let _UU03c3_4 = S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) in
           (match e2 with
            | S_expr_val _UU03c3_' ->
              let e3 = S_expr_invoke ((S_expr_val _UU03c3_2), m, (S_expr_val
                _UU03c3_'))
              in
              let e4 = S_expr_invoke ((S_expr_val _UU03c3_3), m, (S_expr_val
                _UU03c3_'))
              in
              app
                (map (fun x1 ->
                  let (p1, e1') = x1 in
                  let (_, _UU03a3_1') = p1 in
                  let _UU03a3_' =
                    app _UU03a3_1' ((Clause_pos _UU03c3_1) :: [])
                  in
                  ((h, _UU03a3_'), e1')) (cstep_c_fp0 p0 h _UU03a3_ e3))
                (map (fun x1 ->
                  let (p1, e2') = x1 in
                  let (_, _UU03a3_2') = p1 in
                  let _UU03a3_' =
                    app _UU03a3_2' ((Clause_neg _UU03c3_1) :: [])
                  in
                  ((h, _UU03a3_'), e2')) (cstep_c_fp0 p0 h _UU03a3_ e4))
            | x1 ->
              map (fun x2 ->
                let (p1, e1') = x2 in
                let (h', _UU03a3_') = p1 in
                ((h', _UU03a3_'), (S_expr_invoke ((S_expr_val _UU03c3_4), m,
                e1')))) (cstep_c_fp0 p0 h _UU03a3_ x1))
         | x1 ->
           map (fun x2 ->
             let (p1, e1') = x2 in
             let (h', _UU03a3_') = p1 in
             ((h', _UU03a3_'), (S_expr_invoke ((S_expr_val x1), m, e1'))))
             (cstep_c_fp0 p0 h _UU03a3_ e2))
      | x1 ->
        map (fun x2 ->
          let (p1, e1') = x2 in
          let (h', _UU03a3_') = p1 in
          ((h', _UU03a3_'), (S_expr_invoke (e1', m, e2))))
          (cstep_c_fp0 p0 h _UU03a3_ x1))
   | _ -> [])

(** val cstep_c_fp :
    s_prg -> heap -> path_condition -> s_expr ->
    ((heap * path_condition) * s_expr) list **)

let cstep_c_fp p0 h _UU03a3_ e =
  cstep_c_fp_func (ExistT (p0, (ExistT (h, (ExistT (_UU03a3_, e))))))

(** val step_c : config -> config list **)

let step_c =
  let cstep_c = fun j ->
    let (aA, e) = j in
    let (bB, _UU03a3_) = aA in
    let (p0, h) = bB in
    let next = cstep_c_fp p0 h _UU03a3_ e in
    map (fun x0 ->
      let (y0, e') = x0 in
      let (h', _UU03a3_') = y0 in (((p0, h'), _UU03a3_'), e')) next
  in
  (fun j ->
  let (aA, e) = j in
  let (bB, _UU03a3_) = aA in
  let (p0, h) = bB in
  (match rstep_c_star p0 h _UU03a3_ e with
   | Some p1 -> let (h', _UU03a3_') = p1 in cstep_c (((p0, h'), _UU03a3_'), e)
   | None -> []))

(** val compute : s_prg -> computation **)

let compute =
  let do_compute =
    let rec do_compute js =
      lazy (Cons (js, (do_compute (concat (map step_c js)))))
    in do_compute
  in
  (fun p0 -> let j0 = config_initial p0 in do_compute (j0 :: []))

(** val step_at : s_prg -> nat -> config list **)

let step_at p0 n1 =
  str_nth n1 (compute p0)

(** val isWhite : char -> bool **)

let isWhite c0 =
  let n1 = nat_of_ascii c0 in
  (||)
    ((||)
      (Nat.eqb n1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))
      (Nat.eqb n1 (S (S (S (S (S (S (S (S (S O)))))))))))
    ((||) (Nat.eqb n1 (S (S (S (S (S (S (S (S (S (S O)))))))))))
      (Nat.eqb n1 (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))

(** val isAlpha : char -> bool **)

let isAlpha c0 =
  let n1 = nat_of_ascii c0 in
  (||)
    ((&&)
      (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) n1)
      (Nat.leb n1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ((&&)
      (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        n1)
      (Nat.leb n1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val isDigit : char -> bool **)

let isDigit c0 =
  let n1 = nat_of_ascii c0 in
  (&&)
    (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))) n1)
    (Nat.leb n1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type chartype =
| White
| Alpha
| Digit
| Other

(** val classifyChar : char -> chartype **)

let classifyChar c0 =
  if isWhite c0
  then White
  else if isAlpha c0 then Alpha else if isDigit c0 then Digit else Other

(** val list_of_string : string -> char list **)

let rec list_of_string s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> [])
    (fun c0 s0 -> c0 :: (list_of_string s0))
    s

(** val string_of_list : char list -> string **)

let string_of_list xs =
  fold_right (fun x0 x1 ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (x0, x1)) "" xs

type token = string

(** val tokenize_helper :
    chartype -> char list -> char list -> char list list **)

let rec tokenize_helper cls acc xs =
  let tk = match acc with
           | [] -> []
           | _ :: _ -> (rev acc) :: [] in
  (match xs with
   | [] -> tk
   | x0 :: xs' ->
     (match cls with
      | White ->
        (match classifyChar x0 with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
             if b0
             then if b1
                  then app tk (tokenize_helper White [] xs')
                  else if b2
                       then app tk (tokenize_helper White [] xs')
                       else if b3
                            then if b4
                                 then app tk (tokenize_helper White [] xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b1
                  then app tk (tokenize_helper White [] xs')
                  else if b2
                       then app tk (tokenize_helper White [] xs')
                       else if b3
                            then if b4
                                 then app tk (tokenize_helper White [] xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x0
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
             if b0
             then if b1
                  then app tk (tokenize_helper tp (x0 :: []) xs')
                  else if b2
                       then app tk (tokenize_helper tp (x0 :: []) xs')
                       else if b3
                            then if b4
                                 then app tk
                                        (tokenize_helper tp (x0 :: []) xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x0 :: []) xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x0 :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x0 :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x0 :: []) xs')
             else if b1
                  then app tk (tokenize_helper tp (x0 :: []) xs')
                  else if b2
                       then app tk (tokenize_helper tp (x0 :: []) xs')
                       else if b3
                            then if b4
                                 then app tk
                                        (tokenize_helper tp (x0 :: []) xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x0 :: []) xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x0 :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x0 :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x0 :: []) xs'))
             x0
         | x1 ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
             if b0
             then if b1
                  then app tk (tokenize_helper x1 (x0 :: []) xs')
                  else if b2
                       then app tk (tokenize_helper x1 (x0 :: []) xs')
                       else if b3
                            then if b4
                                 then app tk
                                        (tokenize_helper x1 (x0 :: []) xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper x1
                                                    (x0 :: []) xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper x1
                                                         (x0 :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x1 (x0 :: [])
                                               xs')
                            else app tk (tokenize_helper x1 (x0 :: []) xs')
             else if b1
                  then app tk (tokenize_helper x1 (x0 :: []) xs')
                  else if b2
                       then app tk (tokenize_helper x1 (x0 :: []) xs')
                       else if b3
                            then if b4
                                 then app tk
                                        (tokenize_helper x1 (x0 :: []) xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper x1
                                                    (x0 :: []) xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper x1
                                                         (x0 :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x1 (x0 :: [])
                                               xs')
                            else app tk (tokenize_helper x1 (x0 :: []) xs'))
             x0)
      | Other ->
        (match classifyChar x0 with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
             if b0
             then if b1
                  then app tk (tokenize_helper White [] xs')
                  else if b2
                       then app tk (tokenize_helper White [] xs')
                       else if b3
                            then if b4
                                 then app tk (tokenize_helper White [] xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b1
                  then app tk (tokenize_helper White [] xs')
                  else if b2
                       then app tk (tokenize_helper White [] xs')
                       else if b3
                            then if b4
                                 then app tk (tokenize_helper White [] xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x0
         | Other ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
             if b0
             then if b1
                  then tokenize_helper Other (x0 :: acc) xs'
                  else if b2
                       then tokenize_helper Other (x0 :: acc) xs'
                       else if b3
                            then if b4
                                 then tokenize_helper Other (x0 :: acc) xs'
                                 else if b5
                                      then if b6
                                           then tokenize_helper Other
                                                  (x0 :: acc) xs'
                                           else if b7
                                                then tokenize_helper Other
                                                       (x0 :: acc) xs'
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Other (x0 :: acc)
                                             xs'
                            else tokenize_helper Other (x0 :: acc) xs'
             else if b1
                  then tokenize_helper Other (x0 :: acc) xs'
                  else if b2
                       then tokenize_helper Other (x0 :: acc) xs'
                       else if b3
                            then if b4
                                 then tokenize_helper Other (x0 :: acc) xs'
                                 else if b5
                                      then if b6
                                           then tokenize_helper Other
                                                  (x0 :: acc) xs'
                                           else if b7
                                                then tokenize_helper Other
                                                       (x0 :: acc) xs'
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper Other (x0 :: acc)
                                             xs'
                            else tokenize_helper Other (x0 :: acc) xs')
             x0
         | x1 ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
             if b0
             then if b1
                  then app tk (tokenize_helper x1 (x0 :: []) xs')
                  else if b2
                       then app tk (tokenize_helper x1 (x0 :: []) xs')
                       else if b3
                            then if b4
                                 then app tk
                                        (tokenize_helper x1 (x0 :: []) xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper x1
                                                    (x0 :: []) xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper x1
                                                         (x0 :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x1 (x0 :: [])
                                               xs')
                            else app tk (tokenize_helper x1 (x0 :: []) xs')
             else if b1
                  then app tk (tokenize_helper x1 (x0 :: []) xs')
                  else if b2
                       then app tk (tokenize_helper x1 (x0 :: []) xs')
                       else if b3
                            then if b4
                                 then app tk
                                        (tokenize_helper x1 (x0 :: []) xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper x1
                                                    (x0 :: []) xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper x1
                                                         (x0 :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper x1 (x0 :: [])
                                               xs')
                            else app tk (tokenize_helper x1 (x0 :: []) xs'))
             x0)
      | _ ->
        (match classifyChar x0 with
         | White ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
             if b0
             then if b1
                  then app tk (tokenize_helper White [] xs')
                  else if b2
                       then app tk (tokenize_helper White [] xs')
                       else if b3
                            then if b4
                                 then app tk (tokenize_helper White [] xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs')
             else if b1
                  then app tk (tokenize_helper White [] xs')
                  else if b2
                       then app tk (tokenize_helper White [] xs')
                       else if b3
                            then if b4
                                 then app tk (tokenize_helper White [] xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper White []
                                                    xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper White
                                                         [] xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper White [] xs')
                            else app tk (tokenize_helper White [] xs'))
             x0
         | Other ->
           let tp = Other in
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
             if b0
             then if b1
                  then app tk (tokenize_helper tp (x0 :: []) xs')
                  else if b2
                       then app tk (tokenize_helper tp (x0 :: []) xs')
                       else if b3
                            then if b4
                                 then app tk
                                        (tokenize_helper tp (x0 :: []) xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x0 :: []) xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x0 :: []) xs')
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x0 :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x0 :: []) xs')
             else if b1
                  then app tk (tokenize_helper tp (x0 :: []) xs')
                  else if b2
                       then app tk (tokenize_helper tp (x0 :: []) xs')
                       else if b3
                            then if b4
                                 then app tk
                                        (tokenize_helper tp (x0 :: []) xs')
                                 else if b5
                                      then if b6
                                           then app tk
                                                  (tokenize_helper tp
                                                    (x0 :: []) xs')
                                           else if b7
                                                then app tk
                                                       (tokenize_helper tp
                                                         (x0 :: []) xs')
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else app tk
                                             (tokenize_helper tp (x0 :: [])
                                               xs')
                            else app tk (tokenize_helper tp (x0 :: []) xs'))
             x0
         | x1 ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
             if b0
             then if b1
                  then tokenize_helper x1 (x0 :: acc) xs'
                  else if b2
                       then tokenize_helper x1 (x0 :: acc) xs'
                       else if b3
                            then if b4
                                 then tokenize_helper x1 (x0 :: acc) xs'
                                 else if b5
                                      then if b6
                                           then tokenize_helper x1
                                                  (x0 :: acc) xs'
                                           else if b7
                                                then tokenize_helper x1
                                                       (x0 :: acc) xs'
                                                else app tk
                                                       ((')' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper x1 (x0 :: acc) xs'
                            else tokenize_helper x1 (x0 :: acc) xs'
             else if b1
                  then tokenize_helper x1 (x0 :: acc) xs'
                  else if b2
                       then tokenize_helper x1 (x0 :: acc) xs'
                       else if b3
                            then if b4
                                 then tokenize_helper x1 (x0 :: acc) xs'
                                 else if b5
                                      then if b6
                                           then tokenize_helper x1
                                                  (x0 :: acc) xs'
                                           else if b7
                                                then tokenize_helper x1
                                                       (x0 :: acc) xs'
                                                else app tk
                                                       (('(' :: []) :: 
                                                       (tokenize_helper Other
                                                         [] xs'))
                                      else tokenize_helper x1 (x0 :: acc) xs'
                            else tokenize_helper x1 (x0 :: acc) xs')
             x0)))

(** val tokenize : string -> string list **)

let tokenize s =
  map string_of_list (tokenize_helper White [] (list_of_string s))

type 'x optionE =
| SomeE of 'x
| NoneE of string

(** val optionE_map : ('a1 -> 'a2) -> 'a1 optionE -> 'a2 optionE **)

let optionE_map f = function
| SomeE x0 -> SomeE (f x0)
| NoneE s -> NoneE s

type 't parser0 = token list -> token list * 't optionE

(** val match_token : string -> string parser0 **)

let match_token s = function
| [] -> ([], (NoneE ((^) "Expected " ((^) s ", found end of stream"))))
| token0 :: toks' ->
  if (=) token0 s
  then (toks', (SomeE s))
  else (toks', (NoneE ((^) "Expected " ((^) s ((^) ", found " token0)))))

(** val and_then : 'a1 parser0 -> ('a1 -> 'a2 parser0) -> 'a2 parser0 **)

let and_then p0 f toks =
  let (toks', o) = p0 toks in
  (match o with
   | SomeE t1 -> f t1 toks'
   | NoneE s -> (toks', (NoneE s)))

(** val alt : 'a1 parser0 -> 'a1 parser0 -> 'a1 parser0 **)

let alt p0 q toks =
  let (toks', o) = p0 toks in
  (match o with
   | SomeE t1 -> (toks', (SomeE t1))
   | NoneE _ -> q toks)

(** val star_bounded_aux :
    'a1 parser0 -> nat -> token list -> 'a1 list -> token list * 'a1 list
    optionE **)

let rec star_bounded_aux p0 n1 toks l0 =
  let (toks', o) = p0 toks in
  (match o with
   | SomeE t1 ->
     (match n1 with
      | O -> (toks, (NoneE "Too many matches, exhausted bound"))
      | S n' -> star_bounded_aux p0 n' toks' (t1 :: l0))
   | NoneE _ -> (toks, (SomeE (rev l0))))

(** val star_bounded : 'a1 parser0 -> nat -> 'a1 list parser0 **)

let star_bounded p0 n1 toks =
  star_bounded_aux p0 n1 toks []

(** val transform : 'a1 parser0 -> ('a1 -> 'a2) -> 'a2 parser0 **)

let transform p0 f toks =
  let (toks0, result) = p0 toks in (toks0, (optionE_map f result))

(** val b : s_bool parser0 **)

let b = function
| [] -> ([], (NoneE "Expected boolean, found end of stream"))
| token0 :: toks' ->
  if (=) token0 "true"
  then (toks', (SomeE S_bool_true))
  else if (=) token0 "false"
       then (toks', (SomeE S_bool_false))
       else (toks', (NoneE ((^) "Expected boolean, found " token0)))

(** val string_to_nat : string -> nat **)

let string_to_nat token0 =
  fold_left (fun n1 d0 ->
    add (mul (S (S (S (S (S (S (S (S (S (S O)))))))))) n1)
      (sub (nat_of_ascii d0) (nat_of_ascii '0'))) (list_of_string token0) O

(** val nat_token : string parser0 **)

let nat_token = function
| [] -> ([], (NoneE "Expected natural number, found end of stream."))
| token0 :: toks' ->
  if forallb isDigit (list_of_string token0)
  then (toks', (SomeE token0))
  else (toks', (NoneE ((^) "Expected natural number, found " token0)))

(** val n0 : s_int parser0 **)

let n0 =
  transform nat_token string_to_nat

(** val char_nat_token : char -> nat parser0 **)

let char_nat_token char = function
| [] ->
  ([], (NoneE
    ((^) "Expected char "
      ((^)
        ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

        (char, "")) " plus natural number, found end of stream."))))
| token0 :: toks' ->
  (match list_of_string token0 with
   | [] ->
     (toks', (NoneE
       ((^) "Expected char "
         ((^)
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (char, "")) " plus natural number, found empty token"))))
   | c0 :: ltoken' ->
     if (&&) (Nat.eqb (nat_of_ascii c0) (nat_of_ascii char))
          (forallb isDigit ltoken')
     then (toks', (SomeE (string_to_nat (string_of_list ltoken'))))
     else (toks', (NoneE
            ((^) "Expected char "
              ((^)
                ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (char, "")) ((^) " plus natural number, found " token0))))))

(** val l : s_loc parser0 **)

let l =
  transform (char_nat_token 'L') (fun x0 -> x0)

(** val x : s_symb parser0 **)

let x =
  transform (char_nat_token 'X') (fun x0 -> S_symb_expr x0)

(** val y : s_symb parser0 **)

let y =
  transform (char_nat_token 'Y') (fun x0 -> S_symb_expr x0)

(** val _UU03c3_ : s_val parser0 **)

let _UU03c3_ =
  alt
    (alt
      (alt
        (alt
          (alt
            (alt (transform (match_token "BOT") (fun _ -> S_val_unassumed))
              (transform b (fun x0 -> S_val_prim_c (S_prim_c_bool x0))))
            (transform n0 (fun x0 -> S_val_prim_c (S_prim_c_int x0))))
          (transform x (fun x0 -> S_val_prim_c (S_prim_c_symb x0))))
        (transform (match_token "null") (fun _ -> S_val_ref_c S_ref_c_null)))
      (transform l (fun x0 -> S_val_ref_c (S_ref_c_loc x0))))
    (transform y (fun x0 -> S_val_ref_c (S_ref_c_symb x0)))

(** val identifier : string parser0 **)

let identifier = function
| [] -> ([], (NoneE "Expected identifier, found end of stream."))
| token0 :: toks' ->
  if isAlpha (hd '0' (list_of_string token0))
  then (toks', (SomeE token0))
  else (toks', (NoneE ((^) "Expected identifier, found " token0)))

(** val max_expr : nat **)

let max_expr =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val expr : nat -> s_expr parser0 **)

let rec expr = function
| O -> (fun toks -> (toks, (NoneE "Exhausted subexpression recursion bound")))
| S n' ->
  alt
    (alt
      (alt
        (alt
          (alt
            (alt
              (alt
                (alt
                  (alt
                    (alt
                      (alt (transform _UU03c3_ (fun x0 -> S_expr_val x0))
                        (and_then (match_token "new") (fun _ ->
                          transform identifier (fun x0 -> S_expr_new x0))))
                      (and_then (match_token "let") (fun _ ->
                        and_then identifier (fun x0 ->
                          and_then (match_token ":=") (fun _ ->
                            and_then (expr n') (fun y0 ->
                              and_then (match_token "in") (fun _ ->
                                transform (expr n') (fun z -> S_expr_let (x0,
                                  y0, z)))))))))
                    (and_then (match_token "if") (fun _ ->
                      and_then (expr n') (fun x0 ->
                        and_then (match_token "then") (fun _ ->
                          and_then (expr n') (fun y0 ->
                            and_then (match_token "else") (fun _ ->
                              transform (expr n') (fun z -> S_expr_if (x0,
                                y0, z)))))))))
                  (transform identifier (fun x0 -> S_expr_var x0)))
                (and_then (match_token "(") (fun _ ->
                  and_then (expr n') (fun x0 ->
                    and_then (match_token "+") (fun _ ->
                      and_then (expr n') (fun y0 ->
                        transform (match_token ")") (fun _ -> S_expr_add (x0,
                          y0))))))))
              (and_then (match_token "(") (fun _ ->
                and_then (expr n') (fun x0 ->
                  and_then (match_token "<") (fun _ ->
                    and_then (expr n') (fun y0 ->
                      transform (match_token ")") (fun _ -> S_expr_lt (x0,
                        y0))))))))
            (and_then (match_token "(") (fun _ ->
              and_then (expr n') (fun x0 ->
                and_then (match_token "=") (fun _ ->
                  and_then (expr n') (fun y0 ->
                    transform (match_token ")") (fun _ -> S_expr_eq (x0, y0))))))))
          (and_then (match_token "(") (fun _ ->
            and_then (expr n') (fun x0 ->
              and_then (match_token "instanceof") (fun _ ->
                and_then identifier (fun y0 ->
                  transform (match_token ")") (fun _ -> S_expr_instanceof
                    (x0, y0))))))))
        (and_then (match_token "(") (fun _ ->
          and_then (expr n') (fun x0 ->
            and_then (match_token ".") (fun _ ->
              and_then identifier (fun y0 ->
                and_then (match_token "[") (fun _ ->
                  and_then (expr n') (fun z ->
                    and_then (match_token "]") (fun _ ->
                      transform (match_token ")") (fun _ -> S_expr_invoke
                        (x0, y0, z)))))))))))
      (and_then (match_token "(") (fun _ ->
        and_then (expr n') (fun x0 ->
          and_then (match_token ".") (fun _ ->
            and_then identifier (fun y0 ->
              and_then (match_token ":=") (fun _ ->
                and_then (expr n') (fun z ->
                  transform (match_token ")") (fun _ -> S_expr_putfield (x0,
                    y0, z))))))))))
    (and_then (match_token "(") (fun _ ->
      and_then (expr n') (fun x0 ->
        and_then (match_token ".") (fun _ ->
          and_then identifier (fun y0 ->
            transform (match_token ")") (fun _ -> S_expr_getfield (x0, y0)))))))

(** val t0 : s_ty parser0 **)

let t0 =
  alt
    (alt (transform (match_token "bool") (fun _ -> S_ty_bool))
      (transform (match_token "int") (fun _ -> S_ty_int)))
    (transform identifier (fun x0 -> S_ty_class x0))

(** val d : s_dc_m parser0 **)

let d =
  and_then t0 (fun type_m ->
    and_then identifier (fun name_m ->
      and_then (match_token "(") (fun _ ->
        and_then t0 (fun type_p ->
          and_then identifier (fun name_p ->
            and_then (match_token ")") (fun _ ->
              and_then (match_token ":=") (fun _ ->
                transform (expr max_expr) (fun body -> S_dc_m_l (type_m,
                  name_m, (S_dc_v_l (type_p, name_p)), body)))))))))

(** val max_fields : nat **)

let max_fields =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S O)))))))))))))))))))))))))))))))))))))))))))))))))

(** val max_methods : nat **)

let max_methods =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S O)))))))))))))))))))))))))))))))))))))))))))))))))

(** val c : s_dc_c parser0 **)

let c =
  and_then (match_token "class") (fun _ ->
    and_then identifier (fun name_c ->
      and_then
        (star_bounded
          (and_then (match_token "extends") (fun _ -> identifier)) (S O))
        (fun name_super ->
        and_then (match_token "{") (fun _ ->
          and_then
            (star_bounded
              (and_then t0 (fun type_fld ->
                and_then identifier (fun name_fld ->
                  transform (match_token ";") (fun _ -> S_dc_v_l (type_fld,
                    name_fld))))) max_fields) (fun flds ->
            and_then
              (star_bounded
                (and_then d (fun meth ->
                  transform (match_token ";") (fun _ -> meth))) max_methods)
              (fun meths ->
              transform (match_token "}") (fun _ -> S_dc_c_l (name_c,
                (String.concat "" name_super), flds, meths))))))))

(** val max_classes : nat **)

let max_classes =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S O)))))))))))))))))))))))))))))))))))))))))))))))))

(** val p : s_prg parser0 **)

let p =
  and_then (star_bounded c max_classes) (fun classes0 ->
    transform (expr max_expr) (fun body -> S_prg_l (classes0, body)))

(** val parse : string -> token list * s_prg optionE **)

let parse s =
  p (tokenize s)

(** val ty_to_dstr : s_ty -> dstring **)

let ty_to_dstr = function
| S_ty_bool -> from_string "bool"
| S_ty_int -> from_string "int"
| S_ty_class c0 -> from_string c0

(** val bool_to_dstr : s_bool -> dstring **)

let bool_to_dstr = function
| S_bool_true -> from_string "true"
| S_bool_false -> from_string "false"

(** val nat_to_digit : nat -> string **)

let nat_to_digit = function
| O -> "0"
| S n2 ->
  (match n2 with
   | O -> "1"
   | S n3 ->
     (match n3 with
      | O -> "2"
      | S n4 ->
        (match n4 with
         | O -> "3"
         | S n5 ->
           (match n5 with
            | O -> "4"
            | S n6 ->
              (match n6 with
               | O -> "5"
               | S n7 ->
                 (match n7 with
                  | O -> "6"
                  | S n8 ->
                    (match n8 with
                     | O -> "7"
                     | S n9 -> (match n9 with
                                | O -> "8"
                                | S _ -> "9"))))))))

(** val nat_to_dstr_aux : nat -> nat -> dstring **)

let rec nat_to_dstr_aux n1 k =
  match n1 with
  | O -> (match k with
          | O -> from_string "0"
          | S _ -> from_string "")
  | S n2 ->
    (match n2 with
     | O ->
       (match k with
        | O -> from_string ""
        | S k' ->
          (match k' with
           | O -> from_string "1"
           | S _ ->
             append
               (nat_to_dstr_aux
                 (div n1 (S (S (S (S (S (S (S (S (S (S O))))))))))) k')
               (from_string
                 (nat_to_digit
                   (Nat.modulo n1 (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
     | S _ ->
       (match k with
        | O -> from_string ""
        | S k' ->
          append
            (nat_to_dstr_aux
              (div n1 (S (S (S (S (S (S (S (S (S (S O))))))))))) k')
            (from_string
              (nat_to_digit
                (Nat.modulo n1 (S (S (S (S (S (S (S (S (S (S O)))))))))))))))

(** val nat_to_dstr : nat -> dstring **)

let nat_to_dstr n1 =
  nat_to_dstr_aux n1 n1

(** val int_to_dstr : s_int -> dstring **)

let int_to_dstr =
  nat_to_dstr

(** val loc_to_dstr : s_loc -> dstring **)

let loc_to_dstr l0 =
  append (from_string "L") (nat_to_dstr l0)

(** val symb_to_dstr : s_symb -> dstring **)

let symb_to_dstr = function
| S_symb_expr n1 -> nat_to_dstr n1
| S_symb_fld (n1, l0) ->
  append (append (nat_to_dstr n1) (from_string "_"))
    (dconcat (from_string "_") (map from_string l0))

(** val prim_c_to_dstr : s_prim_c -> dstring **)

let prim_c_to_dstr = function
| S_prim_c_bool b0 -> bool_to_dstr b0
| S_prim_c_int n1 -> int_to_dstr n1
| S_prim_c_symb s -> append (from_string "X") (symb_to_dstr s)

(** val ref_c_to_dstr : s_ref_c -> dstring **)

let ref_c_to_dstr = function
| S_ref_c_null -> from_string "null"
| S_ref_c_loc l0 -> loc_to_dstr l0
| S_ref_c_symb s -> append (from_string "Y") (symb_to_dstr s)

(** val val_to_dstr : s_val -> dstring **)

let rec val_to_dstr = function
| S_val_unassumed -> from_string "BOT"
| S_val_prim_c p0 -> prim_c_to_dstr p0
| S_val_ref_c u -> ref_c_to_dstr u
| S_val_add (_UU03c3_1, _UU03c3_2) ->
  append
    (append
      (append (append (from_string "(") (val_to_dstr _UU03c3_1))
        (from_string " + ")) (val_to_dstr _UU03c3_2)) (from_string ")")
| S_val_lt (_UU03c3_1, _UU03c3_2) ->
  append
    (append
      (append (append (from_string "(") (val_to_dstr _UU03c3_1))
        (from_string " < ")) (val_to_dstr _UU03c3_2)) (from_string ")")
| S_val_eq (_UU03c3_1, _UU03c3_2) ->
  append
    (append
      (append (append (from_string "(") (val_to_dstr _UU03c3_1))
        (from_string " = ")) (val_to_dstr _UU03c3_2)) (from_string ")")
| S_val_subtype (_UU03c3_1, t1) ->
  append
    (append
      (append (append (from_string "(") (val_to_dstr _UU03c3_1))
        (from_string " <: ")) (ty_to_dstr t1)) (from_string ")")
| S_val_field (s1, fname, s2) ->
  append
    (append
      (append
        (append
          (append (append (from_string "(Y") (symb_to_dstr s1))
            (from_string ".")) (from_string fname)) (from_string " = Z"))
      (symb_to_dstr s2)) (from_string ")")
| S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) ->
  append
    (append
      (append
        (append
          (append (append (from_string "ite(") (val_to_dstr _UU03c3_1))
            (from_string ", ")) (val_to_dstr _UU03c3_2)) (from_string ", "))
      (val_to_dstr _UU03c3_3)) (from_string ")")

(** val expr_to_dstr : s_expr -> dstring **)

let rec expr_to_dstr = function
| S_expr_var x0 -> from_string x0
| S_expr_val _UU03c3_0 -> val_to_dstr _UU03c3_0
| S_expr_new c0 -> append (from_string "new ") (from_string c0)
| S_expr_getfield (e1, fname) ->
  append
    (append
      (append (append (from_string "(") (expr_to_dstr e1)) (from_string "."))
      (from_string fname)) (from_string ")")
| S_expr_putfield (e1, fname, e2) ->
  append
    (append
      (append
        (append
          (append (append (from_string "(") (expr_to_dstr e1))
            (from_string ".")) (from_string fname)) (from_string " := "))
      (expr_to_dstr e2)) (from_string ")")
| S_expr_let (x0, e1, e2) ->
  append
    (append
      (append
        (append (append (from_string "let ") (from_string x0))
          (from_string " := ")) (expr_to_dstr e1)) (from_string " in "))
    (expr_to_dstr e2)
| S_expr_add (e1, e2) ->
  append
    (append
      (append (append (from_string "(") (expr_to_dstr e1))
        (from_string " + ")) (expr_to_dstr e2)) (from_string ")")
| S_expr_lt (e1, e2) ->
  append
    (append
      (append (append (from_string "(") (expr_to_dstr e1))
        (from_string " < ")) (expr_to_dstr e2)) (from_string ")")
| S_expr_eq (e1, e2) ->
  append
    (append
      (append (append (from_string "(") (expr_to_dstr e1))
        (from_string " = ")) (expr_to_dstr e2)) (from_string ")")
| S_expr_instanceof (e1, c0) ->
  append
    (append
      (append (append (from_string "(") (expr_to_dstr e1))
        (from_string " instanceof ")) (from_string c0)) (from_string ")")
| S_expr_if (e1, e2, e3) ->
  append
    (append
      (append
        (append (append (from_string "if ") (expr_to_dstr e1))
          (from_string " then ")) (expr_to_dstr e2)) (from_string " else "))
    (expr_to_dstr e3)
| S_expr_invoke (e1, m, e2) ->
  append
    (append
      (append
        (append
          (append (append (from_string "(") (expr_to_dstr e1))
            (from_string ".")) (from_string m)) (from_string "["))
      (expr_to_dstr e2)) (from_string "])")

(** val dc_v_to_dstr : bool -> s_dc_v -> dstring **)

let dc_v_to_dstr semicolon = function
| S_dc_v_l (t1, x0) ->
  append (append (append (ty_to_dstr t1) (from_string " ")) (from_string x0))
    (from_string (if semicolon then ";" else ""))

(** val dc_m_to_dstr : s_dc_m -> dstring **)

let dc_m_to_dstr = function
| S_dc_m_l (t1, m, v, e) ->
  append
    (append
      (append
        (append
          (append
            (append (append (ty_to_dstr t1) (from_string " "))
              (from_string m)) (from_string "(")) (dc_v_to_dstr false v))
        (from_string ") := ")) (expr_to_dstr e)) (from_string ";")

(** val dc_c_to_dstr : s_dc_c -> dstring **)

let dc_c_to_dstr = function
| S_dc_c_l (c1, csup, fs, ds) ->
  append
    (append
      (append
        (append
          (append
            (append (append (from_string "class ") (from_string c1))
              (from_string (if (=) csup "" then "" else (^) " extends " csup)))
            (from_string " { "))
          (dconcat (from_string " ") (map (dc_v_to_dstr true) fs)))
        (from_string " ")) (dconcat (from_string " ") (map dc_m_to_dstr ds)))
    (from_string "}")

(** val prg_to_dstr : s_prg -> dstring **)

let prg_to_dstr = function
| S_prg_l (cs, e) ->
  append
    (append (dconcat (from_string " ") (map dc_c_to_dstr cs))
      (from_string " ")) (expr_to_dstr e)

(** val object_to_dstr : object0 -> dstring **)

let object_to_dstr =
  let object_to_dstr_aux =
    let rec object_to_dstr_aux = function
    | [] -> from_string ""
    | p0 :: other_elts ->
      let (f, _UU03c3_0) = p0 in
      append
        (append
          (append (append (from_string f) (from_string ":"))
            (val_to_dstr _UU03c3_0)) (from_string ", "))
        (object_to_dstr_aux other_elts)
    in object_to_dstr_aux
  in
  (fun o ->
  append
    (append
      (append (append (from_string "{class ") (from_string (o_class_name o)))
        (from_string ", "))
      (object_to_dstr_aux (MapString.elements (o_memory o))))
    (from_string "}"))

(** val heap_to_dstr : heap -> dstring **)

let heap_to_dstr h =
  append
    (append (from_string "<")
      (dconcat (from_string ", ")
        (map (fun x0 ->
          let (u, o) = x0 in
          append (append (ref_c_to_dstr u) (from_string " -> "))
            (object_to_dstr o)) (MapRefC.elements h)))) (from_string ">")

(** val path_condition_to_dstr : path_condition -> dstring **)

let rec path_condition_to_dstr = function
| [] -> from_string "true"
| c0 :: other__UU03a3_ ->
  (match c0 with
   | Clause_pos _UU03c3_0 ->
     append (append (val_to_dstr _UU03c3_0) (from_string " && "))
       (path_condition_to_dstr other__UU03a3_)
   | Clause_neg _UU03c3_0 ->
     append
       (append (append (from_string "~") (val_to_dstr _UU03c3_0))
         (from_string " && ")) (path_condition_to_dstr other__UU03a3_))

(** val config_to_dstr : config -> dstring **)

let config_to_dstr = function
| (p0, e) ->
  let (p1, _UU03a3_) = p0 in
  let (p2, h) = p1 in
  append
    (append
      (append
        (append
          (append
            (append
              (append (append (from_string "[") (prg_to_dstr p2))
                (from_string ", ")) (heap_to_dstr h)) (from_string ", "))
          (path_condition_to_dstr _UU03a3_)) (from_string ", "))
      (expr_to_dstr e)) (from_string "]")

(** val step_to_dstr : config list -> dstring list **)

let step_to_dstr js =
  map config_to_dstr js

(** val lF : dstring **)

let lF =
  from_string
    ((fun l ->
      let a = Array.of_list l in
      String.init (Array.length a) (fun i -> a.(i)))
      ((ascii_of_nat (S (S (S (S (S (S (S (S (S (S O))))))))))) :: []))

(** val class_sibling_number_aux :
    s_prg -> s_dc_c list -> s_dc_c -> string -> nat -> nat option **)

let rec class_sibling_number_aux p0 cs c0 c_sup n1 =
  match cs with
  | [] -> None
  | c' :: cs' ->
    if (=) (class_name c0) (class_name c')
    then Some n1
    else if (=) c_sup (superclass_name c')
         then class_sibling_number_aux p0 cs' c0 c_sup (Nat.succ n1)
         else class_sibling_number_aux p0 cs' c0 c_sup n1

(** val class_sibling_number : s_prg -> s_dc_c -> nat option **)

let class_sibling_number p0 c0 =
  class_sibling_number_aux p0 (classes p0) c0 (superclass_name c0) O

(** val class_to_list_aux : s_prg -> s_dc_c -> nat -> nat list **)

let rec class_to_list_aux p0 c0 = function
| O -> []
| S depth' ->
  let c_sup = superclass_name c0 in
  if (=) "" c_sup
  then O :: []
  else (match cdecl p0 c_sup with
        | Some c_sup0 ->
          (match class_sibling_number p0 c0 with
           | Some n1 -> app (class_to_list_aux p0 c_sup0 depth') (n1 :: [])
           | None -> [])
        | None -> [])

(** val class_to_list : s_prg -> s_dc_c -> nat list **)

let class_to_list p0 c0 =
  class_to_list_aux p0 c0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val list_nat_to_dsmt : nat list -> dstring **)

let rec list_nat_to_dsmt = function
| [] -> from_string "nil"
| n1 :: ns ->
  append
    (append
      (append (append (from_string "(insert ") (nat_to_dstr n1))
        (from_string " ")) (list_nat_to_dsmt ns)) (from_string ")")

(** val ref_c_to_dsmt : s_ref_c -> dstring **)

let ref_c_to_dsmt = function
| S_ref_c_null -> from_string "_null"
| S_ref_c_loc l0 -> loc_to_dstr l0
| S_ref_c_symb s -> append (from_string "Y") (symb_to_dstr s)

(** val type_to_dsmt : s_ty -> dstring **)

let type_to_dsmt = function
| S_ty_bool -> from_string "Bool"
| S_ty_int -> from_string "Int"
| S_ty_class _ -> from_string "SRef"

(** val field_to_dsmt : s_dc_v -> dstring **)

let field_to_dsmt f =
  append
    (append
      (append
        (append
          (append
            (append
              (append
                (append
                  (append (from_string "(declare-fun ")
                    (from_string (field_name f))) (from_string " (SRef) "))
                (type_to_dsmt (field_type f))) (from_string ")")) lF)
          (from_string
            (if is_type_primitive (field_type f)
             then "(assert (= 0 ("
             else "(assert (= _null ("))) (from_string (field_name f)))
      (from_string " _null)))")) lF

(** val class_to_dsmt : s_prg -> s_dc_c -> dstring **)

let class_to_dsmt p0 c0 =
  append
    (append
      (append
        (append
          (append
            (append (from_string "(define-fun ")
              (from_string (class_name c0))) (from_string " () SCl "))
          (list_nat_to_dsmt (class_to_list p0 c0))) (from_string ")")) lF)
    (dconcat (from_string "") (map field_to_dsmt (fields c0)))

(** val smt_decls : s_prg -> dstring **)

let smt_decls p0 =
  append
    (append
      (append
        (append
          (append
            (append
              (append
                (append
                  (append
                    (append
                      (append
                        (append
                          (from_string
                            "(define-sort SCl () (List Int)) ;the sort of classes")
                          lF)
                        (from_string
                          "(define-fun-rec subclass ((x SCl) (y SCl)) Bool"))
                      lF)
                    (from_string
                      "(ite (= y nil) true (ite (= x nil) false (ite (= (head x) (head y)) (subclass (tail x) (tail y)) false))))"))
                  lF)
                (from_string "(declare-sort SRef) ;the sort of references"))
              lF) (from_string "(declare-fun classOf (SRef) SCl)")) lF)
        (from_string "(declare-fun _null () SRef)")) lF)
    (dconcat (from_string "") (map (class_to_dsmt p0) (classes p0)))

(** val value_to_dsmt : s_val -> dstring **)

let rec value_to_dsmt = function
| S_val_prim_c p0 -> prim_c_to_dstr p0
| S_val_ref_c u -> ref_c_to_dsmt u
| S_val_add (_UU03c3_1, _UU03c3_2) ->
  append
    (append
      (append (append (from_string "(+ ") (value_to_dsmt _UU03c3_1))
        (from_string " ")) (value_to_dsmt _UU03c3_2)) (from_string ")")
| S_val_lt (_UU03c3_1, _UU03c3_2) ->
  append
    (append
      (append (append (from_string "(< ") (value_to_dsmt _UU03c3_1))
        (from_string " ")) (value_to_dsmt _UU03c3_2)) (from_string ")")
| S_val_eq (_UU03c3_1, _UU03c3_2) ->
  append
    (append
      (append (append (from_string "(= ") (value_to_dsmt _UU03c3_1))
        (from_string " ")) (value_to_dsmt _UU03c3_2)) (from_string ")")
| S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) ->
  append
    (append
      (append
        (append
          (append (append (from_string "(ite ") (value_to_dsmt _UU03c3_1))
            (from_string " ")) (value_to_dsmt _UU03c3_2)) (from_string " "))
      (value_to_dsmt _UU03c3_3)) (from_string ")")
| _ -> from_string ""

(** val clause_to_dsmt : s_prg -> s_val -> bool -> dstring **)

let clause_to_dsmt p0 _UU03c3_0 positive0 =
  match _UU03c3_0 with
  | S_val_prim_c p1 -> prim_c_to_dstr p1
  | S_val_ref_c u -> ref_c_to_dsmt u
  | S_val_lt (_UU03c3_1, _UU03c3_2) ->
    append
      (append
        (append
          (append
            (append
              (append
                (append
                  (append (from_string "(assert ")
                    (if positive0 then from_string "" else from_string "(not "))
                  (from_string "(< ")) (value_to_dsmt _UU03c3_1))
              (from_string " ")) (value_to_dsmt _UU03c3_2)) (from_string ")"))
        (if positive0 then from_string "" else from_string ")"))
      (from_string ")")
  | S_val_eq (_UU03c3_1, _UU03c3_2) ->
    append
      (append
        (append
          (append
            (append
              (append
                (append
                  (append (from_string "(assert ")
                    (if positive0 then from_string "" else from_string "(not "))
                  (from_string "(= ")) (value_to_dsmt _UU03c3_1))
              (from_string " ")) (value_to_dsmt _UU03c3_2)) (from_string ")"))
        (if positive0 then from_string "" else from_string ")"))
      (from_string ")")
  | S_val_subtype (_UU03c3_1, t1) ->
    (match t1 with
     | S_ty_class c0 ->
       append
         (append
           (append
             (append
               (append
                 (append
                   (append
                     (append (from_string "(assert ")
                       (if positive0
                        then from_string ""
                        else from_string "(not "))
                     (from_string "(subclass (classOf "))
                   (value_to_dsmt _UU03c3_1)) (from_string ") "))
               (from_string c0)) (from_string ")"))
           (if positive0 then from_string "" else from_string ")"))
         (from_string ")")
     | _ -> from_string "")
  | S_val_field (s1, f, s2) ->
    append
      (append
        (append
          (append
            (append
              (append
                (append
                  (append
                    (append
                      (append (from_string "(assert ")
                        (if positive0
                         then from_string ""
                         else from_string "(not ")) (from_string "(= ("))
                    (from_string f)) (from_string " "))
                (ref_c_to_dsmt (S_ref_c_symb s1))) (from_string ") "))
            (match class_with_field p0 f with
             | Some c0 ->
               (match fdecl c0 f with
                | Some f0 ->
                  let t1 = field_type f0 in
                  if is_type_primitive t1
                  then prim_c_to_dstr (S_prim_c_symb s2)
                  else ref_c_to_dsmt (S_ref_c_symb s2)
                | None -> from_string "")
             | None -> from_string "")) (from_string ")"))
        (if positive0 then from_string "" else from_string ")"))
      (from_string ")")
  | S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) ->
    append
      (append
        (append
          (append
            (append
              (append
                (append
                  (append
                    (append
                      (append (from_string "(assert ")
                        (if positive0
                         then from_string ""
                         else from_string "(not ")) (from_string "(ite "))
                    (value_to_dsmt _UU03c3_1)) (from_string " "))
                (value_to_dsmt _UU03c3_2)) (from_string " "))
            (value_to_dsmt _UU03c3_3)) (from_string ")"))
        (if positive0 then from_string "" else from_string ")"))
      (from_string ")")
  | _ -> from_string ""

(** val clauses_to_dsmt : s_prg -> path_condition -> dstring **)

let rec clauses_to_dsmt p0 = function
| [] -> from_string ""
| cl :: _UU03a3_' ->
  append
    (match cl with
     | Clause_pos _UU03c3_0 -> append (clause_to_dsmt p0 _UU03c3_0 true) lF
     | Clause_neg _UU03c3_0 -> append (clause_to_dsmt p0 _UU03c3_0 false) lF)
    (clauses_to_dsmt p0 _UU03a3_')

(** val add_vars_prim : s_prg -> s_val -> SetSymb.t -> SetSymb.t **)

let rec add_vars_prim p0 _UU03c3_0 ssPrim =
  match _UU03c3_0 with
  | S_val_prim_c p1 ->
    (match p1 with
     | S_prim_c_symb s -> SetSymb.add s ssPrim
     | _ -> ssPrim)
  | S_val_lt (_UU03c3_1, _UU03c3_2) ->
    add_vars_prim p0 _UU03c3_2 (add_vars_prim p0 _UU03c3_1 ssPrim)
  | S_val_eq (_UU03c3_1, _UU03c3_2) ->
    add_vars_prim p0 _UU03c3_2 (add_vars_prim p0 _UU03c3_1 ssPrim)
  | S_val_subtype (_UU03c3_1, _) -> add_vars_prim p0 _UU03c3_1 ssPrim
  | S_val_field (_, f, s2) ->
    (match class_with_field p0 f with
     | Some c0 ->
       (match fdecl c0 f with
        | Some f0 ->
          let t1 = field_type f0 in
          if is_type_primitive t1 then SetSymb.add s2 ssPrim else ssPrim
        | None -> ssPrim)
     | None -> ssPrim)
  | S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) ->
    add_vars_prim p0 _UU03c3_3
      (add_vars_prim p0 _UU03c3_2 (add_vars_prim p0 _UU03c3_1 ssPrim))
  | _ -> ssPrim

(** val add_vars_ref : s_prg -> s_val -> SetSymb.t -> SetSymb.t **)

let rec add_vars_ref p0 _UU03c3_0 ssRef =
  match _UU03c3_0 with
  | S_val_ref_c u ->
    (match u with
     | S_ref_c_symb s -> SetSymb.add s ssRef
     | _ -> ssRef)
  | S_val_lt (_UU03c3_1, _UU03c3_2) ->
    add_vars_ref p0 _UU03c3_2 (add_vars_ref p0 _UU03c3_1 ssRef)
  | S_val_eq (_UU03c3_1, _UU03c3_2) ->
    add_vars_ref p0 _UU03c3_2 (add_vars_ref p0 _UU03c3_1 ssRef)
  | S_val_subtype (_UU03c3_1, _) -> add_vars_ref p0 _UU03c3_1 ssRef
  | S_val_field (s1, f, s2) ->
    (match class_with_field p0 f with
     | Some c0 ->
       (match fdecl c0 f with
        | Some f0 ->
          let t1 = field_type f0 in
          if is_type_primitive t1
          then SetSymb.add s1 ssRef
          else SetSymb.add s2 (SetSymb.add s1 ssRef)
        | None -> SetSymb.add s1 ssRef)
     | None -> SetSymb.add s1 ssRef)
  | S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) ->
    add_vars_ref p0 _UU03c3_3
      (add_vars_ref p0 _UU03c3_2 (add_vars_ref p0 _UU03c3_1 ssRef))
  | _ -> ssRef

(** val declare_vars_clause :
    s_prg -> s_val -> SetSymb.t -> SetSymb.t -> dstring **)

let rec declare_vars_clause p0 _UU03c3_0 ssPrim ssRef =
  match _UU03c3_0 with
  | S_val_prim_c p1 ->
    (match p1 with
     | S_prim_c_symb s ->
       if SetSymb.mem s ssPrim
       then from_string ""
       else append
              (append
                (append (from_string "(declare-fun ")
                  (prim_c_to_dstr (S_prim_c_symb s)))
                (from_string " () Int)")) lF
     | _ -> from_string "")
  | S_val_ref_c u ->
    (match u with
     | S_ref_c_symb s ->
       if SetSymb.mem s ssRef
       then from_string ""
       else append
              (append
                (append (from_string "(declare-fun ")
                  (ref_c_to_dsmt (S_ref_c_symb s))) (from_string " () SRef)"))
              lF
     | _ -> from_string "")
  | S_val_lt (_UU03c3_1, _UU03c3_2) ->
    append (declare_vars_clause p0 _UU03c3_1 ssPrim ssRef)
      (declare_vars_clause p0 _UU03c3_2 (add_vars_prim p0 _UU03c3_1 ssPrim)
        (add_vars_ref p0 _UU03c3_1 ssRef))
  | S_val_eq (_UU03c3_1, _UU03c3_2) ->
    append (declare_vars_clause p0 _UU03c3_1 ssPrim ssRef)
      (declare_vars_clause p0 _UU03c3_2 (add_vars_prim p0 _UU03c3_1 ssPrim)
        (add_vars_ref p0 _UU03c3_1 ssRef))
  | S_val_subtype (_UU03c3_1, _) ->
    declare_vars_clause p0 _UU03c3_1 ssPrim ssRef
  | S_val_field (s1, f, s2) ->
    append
      (if SetSymb.mem s1 ssRef
       then from_string ""
       else append
              (append
                (append (from_string "(declare-fun ")
                  (ref_c_to_dsmt (S_ref_c_symb s1)))
                (from_string " () SRef)")) lF)
      (match class_with_field p0 f with
       | Some c0 ->
         (match fdecl c0 f with
          | Some f0 ->
            let t1 = field_type f0 in
            if is_type_primitive t1
            then if SetSymb.mem s2 ssPrim
                 then from_string ""
                 else append
                        (append
                          (append (from_string "(declare-fun ")
                            (prim_c_to_dstr (S_prim_c_symb s2)))
                          (from_string " () Int)")) lF
            else if SetSymb.mem s2 ssRef
                 then from_string ""
                 else append
                        (append
                          (append (from_string "(declare-fun ")
                            (ref_c_to_dsmt (S_ref_c_symb s2)))
                          (from_string " () SRef)")) lF
          | None -> from_string "")
       | None -> from_string "")
  | S_val_ite (_UU03c3_1, _UU03c3_2, _UU03c3_3) ->
    append
      (append (declare_vars_clause p0 _UU03c3_1 ssPrim ssRef)
        (declare_vars_clause p0 _UU03c3_2 (add_vars_prim p0 _UU03c3_1 ssPrim)
          (add_vars_ref p0 _UU03c3_1 ssRef)))
      (declare_vars_clause p0 _UU03c3_3
        (add_vars_prim p0 _UU03c3_2 (add_vars_prim p0 _UU03c3_1 ssPrim))
        (add_vars_ref p0 _UU03c3_2 (add_vars_ref p0 _UU03c3_1 ssRef)))
  | _ -> from_string ""

(** val declare_vars :
    s_prg -> path_condition -> SetSymb.t -> SetSymb.t -> dstring **)

let rec declare_vars p0 _UU03a3_ ssPrim ssRef =
  match _UU03a3_ with
  | [] -> from_string ""
  | cl :: _UU03a3_' ->
    (match cl with
     | Clause_pos _UU03c3_0 ->
       append (declare_vars_clause p0 _UU03c3_0 ssPrim ssRef)
         (declare_vars p0 _UU03a3_' (add_vars_prim p0 _UU03c3_0 ssPrim)
           (add_vars_ref p0 _UU03c3_0 ssRef))
     | Clause_neg _UU03c3_0 ->
       append (declare_vars_clause p0 _UU03c3_0 ssPrim ssRef)
         (declare_vars p0 _UU03a3_' (add_vars_prim p0 _UU03c3_0 ssPrim)
           (add_vars_ref p0 _UU03c3_0 ssRef)))

(** val path_condition_to_dsmt : s_prg -> path_condition -> dstring **)

let path_condition_to_dsmt p0 _UU03a3_ =
  append (declare_vars p0 _UU03a3_ SetSymb.empty SetSymb.empty)
    (clauses_to_dsmt p0 _UU03a3_)

(** val config_to_dsmt : config -> dstring **)

let config_to_dsmt = function
| (aA, _) ->
  let (bB, _UU03a3_) = aA in
  let (p0, _) = bB in
  append (smt_decls p0) (path_condition_to_dsmt p0 _UU03a3_)

(** val step_to_dsmt : config list -> dstring list **)

let step_to_dsmt js =
  map config_to_dsmt js
