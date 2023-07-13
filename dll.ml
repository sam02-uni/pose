open Pose

let rec nat_of_int n =
  if n = 0 then O else S (nat_of_int (n - 1))

let src_dll = 
  "class Object { } class Void extends Object { } class Entry extends Object { Object element; Entry next; Entry previous; } class AddParameters extends Object { int index; Object elem; } class AddBeforeParameters extends Object { Object o; Entry e; } class DllEntryLoopFrame extends Object {  Entry entry; int i; int idx; } class DoubleLinkedList extends Object { Entry header; int size; Void add(AddParameters pAdd) := let pAddBefore := new AddBeforeParameters in let foo1 := (pAddBefore.o := (pAdd.elem)) in let foo2 := if ((pAdd.index) = (this.size)) then (pAddBefore.e := (this.header)) else (pAddBefore.e := (this.entry[(pAdd.index)])) in let foo3 := (this.addBefore[pAddBefore]) in new Void; Entry entry(int index) := let f := new DllEntryLoopFrame in let foo1 := (f.entry := (this.header)) in let foo2 := (f.i := 0) in let foo3 := (f.idx := index) in let fPost := (this.doEntryLoop[f]) in (fPost.entry); DllEntryLoopFrame doEntryLoop(DllEntryLoopFrame f) := if ((f.idx) < (f.i)) then f else if ((f.entry) = null) then f else let foo1 := (f.entry := ((f.entry).next)) in let foo2 := (f.i := ((f.i) + 1)) in (this.doEntryLoop[f]); Entry addBefore(AddBeforeParameters pAddBefore) := let newEntry := new Entry in let foo1 := (newEntry.element := (pAddBefore.o)) in let foo2 := (newEntry.next := (pAddBefore.e)) in let foo3 := (newEntry.previous := ((pAddBefore.e).previous)) in let foo4 := ((newEntry.previous).next := newEntry) in let foo5 := ((newEntry.next).previous := newEntry) in let foo6 := (this.size := ((this.size) + 1)) in newEntry; } let l := Y0 in let o := Y1 in let p := new AddParameters in let foo1 := (p.index := 2) in let foo2 := (p.elem := o) in (l.add[p])"

(* with index = 1: 95 steps
 * with index = 2: 111 steps
 * with index = 3: 127 steps
 * with index = 4: 143 steps
 *)

let print_at n =
  match (parse src_dll) with
  | (_, SomeE p) -> print_endline (fold_right (^) "" (step_to_str (step_at p (nat_of_int n))))
  | _ -> () ;;

let () = print_at 111
