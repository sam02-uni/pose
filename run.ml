open Pose

let filename_src = ref ""
let z3 = ref "/usr/local/bin/z3"
let z3_time = ref 0.0
let z3_queries = ref 0

let rec nat_of_int n =
  if n = 0 then O else S (nat_of_int (n - 1))

let read_whole_file filename =
  (* open_in_bin works correctly on Unix and Windows *)
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let src () = read_whole_file !filename_src

let rec output_dstring ch ds =
  match ds with
  | [] -> output_string ch ""
  | s :: ds2 -> let _ = output_string ch s in
                output_dstring ch ds2

let write_whole_file filename ds =
  (* open_out_bin works correctly on Unix and Windows (???) *)
  let ch = open_out_bin filename in
  output_dstring ch ds;
  output_string ch "(check-sat)\n";
  close_out ch

let rec print_dstring_endline ds =
  match ds with
  | [] -> print_endline ""
  | s :: ds2 -> let _ = print_string s in
                print_dstring_endline ds2

let print_dstrings_endline dss =
  let _ = map (fun ds -> let _ = print_dstring_endline ds in print_endline "\n=========\n") dss in ()

let print_stats () = print_endline ("Spent " ^ (string_of_float !z3_time) ^ " seconds in " ^ (string_of_int !z3_queries) ^ " Z3 queries")

let configs_at n =
match (parse (src ())) with
  | (_, SomeE p) -> print_dstrings_endline (step_to_dstr (step_at p (nat_of_int n)))
  | _ -> print_endline "parsing error"

let count_at n =
  match (parse (src ())) with
  | (_, SomeE p) -> print_endline (string_of_int (List.length (step_at p (nat_of_int n))))
  | _ -> print_endline "parsing error"

let smt_at n =
match (parse (src ())) with
  | (_, SomeE p) -> print_dstrings_endline (step_to_dsmt (step_at p (nat_of_int n)))
  | _ -> print_endline "parsing error"

let stats_at n =
match (parse (src ())) with
  | (_, SomeE p) -> let _ = step_at p (nat_of_int n) in print_stats ()
  | _ -> print_endline "parsing error"

(* Returns the leaves gathered up to depth n. *)
let rec leaves_at p n =
  if n = 0 then [] else
  let ls = leaves_at p (n - 1) in
  let js = step_at p (nat_of_int n) in
  let lsNew = filter (fun j -> is_leaf j) js in
  ls @ lsNew

let lconfigs_at n =
match (parse (src ())) with
  | (_, SomeE p) -> print_dstrings_endline (step_to_dstr (leaves_at p n))
  | _ -> print_endline "parsing error"

let lcount_at n =
  match (parse (src ())) with
  | (_, SomeE p) -> print_endline (string_of_int (List.length (leaves_at p n)))
  | _ -> print_endline "parsing error"

let lsmt_at n =
match (parse (src ())) with
  | (_, SomeE p) -> print_dstrings_endline (step_to_dsmt (leaves_at p n))
  | _ -> print_endline "parsing error"

let lstats_at n =
match (parse (src ())) with
  | (_, SomeE p) -> let _ = leaves_at p n in print_stats ()
  | _ -> print_endline "parsing error"

(*** Pruning with Z3 ***)

let save_to_file dsmt = write_whole_file "in.smt" dsmt

let run_z3 () = let t = Sys.time() in let _ = Sys.command (!z3 ^ " -smt2 in.smt >out.txt") in let _ = (z3_time := !z3_time +. (Sys.time() -. t) ; z3_queries := !z3_queries + 1) in ()

let read_result () =
  let s = read_whole_file "out.txt" in
  ((String.sub s 0 3) = "uns")

let rec filter_configs jss =
  match jss with
  | [] -> []
  | j :: jss' ->
    let dsmt = config_to_dsmt j in
    (save_to_file dsmt ;
    run_z3 () ;
    let unsat = read_result () in
    if unsat then filter_configs jss'
    else j :: (filter_configs jss'))

let step_at_prune p n  =
  let j0 = config_initial p in
  let js = ref [j0] in
  let width = ref (length !js) in
  for depth = 1 to n do
    js := List.concat (map step_c !js) ;
    if !width < length !js then
      js := (filter_configs !js) ;
    width := length !js
  done ;
  !js

(* Returns the final configurations at depth n. Performs
   pruning with Z3. *)
let configs_at_prune n =
match (parse (src ())) with
  | (_, SomeE p) -> print_dstrings_endline (step_to_dstr (step_at_prune p n))
  | _ -> print_endline "parsing error"

(* Returns the SMTLIB of the path condition of the final
   configurations at depth n. Performs pruning with Z3. *)
let smt_at_prune n =
match (parse (src ())) with
  | (_, SomeE p) -> print_dstrings_endline (step_to_dsmt (step_at_prune p n))
  | _ -> print_endline "parsing error"

(* Returns the number of final configurations at depth n.
   Performs pruning with Z3. *)
let count_at_prune n =
match (parse (src ())) with
  | (_, SomeE p) -> print_endline (string_of_int (List.length (step_at_prune p n)))
  | _ -> print_endline "parsing error"

let stats_at_prune n =
match (parse (src ())) with
  | (_, SomeE p) -> let _ = step_at_prune p n in print_stats ()
  | _ -> print_endline "parsing error"

(* Returns the leaves gathered up to depth n. Performs
   pruning with Z3. *)
let leaves_at_prune p n  =
  let j0 = config_initial p in
  let js = ref [j0] in
  let ls = ref [] in
  let width = ref (length !js) in
  for depth = 1 to n do
    let nx = (map step_c !js) in
    let lsNew = List.filteri (fun i _ -> (List.length (List.nth nx i)) = 0) !js in 
    js := List.concat nx;
    if !width < length !js then
      js := (filter_configs !js) ;
    width := length !js ;
    ls := !ls @ lsNew
  done ;
  !ls

(* Returns the final configurations at depth n. Performs
   pruning with Z3. *)
let lconfigs_at_prune n =
match (parse (src ())) with
  | (_, SomeE p) -> print_dstrings_endline (step_to_dstr (leaves_at_prune p n))
  | _ -> print_endline "parsing error"

(* Returns the SMTLIB of the path condition of the final
   configurations at depth n. Performs pruning with Z3. *)
let lsmt_at_prune n =
match (parse (src ())) with
  | (_, SomeE p) -> print_dstrings_endline (step_to_dsmt (leaves_at_prune p n))
  | _ -> print_endline "parsing error"

(* Returns the number of final configurations at depth n.
   Performs pruning with Z3. *)
let lcount_at_prune n =
match (parse (src ())) with
  | (_, SomeE p) -> print_endline (string_of_int (List.length (leaves_at_prune p n)))
  | _ -> print_endline "parsing error"

let lstats_at_prune n =
match (parse (src ())) with
  | (_, SomeE p) -> let _ = leaves_at_prune p n in print_stats ()
  | _ -> print_endline "parsing error"

(*** Entry point ***)

type t_to_print =
| Configs
| Count
| Smt
| Stats

let () =
  let depth = ref 0 in
  let prune = ref false in
  let leaves = ref false in
  let to_print = ref Configs in
  let next_z3 = ref false in
  let next_depth = ref false in
  let help = ref false in
  
  for i = 1 to Array.length Sys.argv - 1 do
    if !next_z3 then 
      (z3 := Sys.argv.(i);
      next_z3 := false)
    else if !next_depth then
      (depth := int_of_string Sys.argv.(i);
      next_depth := false)
    else if Sys.argv.(i) = "-z3" then
      next_z3 := true
    else if Sys.argv.(i) = "-c" then
      to_print := Count
    else if Sys.argv.(i) = "-s" then
      to_print := Smt
    else if Sys.argv.(i) = "-t" then
      to_print := Stats
    else if Sys.argv.(i) = "-p" then
      prune := true
    else if Sys.argv.(i) = "-l" then
      leaves := true
    else if Sys.argv.(i) = "-h" then
      help := true
    else
      (filename_src := Sys.argv.(i);
      next_depth := true)
  done;
  if !help then
    (print_endline ("Usage: " ^ Sys.argv.(0) ^ " [-c|-s] [-l] [-p] [-z <z3_path>] source depth");
    print_endline "  -c: prints count of configs";
    print_endline "  -s: prints smtlib of path condition";
    print_endline "  -t: prints time statistics of Z3 queries";
    print_endline "  -l: considers leaves instead of configs at depth";
    print_endline "  -p: prunes infeasible with Z3";
    print_endline "  -z <z3_path>: specifies the path of the Z3 executable (default: /usr/local/bin/z3)")
  else if !leaves then
  match !to_print with
  | Configs -> if !prune then (lconfigs_at_prune !depth) else (lconfigs_at !depth)
  | Count -> if !prune then (lcount_at_prune !depth) else (lcount_at !depth)
  | Smt -> if !prune then (lsmt_at_prune !depth) else (lsmt_at !depth)
  | Stats -> if !prune then (lstats_at_prune !depth) else (lstats_at !depth)
  else
  match !to_print with
  | Configs -> if !prune then (configs_at_prune !depth) else (configs_at !depth)
  | Count -> if !prune then (count_at_prune !depth) else (count_at !depth)
  | Smt -> if !prune then (smt_at_prune !depth) else (smt_at !depth)
  | Stats -> if !prune then (stats_at_prune !depth) else (stats_at !depth)
