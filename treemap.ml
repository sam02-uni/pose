open Pose

let rec nat_of_int n =
  if n = 0 then O else S (nat_of_int (n - 1))

let read_whole_file filename =
  (* open_in_bin works correctly on Unix and Windows *)
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

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

let src_treemap = read_whole_file "./treemap.txt"

let count_at n =
  match (parse src_treemap) with
  | (_, SomeE p) -> print_endline (string_of_int (List.length (step_at p (nat_of_int n))))
  | _ -> print_endline "parsing error"

let print_at n =
match (parse src_treemap) with
  | (_, SomeE p) -> let ds = (step_to_dsmt (step_at p (nat_of_int n))) in print_dstrings_endline ds
  | _ -> print_endline "parsing error"

let save_to_file dsmt = write_whole_file "in.smt" dsmt

let run_z3 () = let _ = Sys.command "/usr/local/bin/z3 -smt2 in.smt >out.txt" in ()

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

let run_it p n  =
  let j0 = config_initial p in
  let js = ref [j0] in
  let width = ref (length !js) in
  for depth = 1 to n do
    js := List.concat (map step_c !js) ;
    if !width < length !js then
      js := (filter_configs !js) ;
    width := length !js
  done ;
  print_dstrings_endline (step_to_dstr !js)

let print_at2 n =
match (parse src_treemap) with
  | (_, SomeE p) -> run_it p n
  | _ -> print_endline "parsing error"

let () = print_at2 150
