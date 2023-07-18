open Pose

let rec nat_of_int n =
  if n = 0 then O else S (nat_of_int (n - 1))

let read_whole_file filename =
  (* open_in_bin works correctly on Unix and Windows *)
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

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
  | (_, SomeE p) -> let ds = (step_to_dstr (step_at p (nat_of_int n))) in print_dstrings_endline ds
  | _ -> print_endline "parsing error"

let () = print_at 140
