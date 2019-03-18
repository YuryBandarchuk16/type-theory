open Tree;;
open Buffer;;
open Printf;;

let (>>) x f = f x;;

let string_of_tree tree =
  let buf = create 2048 in
  let rec helper t = match t with
  | Var(v) -> add_string buf v; ()
  | Appl(left, right) -> add_char buf '('; helper left; add_char buf ' '; helper right; add_char buf ')'; ()
  | Abst(v, rest) -> add_string buf ("(\\" ^ v ^ "."); helper rest; add_char buf ')'; ()
  in helper tree;
  contents buf;;

let ic = stdin;;
let oc = stdout;;

let read_all_input () = begin
  let lines = ref [] in
  let match1 = (Str.regexp "(") in
  let replace1 = " ( " in
  let match2 = (Str.regexp ")") in
  let replace2 = " ) " in
  let match3 = (Str.regexp "\\\\") in
  let replace3 = " \\\\" in
  let helper () =
    try
      while true; do
        let line = (ic >> input_line) in
        let line1 = Str.global_replace match1 replace1 line in
        let line2 = Str.global_replace match2 replace2 line1 in
        let line3 = Str.global_replace match3 replace3 line2 in
        let line4 = String.trim line3 in
        lines := line4 :: !lines
        done; List.rev !lines
      with End_of_file -> List.rev !lines in
  let buf = create 2048 in
  let rec concatenate items = match items with
  | x::xs -> add_string buf x; add_string buf "\n"; concatenate xs
  | [] -> contents buf in
  concatenate (helper());
end;;

let all_input = String.trim (read_all_input());;
all_input >> Lexing.from_string >> Parser.main Lexer.main >> string_of_tree >> fprintf oc "%s\n";;
