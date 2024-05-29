open Str
open Flags
open Exceptions

let resolve_input input =
  try (
    let input = Sys.argv.(1) in
    if not (Sys.file_exists input) then (Printf.printf "%s\n" input; failwith "Input file does not exist")
    else if Str.string_match (regexp {|^\(\.\.?\)?\/?\(\([a-zA-Z0-9_-]+\|\(\.\.?\)\)\/\)*[a-zA-Z0-9_-]+\.ar$|}) input 0 then input
    else failwith "Invalid input file extension"
  ) with
  | Invalid_argument _ -> failwith "No file given to compile"
  | ex -> raise ex

let resolve_arguments () : string =
  let arguments = Array.sub Sys.argv 1 ((Array.length Sys.argv) - 1) in
  let (arg_flags,args) = Array.fold_left (fun (flags,acc) arg -> if String.starts_with ~prefix:"-" arg then (arg::flags,acc) else (flags,arg::acc)) ([],[]) arguments in
  let flag_set name = List.mem name arg_flags in
  let args = List.rev args in
  let () = if flag_set "-d" || flag_set "--debug" then flags.debug <- true in
  let () = if flag_set "-o" || flag_set "--optimize" then flags.optimize <- true in
  let () = if flag_set "-t" || flag_set "--transile" then flags.transpile <- true in
  match args with
  | [input] -> resolve_input input
  | _ -> failwith "Wrong number of arguments"

let read_file path =
  let file = open_in path in
  let content = really_input_string (file) (in_channel_length file) in
  let () = close_in_noerr file in
  content

let read_input input error_printer = 
  let lexbuf = (Lexing.from_string (read_file input)) in
  try 
  Parser.main (Lexer.start input) lexbuf
  with
  | _ -> error_printer "Syntax error:" (Some lexbuf.lex_curr_p.pos_lnum) ; raise_problem Parsing

let print_line ls l =
  Printf.printf "%i | %s\n" (l+1) (List.nth ls l)
