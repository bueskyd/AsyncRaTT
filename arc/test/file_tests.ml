
open Arclib.Exceptions
open Arclib.Rename
open Arclib.Clocks
open Arclib.Optimize

module ProgramEnv = Arclib.Program_env.Make(Example.Simulator)
module TypeSystem = Arclib.Inference.Make(ProgramEnv)
module Interpreter = Arclib.Interpreter.Make(ProgramEnv)


let success msg = Printf.printf "OK: %s\n" msg
let failure msg = Printf.printf "!!: %s\n" msg

let read_file path =
  let file = open_in path in
  let content = really_input_string (file) (in_channel_length file) in
  let () = close_in_noerr file in
  content

let read_input input = 
  try 
    Ok(Arclib.Parser.main (Arclib.Lexer.start input) (Lexing.from_string (read_file input)))
  with
  | _ -> Error () 

let run_file_test file test =
  match read_input file with
  | Error () -> failure ("Parsing "^file^" failed, skipping test")
  | Ok(tops) -> test tops

let error_void = (fun _ _ -> ())

let expected_problem_type name = 
  let last_slash = String.rindex name '/' + 1 in
  let case = String.sub name (last_slash) (String.length name - last_slash) in
  match String.get case 0 with
  | 't' | 'T' -> Typing
  | 'c' | 'C' -> Clocking
  | 'p' | 'P' -> Parsing
  | 'i' | 'I' -> Interpretation
  | 's' | 'S' -> Stability
  | 'o' | 'O' -> Other
  | _ -> failwith ("Unknown failing test prefix: " ^ case)


let failing_file_typing_test file = 
  let expected_problem = expected_problem_type file in
  let test = fun tops -> (
    let res = try 
      tops |>
      rename_tops error_void |>
      List.map optimize_top |>
      TypeSystem.type_tops error_void |> 
      infer_top_clocks error_void |> ignore ; Error None
    with
    | Problem p ->
      if p = expected_problem then Ok ""
      else Error(Some ("Incorrect failure, expected: "^problem_string expected_problem^" got: "^problem_string p))
    | Failure msg -> Error(Some (msg))
    | _ -> Error(Some("Unknown failure"))
    in match res with
    | Ok msg -> success ("Typing "^file^" failed as expected")
    | Error Some msg -> failure ("Typing "^file^" did not fail as expected, with message: \""^msg^"\"")
    | Error None -> failure ("Typing "^file^" did not fail as expected")
  ) 
  in
  run_file_test file test

let succeding_file_typing_test file =
  let test = fun tops -> (
    let res = try 
      tops |>
      rename_tops error_void |>
      List.map optimize_top |>
      TypeSystem.type_tops error_void |> 
      infer_top_clocks error_void |> ignore ; Ok ()
    with
    | Problem p -> Error ("Got problem: "^problem_string p)
    | Failure msg -> Error msg
    in match res with
    | Ok _ -> success ("Typing "^file^" succeded as expected")
    | Error msg -> failure ("Typing "^file^" failed unexpectedly, with message: \""^msg^"\"")
  ) 
  in
  run_file_test file test