open Errors
open Exceptions
open Io
open Absyn
open Clocks
open Rename
open Flags
open Optimize
open Free_bindings

module StringMap = Map.Make(String)


module type ProgramEnvString = sig
  val str : string
end

module type Main = sig
  val run : unit -> unit
end


module Make (PE: Program_env.ProgramEnvironment) (PES: ProgramEnvString) : Main = struct

  module TypeSystem = Inference.Make(PE)
  module Interpreter = Interpreter.Make(PE)
  module Transpiler = Transpiler.Make(PE)

  let () = Printexc.record_backtrace true
  let nothing a = a

  let run () = 
    try 
      let input = resolve_arguments () in
      let error_printer = create_error_printer input in

      let absyn =
        read_input (resolve_arguments ()) error_printer |>
        rename_tops error_printer |>
        attach_free_bindings |>
        (if flags.optimize then List.map optimize_top else nothing) |>
        TypeSystem.type_tops error_printer |>
        infer_top_clocks error_printer
      in
      if flags.transpile then Printf.sprintf Transpile_template.template PES.str (Transpiler.transpile_tops absyn) |> print_endline
      else (
        if flags.debug then List.iter (fun (t) -> Printf.printf "%s\n" (top_string t)) absyn;
        Printf.printf "Running...\n%!";
        Interpreter.run_program absyn
      )
    with 
    | Failure msg -> Printf.printf "%s\n" msg
    | Problem p -> ()

end
