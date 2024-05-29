let str : string = "
open Arclib.Absyn
open Arclib.Runtime_value
open Arclib.Program_env

let program_start_epoch = Unix.time () |> int_of_float

(* https://stackoverflow.com/a/13410456 *)
let get1char () =
  let termio = Unix.tcgetattr Unix.stdin in
  let () =
      Unix.tcsetattr Unix.stdin Unix.TCSADRAIN
          { termio with Unix.c_icanon = false } in
  let res = input_char stdin in
  Unix.tcsetattr Unix.stdin Unix.TCSADRAIN termio;
  res  

let keyboard_handle () =
  let c = get1char () in
  String_rv (Char.escaped c)

let system_time_handle () =
  let now = Unix.time () |> int_of_float in
  Int_rv (now - program_start_epoch)

let console_handle v =
  let str = runtime_value_string v in
  print_endline (\"output: \" ^ str)

  
let channels = [
    ( \"keyboard\", PushBufferedChannel { delay = 0.1; typ = T_String; handler = keyboard_handle; initial_buffer = String_rv \"\"});
    ( \"second\", PushChannel { delay = 1.0; typ = T_Unit; handler = (fun () -> Unit_rv)});
    ( \"minute\", PushChannel { delay = 60.0; typ = T_Unit; handler = (fun () -> Unit_rv)});
    ( \"system_time\", BufferedChannel { delay = 1.0; typ = T_Int; handler = system_time_handle; initial_buffer = (Int_rv 0) });
    ( \"console\", OutputChannel { typ = None; handler = console_handle});
    ( \"console_int\", OutputChannel { typ = Some T_Int; handler =  console_handle});
]
"
