
module Arclib = struct
module Absyn = struct
module StringSet = Set.Make(String)

type typ = 
    | T_Poly of string (* alpha *) 
    | T_Unit
    | T_Int
    | T_String
    | T_Multiplicative of typ * typ
    | T_Additive of (string * typ) list
    | T_Function of typ * typ
    | T_Existential of typ
    | T_Universal of typ
    | T_Fix of string * typ
    | T_Boxed of typ
    | T_Named of typ list * string
    | T_Bool
    | T_Signal of typ

and clock_set = CS of {
    channels : StringSet.t;
    variables : StringSet.t
}

and 'a value = Val of 'a * 'a value_inner
and 'a value_inner =
    | Binding of string
    | Unit
    | Int of int
    | Lambda of string * typ option * StringSet.t * 'a term
    | Wait of string (* channel name *)
    | Box of 'a term * StringSet.t
    | Bool of bool
    | String of string
    | Construct of string * 'a term

and 'a term = Term of 'a * 'a term_inner
and 'a term_inner =
    | Value of 'a value
    | Tuple of 'a term * 'a term
    | App of 'a term * 'a term
    | Let of string * typ option * 'a term * 'a term
    | Match of 'a term * 'a alt list
    | Delay of clock_set * StringSet.t * 'a term
    | Adv of 'a term
    | Select of clock_set * clock_set * 'a value * 'a value
    | Unbox of 'a term
    | Fix of string * 'a term
    | Never
    | Read of string (* channel name *)
    | SignalCons of 'a term * 'a term

and 'a top = 
    | TopLet of string * typ option * 'a term
    | TopBind of string * 'a term
    | TypeDef of string * string list * typ (* name, polys, type *)

and channel = channel_type * string * typ (* NOT SURE *)
and channel_type =
    | Push
    | Buffered
    | PushBuffered

and 'a alt = ('a pattern list * 'a term) 
and 'a pattern = 
    | P_Wild
    | P_Any of string * 'a
    | P_Int of int
    | P_Bool of bool
    | P_Tuple of 'a pattern * 'a pattern * 'a
    | P_Cons of 'a pattern * 'a pattern * 'a
    | P_Construct of string * 'a pattern * 'a

let term ln t = Term(ln,t)

let empty_clock_set = CS {
    channels = StringSet.empty;
    variables = StringSet.empty
}

type clock_result =
    | Single of clock_set
    | NoClock
    | MultipleClocks

let is_empty_clock_set clock =
    match clock with
    | NoClock -> true
    | _ -> false

let clock_set_equal (CS cl1) (CS cl2) =
    let channels_equal = StringSet.equal cl1.channels cl2.channels in
    let bindings_equal = StringSet.equal cl1.variables cl2.variables in
    channels_equal && bindings_equal

let clock_set_compatible cl1 cl2 =
    match cl1, cl2 with
    | Single cl1, Single cl2 ->
        if clock_set_equal cl1 cl2 then Single cl1 else MultipleClocks
    | Single cl, NoClock
    | NoClock, Single cl -> Single cl
    | NoClock, NoClock -> NoClock
    | _ -> MultipleClocks

let singleton_channel_clock channel_name =
    let CS empty_clock = empty_clock_set in
    Single (CS { empty_clock with channels = StringSet.singleton channel_name })

let singleton_variable_clock variable =
    let CS empty_clock = empty_clock_set in
    Single (CS { empty_clock with variables = StringSet.singleton variable })

let add_variable_to_clock variable (CS clock) =
    Single (CS { clock with variables = StringSet.add variable clock.variables })

let binds_from_pattern pat =
    let rec aux pat acc = match pat with
    | P_Any(n, a) -> (n, a) :: acc
    | P_Wild 
    | P_Int _ 
    | P_Bool _ -> acc
    | P_Tuple(p0,p1,_)
    | P_Cons(p0,p1,_) -> aux p0 (aux p1 acc)
    | P_Construct(n,p,_) -> aux p acc
    in
    aux pat []

let rec stable_type typ = match typ with
    | T_Unit
    | T_Int
    | T_String
    | T_Bool
    | T_Universal _
    | T_Boxed _ -> true
    | T_Multiplicative(t1,t2) -> stable_type t1 && stable_type t2
    | T_Additive ts -> List.for_all (fun (_,t) -> stable_type t) ts
    | _ -> false

let rec value_type typ = match typ with
    | T_Unit
    | T_Int -> true
    | T_Multiplicative(t1,t2) -> value_type t1 && value_type t2
    | T_Additive ts -> List.for_all (fun (_,t) -> value_type t) ts
    | _ -> false

(*let rec additive_type_string constructs =
    List.map (fun (n,t) -> "| "^n^" of "^type_string t) ts*)

let rec type_string typ = match typ with
    | T_Poly(s) -> "'"^s
    | T_Unit -> "unit"
    | T_Int -> "int"
    | T_Bool -> "bool"
    | T_String -> "string"
    | T_Multiplicative(t1,t2) -> "("^ type_string t1 ^" * "^ type_string t2 ^")"
    | T_Additive ts -> List.map (fun (n,t) -> "| "^n^" of "^type_string t) ts |> String.concat " "
    | T_Function(t1,t2) -> "("^ type_string t1 ^" -> "^ type_string t2 ^")"
    | T_Existential t -> "O(" ^ type_string t ^ ")"
    | T_Universal t -> "(A)" ^ type_string t
    | T_Fix(n,t) -> "Fix "^n^"."^type_string t
    | T_Boxed t -> "[](" ^ type_string t ^ ")"
    | T_Named([],n) -> n
    | T_Named(typs,n) -> "("^(List.map type_string typs |> String.concat ",")^")"^n
    | T_Signal t -> type_string t^" signal"

and term_string (Term(_,t)) = term_inner_string t

and term_inner_string t = match t with
    | Value v -> value_string v
    | Tuple(t1,t2) -> "("^term_string t1^","^term_string t2^")"
    | App(t1,t2) -> "("^term_string t1^") ("^term_string t2^")"
    | Let(name, _,s,body) -> "let " ^ name ^ " = " ^ term_string s ^ " in\n" ^ term_string body
    | Match(t,alts) -> 
        "match "^term_string t^" with\n"^(List.map alt_string alts |> String.concat "\n" )
    | Delay(_, _, t) -> "delay("^term_string t^")"
    | Adv t -> "adv("^term_string t^")"
    | Select(_,_, v1, v2) -> "select "^value_string v1^" "^value_string v2
    | Unbox t -> "unbox("^term_string t^")"
    | Fix(l,t) -> "fix "^l^"."^term_string t
    | Never -> "never"
    | Read c -> "read "^c
    | SignalCons(t0,t1) -> term_string t0^" :: "^term_string t1

and top_string t : string = match t with
    | TopLet(name,_,s) -> "let " ^ name ^ " = " ^ term_string s ^ " \n"
    | TopBind(oc,t) -> oc^" <- "^term_string t
    | TypeDef(n,_,t) -> "type "^n^" = "^type_string t^"\n"

and alt_string (pats,t) = 
    let rec pat_string p = match p with
        | P_Wild -> "_"
        | P_Any(s,_) -> s
        | P_Int i -> string_of_int i
        | P_Bool true -> "true"
        | P_Bool false -> "false"
        | P_Tuple(p1,p2,_) -> "("^pat_string p1^","^pat_string p2^")"
        | P_Cons(p1,p2,_) -> pat_string p1 ^"::"^pat_string p2
        | P_Construct(name,ps,_) -> name^"("^pat_string ps^")"
    in
    "| "^(List.map pat_string pats |> String.concat "| ") ^" -> "^term_string t

and value_string (Val(_,v)) = match v with
    | Binding x -> x
    | Unit -> "()"
    | Int v -> string_of_int v
    | Lambda(arg, t, _, body) -> "\\"^arg^"."^term_string body
    | Wait c -> "wait "^c
    | Box (t, _) -> "box("^ term_string t^")"
    | Bool b ->
        if b
        then "true"
        else "false"
    | String str -> "\""^str^"\""
    | Construct(n,t) -> n^"("^term_string t^")"
end
module Runtime_value = struct
open Absyn

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type clock = C of StringSet.t
type typed_term = (int*typ) term

let empty_clock = C StringSet.empty
let singleton_clock channel_name = C (StringSet.singleton channel_name)
let union_clocks (C c0) (C c1) = C (StringSet.union c0 c1)

type runtime_value =
    | Binding_rv of string
    | Unit_rv
    | Int_rv of int
    | Bool_rv of bool
    | String_rv of string
    | Tuple_rv of runtime_value * runtime_value
    | Closure of string * value_env * typed_term
    | Construct_rv of string * runtime_value
    | Built_in_1 of (runtime_value -> runtime_value)
    | Built_in_2 of (runtime_value -> runtime_value -> runtime_value)
    | Location of int * clock
    | Box of typed_term * value_env
    | Signal_rv of runtime_value * runtime_value
    | Wait_rv
    | Rec of typed_term

and value_env = VE of { vars : runtime_binding StringMap.t }

and runtime_binding = B of {
    value : runtime_value;
    clock : clock;
    top_level : bool
}

let empty_value_env = VE { vars = StringMap.empty }

type delayed = Delayed of {
    value_env : value_env;
    term : typed_term;
    clock : clock
}

let rec runtime_value_string (value : runtime_value) : string =
    match value with
    | Binding_rv name -> name
    | Unit_rv -> "()"
    | Int_rv n -> string_of_int n
    | Bool_rv b -> if b then "true" else "false"
    | String_rv str -> "\""^str^"\""
    | Tuple_rv (v0, v1) -> "(" ^ runtime_value_string v0 ^ ", " ^ runtime_value_string v1 ^ ")"
    | Closure (param_name, VE value_env, term) ->
        let bindings_list = (StringMap.to_list value_env.vars) in
        let env_string = (
            match bindings_list with
            | [] -> ""
            | _ ->
                let env_string = List.fold_left
                    (fun acc (name, B binding) -> acc ^ ", " ^ name ^ " <- " ^ runtime_value_string binding.value)
                    ""
                    (List.tl bindings_list) in
                let (fst_name, B fst_binding) = List.hd bindings_list in
                fst_name ^ " <- " ^ runtime_value_string fst_binding.value ^ env_string) in
        "closure " ^ "[" ^ env_string ^ "]"
    | Construct_rv (name, v) -> name ^ "(" ^ runtime_value_string v ^ ")"
    | Built_in_2 build_in -> "built_in2"
    | Built_in_1 build_in -> "built_in1"
    | Location (location, clock) -> "Loc" ^ string_of_int location
    | Box _ -> "[]"
    | Signal_rv (head, tail) -> runtime_value_string head ^ " :: " ^ runtime_value_string tail
    | Wait_rv -> "wait"
    | Rec term -> "rec"
end
module Program_env = struct
open Absyn
open Runtime_value

module StringMap = Map.Make(String)

type input_channel_info = {
  delay: float option;
  ctyp : channel_type;
  typ : typ;
  handler : (unit -> runtime_value);
  initial_buffer : runtime_value
}

type output_channel_info = {
  typ : typ option;
  handler : (runtime_value -> unit)
}

type channel = 
  | PushChannel of {
    delay: float option;
    typ : typ;
    handler : (unit -> runtime_value);
  }
  | BufferedChannel of {
    delay: float option;
    typ : typ;
    handler : (unit -> runtime_value);
    initial_buffer : runtime_value
  }
  | PushBufferedChannel of {
    delay: float option;
    typ : typ;
    handler : (unit -> runtime_value);
    initial_buffer : runtime_value
  }
  | OutputChannel of output_channel_info

type channel_info =
  | InputChannelInfo of input_channel_info
  | OutputChannelInfo of output_channel_info

let extract_channel_info ic = match ic with
  | PushChannel c -> InputChannelInfo { delay = c.delay; ctyp = Push; typ = c.typ; handler = c.handler; initial_buffer = Unit_rv }
  | BufferedChannel c  -> InputChannelInfo  { delay = c.delay; ctyp = Buffered; typ = c.typ; handler = c.handler; initial_buffer = c.initial_buffer }
  | PushBufferedChannel c -> InputChannelInfo { delay = c.delay; ctyp = PushBuffered; typ = c.typ; handler = c.handler; initial_buffer = c.initial_buffer }
  | OutputChannel c -> OutputChannelInfo c

module type Channels = sig
  val channels : (string * channel) list
end

(*
    A program environment defines the set of input channels available to a program.
    As such, the ProgramEnviroment module type, defines functions for all the queries we might have over the input channels.
*)
module type ProgramEnvironment = sig
  val buffer_values : unit -> runtime_value StringMap.t
  val output_channels : output_channel_info StringMap.t
  val handle_events : unit -> runtime_value StringMap.t
  val start_channels : unit -> Thread.t list
  val is_buffered_channel : string -> bool
  val is_push_channel : string -> bool
  val input_channel_type : string -> typ
  val output_channel_type : string -> typ option
  val buffers : input_channel_info StringMap.t
end

type input_channel_tempate = unit -> unit
(* Inspiration: https://ocaml.github.io/ocamlunix/threads.html *)
type event_record = { lock : Mutex.t; mutable event_list : (string * runtime_value) list; mutable buffers : runtime_value StringMap.t }

module Make (Chans: Channels) : ProgramEnvironment = struct

  let channel_infos = List.map (fun (n,i) -> (n, extract_channel_info i)) Chans.channels 

  let input_channel c = match c with
    | (name, InputChannelInfo i) -> Some(name,i) 
    | (name, c) -> None

  let output_channel c = match c with
  | (name, OutputChannelInfo i) -> Some(name,i)
  | (name, _) -> None

  let input_channels = channel_infos|> List.filter_map input_channel |> StringMap.of_list
  let output_channels = channel_infos |> List.filter_map output_channel |> StringMap.of_list

  let events = { 
    lock = Mutex.create (); 
    event_list = [];
    buffers = StringMap.empty
  }

  let register_event name value : unit =
    Mutex.lock events.lock;
    events.event_list <- (name,value)::(events.event_list);
    Mutex.unlock events.lock; ()

  let update_buffer name value : unit =
    Mutex.lock events.lock;
    events.buffers <- StringMap.add name value events.buffers;
    Mutex.unlock events.lock; ()

  let clear_event_record () = 
    Mutex.lock events.lock;
    events.event_list <- [];
    Mutex.unlock events.lock; ()

  let channel_values () =
      let rec aux () =
          Mutex.lock events.lock;
          let map = List.fold_left (fun acc (channel,v) -> StringMap.add channel v acc) StringMap.empty events.event_list in
          Mutex.unlock events.lock;
          match StringMap.cardinal map with
          | 0 -> aux ()
          | _ -> map in
      aux ()

  let buffer_values () =
      Mutex.lock events.lock;
      let map = events.buffers in
      Mutex.unlock events.lock;
      map

  let buffered_channel_template init delay handle name : input_channel_tempate = 
    let rec aux () =
      if Option.is_some delay then Option.get delay |> Thread.delay;
      let v = handle () in
      update_buffer name v;
      aux ()
    in
    update_buffer name init; (* Add support for customizing initial value *)
    aux

  let push_channel_template delay handle name : input_channel_tempate = 
    let rec aux () = 
      if Option.is_some delay then Option.get delay |> Thread.delay;
      let v = handle () in
      register_event name v;
      aux ()
    in
    aux

  let push_buffered_channel_template init delay handle name : input_channel_tempate =
    let rec aux () =
      if Option.is_some delay then Option.get delay |> Thread.delay;
      let v = handle () in
      register_event name v;
      update_buffer name v;
      aux ()
    in 
    update_buffer name init;
    aux

  let start_input_channel name channel = 
    let template = match channel.ctyp with
      | Push -> push_channel_template
      | Buffered -> buffered_channel_template channel.initial_buffer
      | PushBuffered -> push_buffered_channel_template channel.initial_buffer
    in
    Thread.create (template channel.delay channel.handler name) ()

  let input_channel_type name = match StringMap.find_opt name input_channels with
    | Some c -> c.typ
    | None -> failwith ("No such channel: "^name)

  let output_channel_type name = match StringMap.find_opt name output_channels with
    | Some(c) -> c.typ
    | None -> failwith ("No such channel: "^name)

  let is_push_channel name = match StringMap.find_opt name input_channels with
    | Some ({ ctyp = Push; _})
    | Some ({ ctyp = PushBuffered; _ }) -> true
    | Some _ -> false
    | None -> failwith ("No such channel: "^name)

  let is_buffered_channel name = match StringMap.find_opt name input_channels with
    | Some ({ ctyp = Buffered; _ })
    | Some ({ ctyp = PushBuffered; _ }) -> true
    | Some _ -> false
    | None -> failwith ("No such channel: "^name)

  let handle_events () = 
      (*Printf.fprintf out "time_step %i: \n%!" time;*)
      (*StringMap.iter (fun c v -> Printf.fprintf out "\t%s: %s\n%!" c (runtime_value_string v)) (channel_values ());*)
      let channel_values = channel_values () in
      Mutex.lock events.lock;
      events.event_list <- [];
      Mutex.unlock events.lock;
      channel_values

  let start_channels () =
      StringMap.fold (fun name c acc -> start_input_channel name c :: acc) input_channels []

  let buffers =
      StringMap.filter (fun name info -> is_buffered_channel name) input_channels

end
end
end
module Program_env_impl = struct 
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
  print_endline ("output: " ^ str)

  
let channels = [
    ( "keyboard", PushBufferedChannel { delay = 0.1; typ = T_String; handler = keyboard_handle; initial_buffer = String_rv ""});
    ( "second", PushChannel { delay = 1.0; typ = T_Unit; handler = (fun () -> Unit_rv)});
    ( "minute", PushChannel { delay = 60.0; typ = T_Unit; handler = (fun () -> Unit_rv)});
    ( "system_time", BufferedChannel { delay = 1.0; typ = T_Int; handler = system_time_handle; initial_buffer = (Int_rv 0) });
    ( "console", OutputChannel { typ = None; handler = console_handle});
    ( "console_int", OutputChannel { typ = Some T_Int; handler =  console_handle});
]
 end
module Transpiled = struct open Arclib.Runtime_value
    module StringMap = Map.Make(String)
    module StringSet = Set.Make(String)
    module type Transpiled = sig
        val run : unit -> unit
    end
    module Make (PE : Arclib.Program_env.ProgramEnvironment) : Transpiled = struct
    type 'a signal =
        | Cons of ('a * ((unit -> 'a signal) * StringSet.t))
    type ('a, 'b) selection =
        | Left of 'a * ((unit -> 'b) * StringSet.t)
        | Right of ((unit -> 'a) * StringSet.t) * 'b
        | Both of 'a * 'b
    let never = 
        let rec never' () = (fun a -> never' () a) in
        (never' (), StringSet.empty)
    let outputs = ref StringMap.empty
    let updated_channel_name = ref ""let buffers = ref (PE.buffer_values ())
let keyboard_buffer () = 
	let wrapped_value = StringMap.find "keyboard" !buffers in
	(match wrapped_value with String_rv s -> s)
let system_time_buffer () = 
	let wrapped_value = StringMap.find "system_time" !buffers in
	(match wrapped_value with Int_rv n -> n)
let set_output_channel channel_name (thunk, in_channels) =
	outputs := StringMap.add channel_name (thunk, in_channels) !outputs
let write_channel channel_name value =
	let wrapped_value =
		match channel_name with
		| "console" -> Tuple_rv (Int_rv (fst value), Int_rv (snd value))
		| _ -> failwith ("Invalid channel " ^ channel_name ^ "\"") in
	let channel = StringMap.find channel_name PE.output_channels in
	channel.handler wrapped_value
let keyboard_update = ref ""

let second_update = ref ()
let update_input_channel channel_name value =
            updated_channel_name := channel_name;
            match channel_name with
	| "keyboard" -> keyboard_update := (match value with String_rv s -> s)
	| "second" -> second_update := ()
	| _ -> ()
type ('a) option = | Some of 'a | None of unit
let fst_0 = fun arg_0_1 -> match arg_0_1 with
| (x_2, _) -> x_2
let rec zip_3 = fun x_sig_4 -> fun y_sig_5 -> match x_sig_4 with
| Cons (x_6, xs_7) -> match y_sig_5 with
| Cons (y_8, ys_9) -> Cons ((x_6, y_8), ((fun () -> (match (match StringSet.mem !updated_channel_name ((StringSet.union (StringSet.of_list []) (List.fold_left StringSet.union StringSet.empty [snd xs_7]))), StringSet.mem !updated_channel_name ((StringSet.union (StringSet.of_list []) (List.fold_left StringSet.union StringSet.empty [snd ys_9]))) with
| true, true -> Both (fst (xs_7) (), fst (ys_9) ())
| true, false -> Left (fst (xs_7) (), ys_9)
| false, true -> Right (xs_7, fst (ys_9) ())) with
| Left (xs'_10, ys'_11) -> ( ( zip_3 ) ( xs'_10 ) ) ( Cons (y_8, ys'_11) )
| Right (xs'_12, ys'_13) -> ( ( zip_3 ) ( Cons (x_6, xs'_12) ) ) ( ys'_13 )
| Both (xs'_14, ys'_15) -> ( ( zip_3 ) ( xs'_14 ) ) ( ys'_15 ))), (StringSet.union (StringSet.of_list []) (List.fold_left StringSet.union StringSet.empty [snd xs_7; snd ys_9]))))
let rec key_handel_16 = ((fun () -> (Cons (Some (fst (((fun () -> !keyboard_update), StringSet.singleton "keyboard")) ()), key_handel_16))), (StringSet.union (StringSet.of_list ["keyboard"]) (List.fold_left StringSet.union StringSet.empty [])))
let rec program_time_17 = let x_18 = ((fun () -> !second_update), StringSet.singleton "second") in
((fun () -> (Cons (( fst_0 ) ( (system_time_buffer (), fst (x_18) ()) ), program_time_17))), (StringSet.union (StringSet.of_list []) (List.fold_left StringSet.union StringSet.empty [snd x_18])))
let rec second_int_sig_19 = fun i_20 -> ((fun () -> (let second_21 = fst (((fun () -> !second_update), StringSet.singleton "second")) () in
Cons (i_20, ( second_int_sig_19 ) ( ( ( + ) ( i_20 ) ) ( 1 ) )))), (StringSet.union (StringSet.of_list ["second"]) (List.fold_left StringSet.union StringSet.empty [])))
let second_int_22 = fun i_23 -> Cons (i_23, ( second_int_sig_19 ) ( ( ( + ) ( i_23 ) ) ( 1 ) ))
let () =
	match ( ( zip_3 ) ( ( second_int_22 ) ( 1 ) ) ) ( Cons (0, program_time_17) ) with
	| Cons (head, tail) ->
	write_channel "console" head;
	set_output_channel "console" tail

    let rec loop () =
        let channel_values = PE.handle_events () in
            buffers := PE.buffer_values ();
            StringMap.iter (fun channel_name value ->
                update_input_channel channel_name value;
                StringMap.iter (fun out_channel (thunk, in_channels) ->
                    if StringSet.mem channel_name in_channels then
                        match thunk () with
                        | Cons (head, tail) ->
                            write_channel out_channel head;
                            set_output_channel out_channel tail
                    else ()) !outputs) channel_values;
            loop ()
    let run () = 
        let _ = PE.start_channels () in loop ()
    end
     end
module PE = Arclib.Program_env.Make(Program_env_impl)
module Program = Transpiled.Make(PE)
let _ = Program.run ()
(*
compile using:
    'ocamlc unix.cma -thread threads.cma <file>' 
    or
    'ocamlopt unix.cmxa -thread threads.cmxa <file>' 
*)

