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
