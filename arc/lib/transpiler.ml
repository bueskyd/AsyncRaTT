open Absyn
open Program_env

module StringMap = Map.Make(String)

module type Transpiler = sig
    val transpile_tops : ('a * typ) top list -> string
end

module Make (PE : Program_env.ProgramEnvironment) : Transpiler = struct

let rec transpile_pattern pattern =
    match pattern with
    | P_Wild -> "_"
    | P_Any (binding_name, _) -> binding_name
    | P_Int n -> string_of_int n
    | P_Bool b -> string_of_bool b
    | P_Tuple (p0, p1, _) ->
        "(" ^ transpile_pattern p0 ^ ", " ^ transpile_pattern p1 ^ ")"
    | P_Cons (p0, p1, _) ->
        "Cons (" ^ transpile_pattern p0 ^ ", " ^ transpile_pattern p1 ^ ")"
    | P_Construct (name, p, _) ->
        name ^ " " ^ transpile_pattern p

let determine_clock (CS clock_set) =
    let channels =
        StringSet.to_list clock_set.channels
        |> List.map (fun channel -> "\"" ^ channel ^ "\"")
        |> String.concat "; " in
    let binding_clocks =
        StringSet.to_list clock_set.variables
        |> List.map (fun binding -> "snd " ^ binding)
        |> String.concat "; " in
    let binding_channels = "List.fold_left StringSet.union StringSet.empty [" ^ binding_clocks ^ "]" in
    "(StringSet.union (StringSet.of_list [" ^ channels ^ "]) (" ^ binding_channels ^ "))"

let get_updated_value channel_name = channel_name ^ "_update"

let rec_or_empty term =
    let Term (_, term) = term in
    match term with
    | Fix _ -> "rec "
    | _ -> ""

let rec transpile_term term =
    let Term (_, term) = term in
    match term with
    | Value value -> transpile_value value
    | Tuple (t0, t1) -> "(" ^ transpile_term t0 ^ ", " ^ transpile_term t1 ^ ")"
    | App (t0, t1) -> "( " ^ transpile_term t0 ^ " ) ( " ^ transpile_term t1 ^ " )"
    | Let (binding_name, _, binding_term, in_term) ->
        "let " ^ rec_or_empty binding_term ^ binding_name ^ " = " ^ transpile_term binding_term ^ " in\n" ^
        transpile_term in_term
    | Match (matched_term, alts) ->
        "match " ^ transpile_term matched_term ^ " with\n" ^
        (List.map (fun (patterns, case_term) ->
            "| " ^ (List.map transpile_pattern patterns |> String.concat "|") ^ " -> " ^ transpile_term case_term)
            alts
        |> String.concat "\n")
    | Delay (clock_set, _, term) ->
        let first = "(fun () -> (" ^ transpile_term term ^ "))" in
        let second = determine_clock clock_set in
        "(" ^ first ^ ", " ^ second ^ ")"
    | Adv term ->
        "fst (" ^ transpile_term term ^ ") ()"
    | Select (cl0, cl1, v0, v1) ->
        let first_clock = "(" ^ determine_clock cl0 ^ ")" in
        let second_clock = "(" ^ determine_clock cl1 ^ ")" in
        let in_first_clock = "StringSet.mem !updated_channel_name " ^ first_clock in
        let in_second_clock = "StringSet.mem !updated_channel_name " ^ second_clock in
        "(match " ^ in_first_clock ^ ", " ^ in_second_clock ^ " with\n" ^
        "| true, true -> Both (fst (" ^ transpile_value v0 ^ ") (), fst (" ^ transpile_value v1 ^ ") ())\n" ^
        "| true, false -> Left (fst (" ^ transpile_value v0 ^ ") (), " ^ transpile_value v1 ^ ")\n" ^
        "| false, true -> Right (" ^ transpile_value v0 ^ ", fst (" ^ transpile_value v1 ^ ") ()))"
    | Unbox term -> "(" ^ transpile_term term ^ ") ()"
    | Fix (_, term) -> transpile_term term
    | Never -> "never"
    | Read channel_name -> channel_name ^ "_buffer ()"
    | SignalCons (t0, t1) -> "Cons (" ^ transpile_term t0 ^ ", " ^ transpile_term t1 ^ ")"

and transpile_value value =
    let Val (_, value) = value in
    match value with
    | Binding name -> name
    | Unit -> "()"
    | Int n -> string_of_int n
    | Lambda (param_name, _, _, term) -> "fun " ^ param_name ^ " -> " ^ transpile_term term
    | Wait channel_name ->
        "((fun () -> !" ^ get_updated_value channel_name ^ "), StringSet.singleton \"" ^ channel_name^ "\")"
    | Box (term, _) -> "(fun () -> " ^ transpile_term term ^ ")"
    | Bool b -> string_of_bool b
    | String str -> "\"" ^ str ^ "\""
    | Construct (name, term) -> name ^ " (" ^ transpile_term term ^ ")"

let rec get_advanced_channels_term term acc =
    let Term ((_, typ), term) = term in
    match term with
    | Value value -> get_advanced_channels_value value acc
    | Tuple (t0, t1) ->
        get_advanced_channels_term t0 acc |> get_advanced_channels_term t1
    | App (t0, t1) ->
        get_advanced_channels_term t0 acc |> get_advanced_channels_term t1
    | Let (_, _, let_term, in_term) ->
        get_advanced_channels_term let_term acc |> get_advanced_channels_term in_term
    | Match (matched_term, alts) ->
        let acc' = get_advanced_channels_term matched_term acc in
        List.fold_left
            (fun acc (_, term) -> get_advanced_channels_term term acc)
            acc' alts
    | Delay (_, _, term) -> get_advanced_channels_term term acc
    | Adv (Term (_, Value (Val (_, Wait channel_name)))) ->
        StringMap.add channel_name typ acc
    | Adv term -> get_advanced_channels_term term acc
    | Select (_, _, v0, v1) ->
        get_advanced_channels_value v0 acc |> get_advanced_channels_value v1
    | Unbox term -> get_advanced_channels_term term acc
    | Fix (_, term) -> get_advanced_channels_term term acc
    | Never -> acc
    | Read _ -> acc
    | SignalCons (t0, t1) ->
        get_advanced_channels_term t0 acc |> get_advanced_channels_term t1

and get_advanced_channels_value value acc =
    let Val (_, value) = value in
    match value with
    | Binding _
    | Unit
    | Int _
    | Wait _
    | Bool _
    | String _ -> acc
    | Lambda (_, _, _, term)
    | Box (term, _)
    | Construct (_, term) -> get_advanced_channels_term term acc

let get_advanced_channels_tops absyn =
    let rec aux absyn acc =
        match absyn with
        | [] -> acc
        | top :: tops -> (
            match top with
            | TopLet (_, _, term)
            | TopBind (_, term) ->
                get_advanced_channels_term term acc |> aux tops
            | TypeDef _ -> aux tops acc) in
    aux absyn StringMap.empty

let transpile_tops absyn =
    let rec type_to_constructor typ binding_name =
        match typ with
        | T_Unit -> "Unit_rv"
        | T_Int -> "Int_rv " ^ binding_name
        | T_String -> "String_rv " ^ binding_name
        | T_Multiplicative (t0, t1) ->
            let v0 = "(fst " ^ binding_name ^ ")" in
            let v1 = "(snd " ^ binding_name ^ ")" in
            "Tuple_rv (" ^ type_to_constructor t0 v0 ^ ", " ^ type_to_constructor t1 v1 ^ ")"
        | T_Additive _ -> ""
        | T_Function _ -> ""
        | T_Bool -> "Bool_rv " ^ binding_name
        | _ -> failwith (type_string typ ^ " not allowed") in

    let signal_type_to_constructor typ binding_name =
        match typ with
        | T_Signal typ' -> type_to_constructor typ' binding_name
        | _ -> failwith ("Invalid type " ^ type_string typ) in

    let type_to_constructor_pattern typ value =
        match typ with
        | T_Unit -> "Unit_rv"
        | T_Int -> "Int_rv " ^ value
        | T_String -> "String_rv " ^ value
        | T_Multiplicative _ -> ""
        | T_Additive _ -> ""
        | T_Function _ -> ""
        | T_Bool -> "Bool_rv " ^ value
        | _ -> failwith (type_string typ ^ " not allowed") in

    let unwrap_value typ value =
        let rec aux typ value =
            match typ with
            | T_Unit -> "()"
            | T_Int -> "(match " ^ value ^ " with Int_rv n -> n)"
            | T_String -> "(match " ^ value ^ " with String_rv s -> s)"
            | T_Multiplicative (t0, t1) ->
                "(match " ^ value ^ " with Tuple_rv (v0, v1) -> (" ^ aux t0 "v0" ^ ", " ^ aux t1 "v1" ^ "))"
            | T_Additive _ -> ""
            | T_Function _ -> ""
            | T_Bool -> value
            | _ -> failwith (type_string typ ^ " not allowed") in
        aux typ value in

    let transpile_buffers =
        let readers =
            StringMap.to_list PE.buffers
            |> List.map (fun (buffer_name, (info : input_channel_info)) ->
                "let " ^ buffer_name ^ "_buffer () = \n" ^
                "\tlet wrapped_value = StringMap.find \"" ^ buffer_name ^ "\" !buffers in\n\t" ^
                unwrap_value info.typ "wrapped_value")
            |> String.concat "\n" in
        "let buffers = ref (PE.buffer_values ())\n" ^
        readers ^ "\n" in

    let transpile_write_channels =
        let rec aux absyn =
            match absyn with
            | [] -> "\t\t| _ -> failwith (\"Invalid channel \" ^ channel_name ^ \"\\\"\") in\n"
            | top :: tops -> (
                match top with
                | TopBind (channel_name, Term ((_, typ), term)) -> (
                    let wrapped_value = signal_type_to_constructor typ "value" in
                    "| \"" ^ channel_name ^ "\" -> " ^ wrapped_value ^ "\n" ^
                    aux tops)
                | _ -> aux tops) in
        "let write_channel channel_name value =\n" ^
        "\tlet wrapped_value =\n" ^
        "\t\tmatch channel_name with\n" ^
        "\t\t" ^ aux absyn ^
        "\tlet channel = StringMap.find channel_name PE.output_channels in\n" ^
        "\tchannel.handler wrapped_value\n" in

    let transpile_set_output_channels =
        "let set_output_channel channel_name (thunk, in_channels) =\n" ^ 
        "\toutputs := StringMap.add channel_name (thunk, in_channels) !outputs\n" in

    let transpile_read_inputs absyn =
        let get_default_value typ =
            match typ with
            | T_Unit -> "()"
            | T_Int -> "0"
            | T_String -> "\"\""
            | T_Bool -> "false"
            | _ -> failwith "Not implemented" in
        StringMap.to_list (get_advanced_channels_tops absyn)
        |> List.map (fun (advanced_channel, typ) ->
            "let " ^ advanced_channel ^ "_update = ref " ^ get_default_value typ ^ "\n")
        |> String.concat "\n" in

    let transpile_write_inputs absyn =
        let cases =
            StringMap.to_list (get_advanced_channels_tops absyn)
            |> List.map (fun (advanced_channel, typ) ->
                let constructor = type_to_constructor_pattern typ "value" in
                let value = unwrap_value typ "value" in
                "\t| \"" ^ advanced_channel ^ "\" -> " ^ advanced_channel ^ "_update := " ^ value)
            |> String.concat "\n" in
        "let update_input_channel channel_name value =
            updated_channel_name := channel_name;
            match channel_name with\n" ^
        cases ^ "\n" ^
        "\t| _ -> ()\n" in

    let rec transpile_bindings absyn =
        match absyn with
        | [] -> ""
        | top :: tops -> (
            match top with
            | TopLet (binding_name, _, term) ->
                let rec_or_empty = rec_or_empty term in
                "let " ^ rec_or_empty ^ binding_name ^ " = " ^ transpile_term term ^ "\n" ^
                transpile_bindings tops
            | TypeDef(n,ps,ty) -> 
                let polys = match ps with
                | [] -> ""
                | ps -> " ("^(List.map (fun p -> "'"^p) ps |> String.concat ", ")^")"
                in
                "type"^polys^" "^n^" = "^type_string ty^"\n"^transpile_bindings tops
            | _ -> transpile_bindings tops) in

    let rec transpile_channel_bindings absyn =
        match absyn with
        | [] -> ""
        | top :: tops -> (
            match top with
            | TopBind (channel_name, term) ->
                let transpiled_term = transpile_term term in
                let init_channel =
                    "\tmatch " ^ transpiled_term ^ " with\n" ^
                    "\t| Cons (head, tail) ->\n" ^
                    "\twrite_channel \"" ^ channel_name ^ "\" head;\n" ^
                    "\tset_output_channel \"" ^ channel_name ^ "\" tail\n" in
                let top_binding = "let () =\n" ^ init_channel in
                top_binding ^ transpile_channel_bindings tops
            | _ -> transpile_channel_bindings tops) in
    "open Arclib.Runtime_value
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
    let updated_channel_name = ref \"\""^
    transpile_buffers ^
    transpile_set_output_channels ^
    transpile_write_channels ^
    transpile_read_inputs absyn ^
    transpile_write_inputs absyn ^
    transpile_bindings absyn ^
    transpile_channel_bindings absyn ^
    "
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
    "
end
