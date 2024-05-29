open Absyn
open Runtime_value
open Exceptions
open Defaults
open Program_env

module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)

module type Interpreter = sig
    val run_program : (int*typ)top list -> unit
end

module Make (PE : Program_env.ProgramEnvironment) : Interpreter = struct

let empty_value_env = VE {
    vars = StringMap.empty
}

let add_to_value_env name value clock (VE ve) =
    let binding = B { value = value; clock = clock; top_level = false } in
    VE { vars = StringMap.add name binding ve.vars }

type heap = (* The runtime_values in the IntMaps must always be Closures *)
    | OneHeap of delayed IntMap.t
    | TwoHeap of {
        now : delayed IntMap.t;
        update : string * runtime_value;
        later : delayed IntMap.t
    }

type heap_type =
    | OneHeap_t
    | TwoHeap_t

type state = S of {
    bindings : runtime_binding StringMap.t list;
    heap : heap;
    next_heap_location : int;
    outputs : int StringMap.t;
    buffers : runtime_value StringMap.t
}

let empty_state = S {
    bindings = [StringMap.empty];
    heap = OneHeap IntMap.empty;
    next_heap_location = 0;
    outputs = StringMap.empty;
    buffers = StringMap.empty
}

module EvalM = Monad.Make(struct
    type s = state
    type e = string * problem * int option
    let debug_info = None
end)
open EvalM

let push_scope =
    M (fun (S state) ->
        let state' = S { state with bindings = StringMap.empty :: state.bindings } in
        Ok((), state'))

let pop_scope =
    M (fun (S state) ->
        let state' = S { state with bindings = List.tl state.bindings } in
        Ok((), state'))

let allocate =
    M (fun (S state) ->
        let location = state.next_heap_location in
        (* This might cause an interger overflow. Maybe fix it? *)
        let state' = S { state with next_heap_location = location + 1 } in
        Ok(location, state'))

let get_update =
    M (fun (S state) ->
        match state.heap with
        | OneHeap _ -> Error("Cannot get an update in a one heap", Interpretation, None)
        | TwoHeap heap -> Ok(heap.update, S state))

let init location computation =
    M (fun (S state) ->
        let heap' =
            match state.heap with
            | OneHeap h -> OneHeap (IntMap.add location computation h)
            | TwoHeap h -> TwoHeap { h with later = IntMap.add location computation h.later } in
        let state' = S { state with heap = heap' } in
        Ok((), state'))

let print_environment =
    M (fun (S state) ->
        print_endline ("Scopes: " ^ string_of_int (List.length state.bindings));
        List.iter (fun scope ->
            print_endline "Scope:";
            StringMap.iter (fun k (B b) ->
                print_endline ("\t" ^ k ^ " -> " ^ runtime_value_string b.value)) scope) state.bindings;
        Ok((), S state))

let lookup name =
    let rec lookup' vars =
        match vars with
        | [] -> Error ("Undeclared binding " ^ name)
        | scope :: scopes -> (
            let binding_opt = StringMap.find_opt name scope in
            match binding_opt with
            | Some binding -> Ok binding
            | None -> lookup' scopes) in
    M (fun (S state) ->
        match lookup' state.bindings with
        | Ok binding -> Ok(binding, S state)
        | Error msg -> Error(msg,Interpretation,None)
    )

let lookup_many binding_names =
    List.map (fun binding_name ->
        lookup binding_name >=> fun value ->
            (binding_name, value))
        binding_names
    |> sequence

let lookup_buffer_value channel_name =
    M (fun (S state) ->
        let value_opt = StringMap.find_opt channel_name state.buffers in
        match value_opt with
        | Some value -> Ok(value, S state)
        | None -> Error("Buffer " ^ channel_name ^ " does not exist",Interpretation,None)
    )

let declare name value clock top_level =
    M (fun (S state) ->
        let top_scope = List.hd state.bindings in
        match StringMap.find_opt name top_scope with
        | Some _ -> 
            Error ("A binding with that name already exists in the current scope: " ^ name,Interpretation,None)
        | None ->
            let scopes = List.tl state.bindings in
            let binding = B { value = value; clock = clock; top_level = top_level } in
            let scopes' = StringMap.add name binding top_scope :: scopes in
            let state' = S { state with bindings = scopes' } in
            Ok((), state'))

let declare_or_assign name value clock top_level =
    M (fun (S state) ->
        let top_scope = List.hd state.bindings in
        let scopes = List.tl state.bindings in
        let binding = B { value = value; clock = clock; top_level = top_level } in
        let scopes' = StringMap.add name binding top_scope :: scopes in
        let state' = S { state with bindings = scopes' } in
        Ok((), state')
    )

let lookup_computation location =
    M (fun (S state) ->
        let lookup =
            match state.heap with
            | OneHeap h -> Error ("Cannot lookup a term in a OneHeap. Can be caused by calling adv outside of a delay.",Interpretation,None)
            | TwoHeap h ->
                match IntMap.find_opt location h.now with
                | Some (Delayed _ as delayed) -> Ok delayed
                | None ->
                    Error (
                        "Location " ^
                        string_of_int location ^
                        " does not exist in the now heap",Interpretation,None) 
        in
        match lookup with
        | Ok delayed -> Ok(delayed, S state)
        | Error msg -> Error msg
    )

let heap_type =
    M (fun (S state) ->
        let heap_type =
            match state.heap with
            | OneHeap _ -> OneHeap_t
            | TwoHeap _ -> TwoHeap_t in
        Ok(heap_type, S state)
    )

let set_output_channel channel_name location =
    M (fun (S state) ->
        let outputs' = StringMap.add channel_name location state.outputs in
        let state' = S { state with outputs = outputs' } in
        Ok((), state')
    )

let declare_many_impl bindings declare =
    List.map (fun (name, value, clock, top_level) -> declare name value clock top_level) bindings
    |> sequence
    >>>= return ()

let declare_or_assign_many bindings =
    declare_many_impl bindings declare_or_assign

let declare_many bindings =
    declare_many_impl bindings declare

let declare_vars_in_value_env (VE value_env) =
    StringMap.to_list value_env.vars
    |> List.map (fun (n, B binding) -> (n, binding.value, binding.clock, binding.top_level))
    |> declare_many

let declare_or_assign_vars_in_value_env (VE value_env) =
    StringMap.to_list value_env.vars
    |> List.map (fun (n, B binding) -> (n, binding.value, binding.clock, binding.top_level))
    |> declare_or_assign_many

let print_runtime_value value message =
    print_endline (message ^ runtime_value_string value)

let rec match_value value alts =
    match alts with
    | [] -> failwith ("Unmatched value " ^ runtime_value_string value)
    | (alt_patterns, alt_term) :: alts' ->
        let rec matches pattern value =
            match pattern, value with
            | P_Wild, _ -> Some[]
            | P_Any(name, _), _ -> Some[name, value]
            | P_Int n, Int_rv v -> if n = v then Some[] else None
            | P_Bool b, Bool_rv v -> if b = v then Some[] else None
            | P_Tuple(p0, p1, _), Tuple_rv (t0, t1) -> (
                match matches p0 t0, matches p1 t1 with
                | Some bs0, Some bs1 -> Some(List.rev_append bs0 bs1)
                | _,_ -> None
            )
            | P_Cons(head, tail, _), Signal_rv (t0, t1) -> (
                match matches head t0, matches tail t1 with
                | Some bs0, Some bs1 -> Some(List.rev_append bs0 bs1)
                | _,_ -> None
            )
            | P_Construct(str, p, _), Construct_rv (c_name, v) ->
                if str = c_name then matches p v
                else None
            | _, _ -> None (* failwith ("Pattern not implemented: " ^ alt_string (alt_pattern,alt_term) ^ " | " ^ runtime_value_string value) *)
        in
        match List.find_map (fun pattern -> matches pattern value) alt_patterns with
        | Some binds -> (alt_term, binds)
        | None -> match_value value alts'

let determine_clock (CS clock_set) =
    StringSet.to_list clock_set.variables
    |> List.map (fun name ->
        lookup name >=> fun (B binding) ->
        let C clock = binding.clock in
        StringSet.to_list clock)
    |> sequence
    >=> fun channels -> List.flatten channels
    |> StringSet.of_list
    |> StringSet.union clock_set.channels
    |> fun channels -> C channels

let value_env_from_names binding_names =
    lookup_many (StringSet.to_list binding_names) >>= fun free_bindings' ->
    let vars = StringMap.of_list free_bindings' in
    return (VE { vars = vars })

let rec eval_term (Term((ln,typ),term)) =
    match term with
    | Value v ->
        debug_print "Eval Value" >>>=
        eval_value v
    | Tuple(t0, t1) ->
        debug_print "Eval Tuple_t" >>>=
        eval_term t0 >>= fun (v0, c0) ->
        eval_term t1 >>= fun (v1, c1) ->
            return (Tuple_rv (v0, v1), empty_clock)
    | App(func_term, arg_term) ->
        debug_print "Eval App" >>>=
        eval_term func_term >>= fun (func_value, func_clock) -> (
        match func_value with
        | Closure (param_name, VE value_env, lambda_term) ->
            eval_term arg_term >>= fun (arg_value, func_clock) ->
            let VE value_env' =
                    add_to_value_env param_name arg_value func_clock (VE value_env) in
            push_scope
            >>>= declare_vars_in_value_env (VE value_env')
            >>>= eval_term lambda_term
            >>= fun (lambda_value, lambda_clock) ->
            pop_scope >>>= (
            match lambda_value with
            | Closure (param_name_ret, VE value_env_ret, lambda_term_ret) ->
                let merged_vars =
                    StringMap.merge (fun _ fst snd ->
                        match fst, snd with
                        | None, None -> None
                        | Some _, None -> fst
                        | None, Some _ -> snd
                        | Some _, Some _ -> snd) value_env'.vars value_env_ret.vars in
                let merged_value_env = VE { vars = merged_vars } in
                return (Closure (param_name_ret, merged_value_env, lambda_term_ret), lambda_clock)
            | _ -> return (lambda_value, lambda_clock))
        | Built_in_2 build_in ->
            eval_term arg_term >>= fun (arg_value, arg_clock) ->
            return (Built_in_1 (build_in arg_value), arg_clock)
        | Built_in_1 build_in ->
            eval_term arg_term >>= fun (arg_value, arg_clock) ->
            return (build_in arg_value, arg_clock)
        | _ -> failwith ("Not a lambda expression: " ^ runtime_value_string func_value))
    | Let(name, _, body_term, in_term) ->
        debug_print ("Eval Let " ^ name) >>>=
        push_scope >>>= (
        match body_term with
        | Term (_, Fix (_, body_term')) -> declare name (Rec body_term') empty_clock false
        | _ -> return ()) >>>=
        eval_term body_term
        >>= fun (binding_value, binding_clock) ->
        pop_scope
        >>>= push_scope >>>= (
        match binding_value with
        | Closure (param_name, VE value_env, term) ->
            let param_binding = B { value = binding_value; clock = empty_clock; top_level = false } in
            let vars = StringMap.add name param_binding value_env.vars in
            let value_env' = VE { vars = vars } in
            let closure = Closure (param_name, value_env', term) in
            declare name closure binding_clock false
        | _ -> declare name binding_value binding_clock false)
        >>>= eval_term in_term >>= fun (in_value, in_clock) ->
        pop_scope
        >>>= return (in_value, in_clock)
    | Match(term_matched_on, alts) ->
        debug_print "Eval Match" >>>=
        eval_term term_matched_on >>= fun (value_matched_on, clock_matched_on) ->
        let (case_term, binds) = match_value value_matched_on alts in
        push_scope >>>=
        declare_many (List.map (fun (n, v) ->
            match v with
            | Location (_, clock) -> (n, v, clock, false)
            | _ -> (n, v, empty_clock, false)) binds) >>>=
        debug_print "Eval match case" >>>=
        eval_term case_term >>= fun (value, clock) ->
        pop_scope >>>=
        return (value, clock)
    | Delay(clock_set, free_bindings, term) ->
        debug_print "Eval Delay" >>>=
        allocate >>= fun location ->
        value_env_from_names free_bindings >>= fun value_env ->
        determine_clock clock_set >>= fun (C clock) ->
        init location (Delayed { value_env = value_env; term = term; clock = C clock }) >>>=
        return (Location (location, C clock), C clock) (* Use the correct clock *)
    | Adv term ->
        debug_print "Eval Adv" >>>=
        heap_type >>= fun heap_type -> (
        match heap_type with
        | OneHeap_t -> failwith "Cannot advance in a OneHeap"
        | TwoHeap_t -> (
            match term with
            | Term(_,Value(Val(_,(Wait channel_name)))) ->
                get_update >>= fun (_, value) -> return (value, singleton_clock channel_name)
            | _ -> eval_term term >>= fun (value, clock) -> (
                match value with
                | Location (location, _) ->
                    lookup_computation location >>= fun (Delayed delayed) -> ( 
                        (* We can prevent evaluating the term multiple times by only doing it once in the input transition *)
                        let VE value_env = delayed.value_env in
                        push_scope >>>=
                        declare_vars_in_value_env (VE value_env) >>>=
                        eval_term delayed.term >>= fun v ->
                        pop_scope >>>= return v
                    )
                | Wait_rv ->
                    get_update >>= fun (channel_name, value) ->
                    return (value, singleton_clock channel_name)
                | _ -> fail ("Can only advance locations",Interpretation,None))))
    | Select(cs0, cs1, v0, v1) -> (
        debug_print "Eval Select" >>>=
        get_update >>= fun (channel_name, value) ->
        determine_clock cs0 >>= fun (C cl0) ->
        determine_clock cs1 >>= fun (C cl1) ->
        eval_value v0 >>= fun (v0', C a) ->
        eval_value v1 >>= fun (v1', C b) ->
        let in_left = StringSet.mem channel_name cl0 in
        let in_right = StringSet.mem channel_name cl1 in
        match in_left, in_right with
        | true, true -> (
            match v0', v1' with
            | Location (l0, _), Location (l1, _) ->
                lookup_computation l0 >>= fun (Delayed d0) ->
                lookup_computation l1 >>= fun (Delayed d1) ->
                let VE ve0 = d0.value_env in
                let VE ve1 = d1.value_env in
                push_scope >>>=
                declare_vars_in_value_env (VE ve0) >>>=
                eval_term d0.term >>= fun (dv0, _) ->
                pop_scope >>>=
                push_scope >>>=
                declare_vars_in_value_env (VE ve1) >>>=
                eval_term d1.term >>= fun (dv1, _) ->
                pop_scope >>>=
                return (Construct_rv ("Both", Tuple_rv (dv0, dv1)), empty_clock) (* Use the correct clock *)
            | _ -> failwith ("Not locations " ^ runtime_value_string v0' ^ ", " ^ runtime_value_string v1'))
        | true, false ->
            eval_value v0 >>= fun (value, _) -> (
            match value with
            | Location (l, _) ->
                lookup_computation l >>= fun (Delayed delayed) ->
                let VE value_env = delayed.value_env in
                push_scope >>>=
                declare_vars_in_value_env (VE value_env) >>>=
                eval_term delayed.term >>= fun (value, clock) ->
                pop_scope >>>=
                return (Construct_rv ("Left", Tuple_rv (value, v1')), clock)
            | _ -> failwith ("Not a location " ^ runtime_value_string value))
        | false, true ->
            eval_value v1 >>= fun (value, _) -> (
            match value with
            | Location (l, _) ->
                lookup_computation l >>= fun (Delayed delayed) ->
                let VE value_env = delayed.value_env in
                push_scope >>>=
                declare_vars_in_value_env (VE value_env) >>>=
                eval_term delayed.term >>= fun (value, clock) ->
                pop_scope >>>=
                return (Construct_rv ("Right", Tuple_rv (v0', value)), clock)
            | _ -> failwith ("Not a location " ^ runtime_value_string value))
        | false, false -> failwith "At least one clock must tick")
    | Unbox term ->
        debug_print "Eval Unbox" >>>=
        eval_term term >>= fun (value, _) -> (
        match value with
        | Box (term', value_env) ->
            push_scope >>>=
            declare_or_assign_vars_in_value_env value_env >>>= eval_term term' >>= fun result ->
            pop_scope >>>= return result
        | _ -> failwith "Result of unbox must be a boxed term")
    | Fix(_, term) -> debug_print "Eval Fix" >>>= eval_term term
    | Never -> 
        debug_print "Eval Never" >>>= 
        allocate >>= fun location -> 
        init location (Delayed { value_env = empty_value_env; term = Term((ln,typ),term); clock = empty_clock }) >>>=
        return (Location (location, empty_clock), empty_clock)
    | Read channel_name ->
        debug_print "Eval Read" >>>=
        lookup_buffer_value channel_name >>= fun value -> return (value, empty_clock)
    | SignalCons(t0, t1) ->
        debug_print "Eval SignalCons" >>>=
        eval_term t0 >>= fun (v0, c0) ->
        eval_term t1 >>= fun (v1, c1) ->
        return (Signal_rv (v0, v1), c1)

and eval_value (Val((ln,typ),value) as wrap) =
    match value with
    | Binding name ->
        debug_print ("Eval Variable " ^ name) >>>=
        lookup name >>= fun (B binding) -> (
        debug_print "" >>>=
        match binding.value with
        (* No need to declare bindings in value_env as only toplevel bindings are implicitly boxed*)
        | Box (term, _) when binding.top_level -> eval_term term
        | Rec term -> eval_term term
        | _ -> debug_print (name ^ " not boxed") >>>= return (binding.value, binding.clock))
    | Unit -> debug_print "Eval Unit" >>>= return (Unit_rv, empty_clock)
    | Int v -> debug_print "Eval Int" >>>= return (Int_rv v, empty_clock)
    | String str -> return (String_rv str, empty_clock)
    | Lambda(param_name, _, free_bindings, lambda_term) ->
        debug_print "Eval Lambda" >>>=
        value_env_from_names free_bindings >>= fun value_env ->
        return (Closure (param_name, value_env, lambda_term), empty_clock)
    | Wait channel_name ->
        debug_print "Eval Wait" >>>=
        return (Wait_rv, C (StringSet.singleton channel_name))
    | Box (term, free_binding) ->
        debug_print "Eval Box" >>>=
        value_env_from_names free_binding >>= fun value_env ->
        return (Box (term, value_env), empty_clock)
    | Bool b -> debug_print "Eval Bool" >>>= return (Bool_rv b, empty_clock)
    | Construct(name, term) ->
        debug_print "Eval Construct" >>>=
        eval_term term >>= fun (value, clock) ->
            return (Construct_rv (name, value), clock)

let default_state =
    let S es = empty_state in
    let bindings =
        List.map (fun (Default binding) -> (binding.name, binding.value))
        defaults in
    S { es with 
        bindings = [StringMap.of_list bindings];
        buffers = StringMap.map (fun info -> info.initial_buffer) PE.buffers
    }

let init tops =
    let ms =
        List.map (fun top ->
            match top with
            | TypeDef _ -> return ()
            | TopLet(name, _, Term(_,Fix(_, term))) ->
                declare name (Box (term, empty_value_env)) empty_clock true
            | TopLet(name, _, term) ->
                declare name (Box (term, empty_value_env)) empty_clock true
            | TopBind(channel_name, term) ->
                eval_term term >>= fun (signal, _) -> (
                match signal with
                | Signal_rv (v0, Location (location, C cl)) -> (
                    let channel_opt = StringMap.find_opt channel_name PE.output_channels in
                    match channel_opt with
                    | Some c ->
                        c.handler v0;
                        set_output_channel channel_name location
                    | None -> failwith ("Channel " ^ channel_name ^ " does not exist"))
                | Signal_rv (v0, Box (term, _)) -> (
                    let channel_opt = StringMap.find_opt channel_name PE.output_channels in
                    match channel_opt with
                    | Some c ->
                        c.handler v0;
                        eval_term term >>= fun (location, _) -> (
                        match location with
                        | Location (location, _) -> set_output_channel channel_name location
                        | _ -> failwith ("Not a location: " ^ runtime_value_string location))
                    | None -> failwith ("Channel " ^ channel_name ^ " does not exist"))
                | _ -> failwith ("Cannot initialize an output channel with value: " ^ runtime_value_string signal)))
            tops in
    let m = sequence ms in
    match eval_m m default_state with 
    | Ok(_,res) -> res 
    | Error(msg,p,ln) -> failwith msg

let clock_of location (S state) =
    let heap =
        match state.heap with
        | OneHeap h -> h
        | TwoHeap h -> h.now in
    let closure_opt = IntMap.find_opt location heap in
    match closure_opt with
    | Some (Delayed delayed) -> delayed.clock
    | None -> failwith ("Location " ^ string_of_int location ^ " does not exist")

let location_depends_on_channel location channel_name state =
    let C clock = clock_of location state in
    StringSet.mem channel_name clock

let do_input_transition channel_name value (S state) =
    match state.heap with
    | OneHeap heap ->
        let later' = IntMap.filter (fun l _ ->
            location_depends_on_channel l channel_name (S state) |> not) heap in
        let heap = TwoHeap {
            now = heap;
            update = (channel_name, value);
            later = later'
        } in
        let buffers = PE.buffer_values () in
        S { state with
            heap = heap;
            buffers = buffers }
    | TwoHeap _ -> failwith "Cannot do an input transition on a state with a two heap"

let collect_garbage (S state) =
    match state.heap with
    | OneHeap _ -> failwith "Cannot perform a garbage collection on a one heap"
    | TwoHeap heap ->
        let heap' = OneHeap heap.later in
        S { state with heap = heap' }

let do_output_transitions (S state) =
    match state.heap with
    | OneHeap _ -> failwith "Cannot do an output transition on a state with a one heap"
    | TwoHeap heap ->
        let (updated_channel, _) = heap.update in
        let locations_to_advance =
            StringMap.to_list state.outputs
            |> List.filter_map
            (fun (c, l) -> if location_depends_on_channel l updated_channel (S state)
                then Some (c, l)
                else None)
            in
        let computations_to_advance =
            List.filter_map
            (fun (c, l) -> IntMap.find_opt l heap.now |> Option.map (fun x -> (c, x)))
            locations_to_advance in
        let advanced_computations =
            List.map (fun (c, Delayed delayed) ->
                let VE value_env = delayed.value_env in
                push_scope >>>=
                declare_vars_in_value_env (VE value_env) >>>=
                eval_term delayed.term >>= fun (v, _) ->
                pop_scope >>>=
                return (c, v)) computations_to_advance
            |> sequence in
        let updated_channels = advanced_computations >>= (fun runtime_values ->
            List.fold_left (fun state (channel_name, runtime_value) ->
                match runtime_value with
                | Signal_rv (head, Location (location, _)) ->
                    set_output_channel channel_name location
                | Signal_rv (head, Box (term, _)) ->
                    eval_term term >>= fun (location, _) -> (
                    match location with
                    | Location (location, _) -> set_output_channel channel_name location
                    | _ -> failwith ("Not a location: " ^ runtime_value_string location))
                | _ -> failwith ("Not a valid value " ^ runtime_value_string runtime_value)) (return ()) runtime_values
            >>>= return runtime_values) in
        let (runtime_values, state') = match eval_m updated_channels (S state) with 
            | Ok res -> res
            | Error(msg,p,ln) -> failwith msg
        in
        let output_channels =
            List.filter_map (fun (name, v) ->
                Option.bind (
                    StringMap.find_opt name PE.output_channels)
                    (fun c -> Some (c.handler, v))) runtime_values in
        List.iter (fun (f, v) ->
            match v with
            | Signal_rv (head, tail) -> f head
            | _ -> failwith "Not a valid value") output_channels;
        state'

let run_program absyn =
    let rec loop state =
        let channel_values = PE.handle_events () in
        let state' = StringMap.fold (fun channel_name value state ->
            do_input_transition channel_name value state
            |> do_output_transitions
            |> collect_garbage) channel_values state in
        loop state' in
    let state = init absyn in
    let _ = PE.start_channels () in
    loop state

end
