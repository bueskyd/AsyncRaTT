open Absyn
open Defaults
open Exceptions

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

type state = S of {
    tick : clock_result option
}

let empty_state = S { tick = None }

module EvalM = Monad.Make(struct
    type s = state
    type e = string * int option
    let debug_info = None
end)
open EvalM

let tick (M m) =
    M (fun (S state) ->
        match state.tick with
        | Some _ ->
            failwith "There can be at most one tick in a context"
        | None ->
            let state' = S { state with tick = Some NoClock} in
            match m state' with
            | Ok(result, (S state'')) -> (
                let state''' = S { state'' with tick = None } in
                Ok(result, state'''))
            | error -> error
    )

let has_tick =
    M (fun (S state) -> Ok(Option.is_some state.tick, S state))

let unwrap_single cl =
    match cl with
    | Single cl -> return cl
    | _ -> fail ("Cannot unwrap clock", None)

let union_clocks cl0 cl1 =
    unwrap_single cl0 >>= fun (CS cl0) ->
    unwrap_single cl1 >>= fun (CS cl1) ->
    let channels = StringSet.union cl0.channels cl1.channels in
    let variables = StringSet.union cl0.variables cl1.variables in
    let rec distinct calls =
        match calls with
        | [] -> []
        | x :: xs -> List.filter ((<>) x) xs |> distinct in
    return (Single (CS {
        channels = channels;
        variables = variables
    }))

let advance_on clock line_number =
    M (fun (S state) ->
        match state.tick with
        | Some cl -> (
            match clock_set_compatible clock cl with
            | Single _ as cl ->
                let state' = S { state with
                    tick = Some cl } in
                Ok ((), state')
            | MultipleClocks -> Error ("Incompatible clocks", Some line_number)
            | NoClock -> Error ("Cannot advance on no clock", Some line_number))
        | None -> Error ("Cannot advance outside a ticked context", Some line_number))

let get_clock_advanced_on =
    M (fun (S state) ->
        match state.tick with
        | Some clock -> Ok (clock, S state)
        | None -> Error ("Not inside tick", None))

let rec infer_term_clock (Term((ln,ty),term) as wrap) : unit monad =
    match term with
    | Value v -> infer_value_clock v
    | Tuple(t1, t2) -> 
        infer_term_clock t1 >>>= infer_term_clock t2
    | Let(name, binding_typ, t1, t2) ->
        infer_term_clock t1 >>>= infer_term_clock t2
    | App(t1, t2) ->
        infer_term_clock t1 >>>= infer_term_clock t2
    | Delay(_, free_bindings, t) ->
        fail ("This should never happen", Some ln)
    | Adv (Term (_, Value (Val (_, Binding binding_name)))) -> advance_on (singleton_variable_clock binding_name) ln
    | Adv (Term (_, Value (Val (_, Wait channel_name)))) -> advance_on (singleton_channel_clock channel_name) ln
    | Adv _ -> fail ("This should never happen", Some ln)
    | Unbox t -> infer_term_clock t
    | Fix(n, t) -> infer_term_clock t
    | Match(t, alts) ->
        debug_print "infer clock match" >>>= 
        (List.map (fun (_, term) -> infer_term_clock term) alts
        |> sequence) >>>= infer_term_clock t
    | Select(_, _, v1, v2) -> 
        debug_print "infer clock select" >>>=
            let get_clock (Val (_, value)) =
                match value with
                | Binding binding_name -> return (singleton_variable_clock binding_name)
                | Wait channel_name -> return (singleton_channel_clock channel_name)
                | _ -> fail ("Invalid select", Some ln) in
            get_clock v1 >>= fun cl1 ->
            get_clock v2 >>= fun cl2 ->
            union_clocks cl1 cl2 >>= fun cl -> advance_on cl ln
    | Never -> return ()
    | Read _ -> return ()
    | SignalCons(t1, t2) -> 
        infer_term_clock t1 >>>= infer_term_clock t2

and infer_value_clock (Val((ln,ty),value)) : unit monad =
    match value with
    | Binding _
    | Unit -> return ()
    | Lambda (param_name, typ_opt, free_bindings, term) ->
        fail ("Invalid AST. Assumed no lambda expressions", Some ln)
    | Bool _
    | String _
    | Int _ -> return ()
    | Construct(name, t) -> infer_term_clock t
    | Wait _ -> return ()
    | Box (t, _) -> infer_term_clock t

let rec infer_term_clocks term =
    let Term ((ln, typ), term) = term in
    match term with
    | Value value -> infer_value_clocks value >=> fun value -> Term ((ln, typ), Value value)
    | Tuple (t0, t1) ->
        infer_term_clocks t0 >>= fun t0 ->
        infer_term_clocks t1 >>= fun t1 ->
            return (Term ((ln, typ), Tuple (t0, t1)))
    | App (t0, t1) ->
        infer_term_clocks t0 >>= fun t0 ->
        infer_term_clocks t1 >>= fun t1 ->
            return (Term ((ln, typ), App (t0, t1)))
    | Let (name, typ_opt, t0, t1) ->
        infer_term_clocks t0 >>= fun t0 ->
        infer_term_clocks t1 >>= fun t1 ->
            return (Term ((ln, typ), Let (name, typ_opt, t0, t1)))
    | Match (matched_term, alts) ->
        infer_term_clocks matched_term >>= fun matched_term ->
        (List.map (fun (patterns, term) ->
            infer_term_clocks term >>= fun term -> return (patterns, term))
            alts
        |> sequence) >>= fun alts ->
        return (Term ((ln, typ), Match (matched_term, alts)))
    | Delay (_, free_bindings, term) ->
        tick (infer_term_clock term >>>= get_clock_advanced_on) >>= fun clock_result -> (
            match clock_result with
            | Single clock ->
                infer_term_clocks term >>= fun term ->
                return (Term ((ln, typ), Delay (clock, free_bindings, term)))
            | NoClock ->
                fail ("Cannot delay on an empty clock", Some ln)
            | MultipleClocks ->
                fail ("Cannot delay on multiple clocks", Some ln))
    | Adv _ -> return (Term ((ln, typ), term))
    | Select (_, _, v0, v1) ->
        let get_clock (Val (_, value)) =
            match value with
            | Binding binding_name -> return (singleton_variable_clock binding_name)
            | Wait channel_name -> return (singleton_channel_clock channel_name)
            | _ -> fail ("Invalid select", Some ln) in
        get_clock v0 >>= unwrap_single >>= fun cl0 ->
        get_clock v1 >>= unwrap_single >>= fun cl1 ->
        return (Term ((ln, typ), Select (cl0, cl1, v0, v1)))
    | Unbox term ->
        infer_term_clocks term >>= fun term ->
        return (Term ((ln, typ), Unbox term))
    | Fix (name, term) ->
        infer_term_clocks term >>= fun term ->
        return (Term ((ln, typ), Fix (name, term)))
    | Never -> return (Term ((ln, typ), term))
    | Read _ -> return (Term ((ln, typ), term))
    | SignalCons (t0, t1) ->
        infer_term_clocks t0 >>= fun t0 ->
        infer_term_clocks t1 >>= fun t1 ->
            return (Term ((ln, typ), SignalCons (t0, t1)))

and infer_value_clocks value =
    let Val ((ln, typ), value) = value in
    match value with
    | Binding _
    | Unit
    | Int _ -> return (Val ((ln, typ), value))
    | Lambda (param_name, typ_opt, free_bindings, term) ->
        infer_term_clocks term >>= fun term ->
        return (Val ((ln, typ), Lambda (param_name, typ_opt, free_bindings, term)))
    | Wait _ -> return (Val ((ln, typ), value))
    | Box (term, free_bindings) ->
        infer_term_clocks term >>= fun term ->
        return (Val ((ln, typ), Box (term, free_bindings)))
    | Bool _ -> return (Val ((ln, typ), value))
    | String _ -> return (Val ((ln, typ), value))
    | Construct (name, term) ->
        infer_term_clocks term >>= fun term ->
        return (Val ((ln, typ), Construct (name, term)))

let pattern_bindings pattern =
    let rec aux pattern acc =
        match pattern with
        | P_Any(name,_) -> name :: acc
        | P_Wild
        | P_Int _
        | P_Bool _ -> acc
        | P_Tuple (p0, p1, _)
        | P_Cons (p0, p1, _) -> aux p0 acc |> aux p1
        | P_Construct (name, p, _) -> aux p (name :: acc) in
    aux pattern []

let default_bindings : string list =
    List.map (fun (Default info) -> info.name) defaults

let default_state = empty_state

let infer_top_clocks print_error absyn =
    let rec loop absyn =
        match absyn with
        | [] -> return []
        | top :: tops ->
            match top with
            | TypeDef _ -> loop tops >>= fun tops -> return (top :: tops)
            | TopLet(name, typ, term) ->
                infer_term_clocks term >>= fun term' ->
                loop tops >>= fun tops ->
                return (TopLet(name, typ, term') :: tops)
            | TopBind(channel_name, term) ->
                infer_term_clocks term >>= fun term' ->
                loop tops >>= fun tops -> return (TopBind(channel_name, term') :: tops) in
    match eval_m (loop absyn) default_state with 
    | Ok(res,_) -> res 
    | Error(msg,ln) -> (print_error msg ln ; raise_problem Clocking)
