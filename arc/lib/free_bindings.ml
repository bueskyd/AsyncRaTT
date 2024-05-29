open Absyn
open Defaults

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type state = S of {
    bindings : int StringMap.t list;
    binding_level : int
}

let empty_state = S {
    bindings = [StringMap.empty];
    binding_level = 0
}

module FreeM = Monad.Make(struct
    type s = state
    type e = string
    let debug_info = None
end)
open FreeM

let push_scope =
    M (fun (S state) ->
        let state' = S { state with bindings = StringMap.empty :: state.bindings } in
        Ok((), state')
    )

let pop_scope =
    M (fun (S state) ->
        let state' = S { state with bindings = List.tl state.bindings } in
        Ok((), state')
    )

let increase_binding_level =
    M (fun (S state) ->
        let state' = S { state with binding_level = state.binding_level + 1} in
        Ok((), state')
    )

let decrease_binding_level =
    M (fun (S state) ->
        match state.binding_level with
        | 0 -> Error "Cannot decrease binding_level below 0"
        | _ ->
            let state' = S { state with binding_level = state.binding_level - 1} in
            Ok((), state')
    )

let current_binding_level =
    M (fun (S state) ->
        Ok(state.binding_level, S state)
    )


let declare name =
    M (fun (S state) ->
        let top_scope = List.hd state.bindings in
        match StringMap.find_opt name top_scope with
        | Some _ -> 
            Error ("A binding with that name already exists in the current scope: " ^ name)
        | None ->
            let scopes = List.tl state.bindings in
            let scopes' = StringMap.add name state.binding_level top_scope :: scopes in
            let state' = S { state with bindings = scopes' } in
            Ok ((), state'))

let print_environment =
    M (fun (S state) ->
        print_endline ("Scopes: " ^ string_of_int (List.length state.bindings));
        List.iter (fun scope ->
            print_endline "Scope:";
            StringMap.iter (fun k bl ->
                print_endline ("\t" ^ k ^ " -> " ^ string_of_int bl)) scope) state.bindings;
        Ok((), S state)
    )

let declare_many bindings =
    List.map declare bindings
    |> sequence
    >>>= return ()

let lookup name =
    let rec lookup' vars =
        match vars with
        | [] -> Error ("Undeclared binding " ^ name)
        | scope :: scopes -> (
            let binding_opt = StringMap.find_opt name scope in
            match binding_opt with
            | Some binding_level -> Ok binding_level
            | None -> lookup' scopes) in
    M (fun (S state) ->
        match lookup' state.bindings with
        | Ok binding_level -> Ok (binding_level, S state)
        | Error msg -> Error msg
    )

let filter_for_current_level free_bindings =
    current_binding_level >=> fun current_binding_level ->
    List.map (fun (binding_name, binding_level) ->
        if binding_level < current_binding_level
        then Some binding_name
        else None) free_bindings
    |> List.filter Option.is_some
    |> List.map Option.get

let rec free_term_bindings term =
    let Term (x, term_inner) = term in
    match term_inner with
    | Value v ->
        debug_print "Free bindings value" >>>=
        free_value_bindings v >>= fun (free_bindings, v') ->
        return (free_bindings, Term (x, Value v'))
    | Tuple(t0, t1) ->
        debug_print "Free bindings tuple" >>>=
        free_term_bindings t0 >>= fun (fb0, t0') ->
        free_term_bindings t1 >>= fun (fb1, t1') ->
        return (fb0 @ fb1, Term (x, Tuple (t0', t1')))
    | App(t0, t1) ->
        debug_print "Free bindings app" >>>=
        free_term_bindings t0 >>= fun (fb0, t0') ->
        free_term_bindings t1 >>= fun (fb1, t1') ->
        return (fb0 @ fb1, Term (x, App (t0', t1')))
    | Let(name, typ_opt, body_term, in_term) ->
        debug_print "Free bindings let" >>>=
        push_scope >>>=
        declare name >>>=
        push_scope >>>=
        free_term_bindings body_term
        >>= fun (body_free_bindings, body_term') ->
        free_term_bindings body_term >>>=
        pop_scope >>>=
        free_term_bindings in_term >>= fun (in_term_free_bindings, in_term') ->
        pop_scope >>>=
        return (
            body_free_bindings @ in_term_free_bindings,
            Term (x, Let (name, typ_opt, body_term', in_term')))
    | Match(matched_term, alts) ->
        debug_print "Free bindings match" >>>= (
        List.map
            (fun (pats, term) -> 
                let binds = List.map fst (binds_from_pattern (List.hd pats)) in
                List.map debug_print binds |> sequence >>>=
                push_scope >>>=
                declare_many binds >>>=
                free_term_bindings term >>= fun (free_bindings, term') ->
                pop_scope >>>=
                return (free_bindings, (pats, term')))
            alts
        |> sequence >>= fun alt_results ->
        let (lst, alts') = List.split alt_results in
        let free_alts_bindings = List.flatten lst in
        free_term_bindings matched_term >>= fun (matched_term_free_bindings, matched_term') ->
        let free_bindings = free_alts_bindings @ matched_term_free_bindings in
        return (free_bindings, Term (x, Match (matched_term', alts'))))
    | Delay(clock, _, t) ->
        debug_print "Free bindings delay" >>>=
        increase_binding_level
        >>>= free_term_bindings t >>= fun (free_bindings, t') ->
        filter_for_current_level free_bindings >>= fun free_bindings' ->
        decrease_binding_level >>>=
        return (free_bindings, Term (x, Delay (clock, StringSet.of_list free_bindings', t')))
    | Adv t ->
        debug_print "Free bindings adv" >>>=
        free_term_bindings t >>= fun (free_bindings, t') -> return (free_bindings, Term (x, Adv t'))
    | Select(cl0, cl1, v0, v1) ->
        debug_print "Free bindings select" >>>=
        free_value_bindings v0 >>= fun (fb0, v0') ->
        free_value_bindings v1 >>= fun (fb1, v1') ->
        return (fb0 @ fb1, Term (x, Select (cl0, cl1, v0', v1')))
    | Unbox t ->
        debug_print "Free bindings unbox" >>>=
        free_term_bindings t >=> fun (free_bindings, t') -> (free_bindings, Term (x, Unbox t'))
    | Fix (name, t) ->
        debug_print "Free bindings fix" >>>=
        free_term_bindings t >=> fun (free_bindings, t') -> (free_bindings, Term (x, Fix (name, t')))
    | Never -> return ([], term)
    | Read _ -> return ([], term)
    | SignalCons(t0, t1) ->
        debug_print "Free bindings SignalCons" >>>=
        free_term_bindings t0 >>= fun (fb0, t0') ->
        free_term_bindings t1 >>= fun (fb1, t1') ->
        return (fb0 @ fb1, Term (x, SignalCons (t0', t1')))

and free_value_bindings value =
    let Val (x, value_inner) = value in
    match value_inner with
    | Binding name ->
        debug_print ("Free bindings variable " ^ name) >>>=
        lookup name >>= fun binding_level ->
        return ([(name, binding_level)], value)
    | Unit -> return ([], value)
    | String _ -> return ([], value)
    | Int _ -> return ([], value)
    | Lambda(param_name, typ_opt, _, lambda_term) ->
        debug_print "Free bindings lambda" >>>=
        push_scope
        >>>= increase_binding_level
        >>>= declare param_name
        >>>= free_term_bindings lambda_term >>= fun (lambda_term_free_bindings, lambda_term') ->
        pop_scope >>>=
        filter_for_current_level lambda_term_free_bindings >>= fun lambda_term_free_bindings' ->
        decrease_binding_level >>>=
        return (lambda_term_free_bindings, Val (x, Lambda(param_name, typ_opt, StringSet.of_list lambda_term_free_bindings', lambda_term')))
    | Wait _ -> return ([], value)
    | Box (t, _) ->
        debug_print "Free bindings box" >>>=
        increase_binding_level >>>=
        free_term_bindings t >>= fun (free_bindings, t') ->
        filter_for_current_level free_bindings >>= fun free_bindings' ->
        decrease_binding_level >>>=
        return (free_bindings, Val (x, Box (t', StringSet.of_list free_bindings')))
    | Bool _ -> return ([], value)
    | Construct(name, t) ->
        debug_print "Free bindings construct" >>>=
        free_term_bindings t >>= fun (free_bindings, t') -> return (free_bindings, Val (x, Construct (name, t')))

let default_state =
    let S empty_state = empty_state in
    let top_scope =
        List.map (fun (Default default) -> (default.name, 0)) defaults
        |> StringMap.of_list in
    S { empty_state with bindings = [top_scope] }

let attach_free_bindings absyn =
    let rec aux absyn =
        match absyn with
        | [] -> return []
        | top :: tops -> (
            match top with
            | TopLet (binding_name, typ_opt, term) ->
                declare binding_name >>>=
                free_term_bindings term >>=
                fun (free_bindings, term') ->
                aux tops >>= fun tops' ->
                return (TopLet (binding_name, typ_opt, term') :: tops')
            | TopBind (output_channel, term) ->
                free_term_bindings term >>=
                fun (free_bindings, term') ->
                aux tops >>= fun tops' ->
                return (TopBind (output_channel, term') :: tops')
            | TypeDef _ ->
                aux tops >>= fun tops' ->
                return (top :: tops')) in
    let m = eval_m (aux absyn) default_state in
    match m with
    | Ok (tops, _) -> tops
    | Error e -> failwith e
