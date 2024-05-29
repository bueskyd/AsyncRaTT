open Absyn
open Exceptions
open Defaults

module StringMap = Map.Make(String)

type state =
    S of {
        renamings : string StringMap.t list;
        next_id : int
    }

type error = string * int option

module RenameM = Monad.Make(struct
    type s = state
    type e = error
    let debug_info = None
end)
open RenameM

let declare name =
    M (fun (S state) ->
        let top_scope = List.hd state.renamings in
        let binding_opt = StringMap.find_opt name top_scope in
        match binding_opt with
        | Some _ ->
            failwith ("A binding with the name '" ^ name ^ "' has already been declared")
        | None ->
            let suffix = string_of_int state.next_id in
            let new_name = name ^ "_" ^ suffix in
            let top_scope' = StringMap.add name new_name top_scope in
            let renamings' = top_scope' :: List.tl state.renamings in
            let state' = S { state with
                renamings = renamings';
                next_id = state.next_id + 1 } in
            Ok (new_name, state'))
            
let line_mark ln (M monad) =
    M (fun env ->
        match monad env with
        | Ok res -> Ok res
        | Error(msg,None) -> Error(msg,Some ln)
        | error -> error
    )

let declare_many bindings =
    List.map declare bindings |> sequence >>>= return ()

let lookup_renaming name =
    let rec lookup name renamings =
        match renamings with
        | [] -> Error ("Undeclared binding: " ^ name)
        | scope :: scopes ->
            let new_name_opt = StringMap.find_opt name scope in
            match new_name_opt with
            | Some name' -> Ok name'
            | None -> lookup name scopes in
    M (fun (S state) ->
        match lookup name state.renamings with
        | Ok binding -> Ok (binding, S state)
        | Error msg -> Error (msg, None)
    )

let patterns_binds_equal patterns = 
    match patterns with
    | [] -> failwith "Empty pattern list"
    | h::t -> 
        let get_binds_set p = binds_from_pattern p |> List.map fst |> StringSet.of_list in
        let head_bind_set = get_binds_set h in
        List.for_all (fun p -> StringSet.equal head_bind_set (get_binds_set p)) t

let rec replace_pattern_binding pattern map = 
    match pattern with
    | P_Any (name, x) -> P_Any(StringMap.find name map, x) |> return
    | P_Wild 
    | P_Int _ 
    | P_Bool _ -> return pattern
    | P_Tuple (p0, p1, x) ->
        replace_pattern_binding p0 map >>= fun p0' ->
        replace_pattern_binding p1 map >>= fun p1' ->
        return (P_Tuple (p0', p1', x))
    | P_Cons (p0, p1, x) ->
        replace_pattern_binding p0 map >>= fun p0' ->
        replace_pattern_binding p1 map >>= fun p1' ->
        return (P_Cons (p0', p1', x))
    | P_Construct (name, p, x) ->
        replace_pattern_binding p map >>= fun p' -> return (P_Construct (name, p', x))

let rec rename_pattern_bindings pattern =
    match pattern with
    | P_Any (name, x) -> declare name >=> fun name' -> (P_Any (name', x), [name,name'])
    | P_Wild 
    | P_Int _ 
    | P_Bool _ -> return (pattern, [])
    | P_Tuple (p0, p1, x) ->
        rename_pattern_bindings p0 >>= fun (p0',rep0') ->
        rename_pattern_bindings p1 >>= fun (p1',rep1') ->
        return (P_Tuple (p0', p1', x), List.rev_append rep0' rep1')
    | P_Cons (p0, p1, x) ->
        rename_pattern_bindings p0 >>= fun (p0', rep0') ->
        rename_pattern_bindings p1 >>= fun (p1', rep1') ->
        return (P_Cons (p0', p1', x), List.rev_append rep0' rep1')
    | P_Construct (name, p, x) ->
        rename_pattern_bindings p >>= fun (p',rep) -> return (P_Construct (name, p', x), rep)

let push_scope =
    M (fun (S state) ->
        let state' = S { state with renamings = StringMap.empty :: state.renamings } in
        Ok ((), state'))

let pop_scope =
    M (fun (S state) ->
        let state' = S { state with renamings = List.tl state.renamings } in
        Ok ((), state'))

let rec rename_term (Term(ln,term)) =
    line_mark ln (
    match term with
    | Value value -> rename_value value >=> fun value' -> Term(ln, Value value')
    | Tuple (t0, t1) ->
        rename_term t0 >>= fun t0' ->
        rename_term t1 >>= fun t1' ->
        return (Term(ln, Tuple (t0', t1')))
    | App (t0, t1) ->
        rename_term t0 >>= fun t0' ->
        rename_term t1 >>= fun t1' ->
        return (Term(ln, App (t0', t1')))
    | Let (name, param_typ, let_term, in_term) ->
        push_scope >>>=
        declare name >>= fun name' ->
        push_scope >>>=
        rename_term let_term >>= fun let_term' ->
        pop_scope >>>=
        rename_term in_term >>= fun in_term' ->
        pop_scope >>>=
        return (Term(ln, Let (name', param_typ, let_term', in_term')))
    | Match (matched_term, alts) ->
        rename_term matched_term >>= fun matched_term' ->
        List.map (fun (patterns, term) ->
            match patterns_binds_equal patterns with
            | false -> fail ("Unequal bindings in patterns", Some ln)
            | true ->
                push_scope >>>=
                rename_pattern_bindings (List.hd patterns) >>= fun (pattern', reps) ->
                let replacements = StringMap.of_list reps in 
                list_map (fun p -> replace_pattern_binding p replacements) (List.tl patterns) >>= fun patterns' ->
                rename_term term >>= fun term' ->
                pop_scope >>>=
                return (pattern'::patterns', term')) alts
        |> sequence
        >>= fun alts' -> return (Term(ln, Match (matched_term', alts')))
    | Delay (clock, free_bindings, term) -> rename_term term >=> fun term' -> Term(ln, Delay (clock, free_bindings, term'))
    | Adv term -> rename_term term >=> fun term' -> Term(ln, Adv term')
    | Select (cl0, cl1, v0, v1) ->
        rename_value v0 >>= fun v0' ->
        rename_value v1 >>= fun v1' ->
        return (Term(ln, Select (cl0, cl1, v0', v1')))
    | Unbox term -> rename_term term >=> fun term' -> Term(ln, Unbox term')
    | Fix (name, term) ->
        lookup_renaming name >>= fun name' ->
        rename_term term >=> fun term' -> Term(ln, Fix (name', term'))
    | Never -> return (Term(ln, Never))
    | Read _ -> return (Term(ln, term))
    | SignalCons (head_term, tail_term) ->
        rename_term head_term >>= fun head_term' ->
        rename_term tail_term >>= fun tail_term' ->
        return (Term(ln, SignalCons (head_term', tail_term')))
    )

and rename_value (Val(ln,value)) =
    line_mark ln (
    match value with
    | Binding name ->
        lookup_renaming name >=> fun name' -> Val (ln, Binding name')
    | Unit
    | String _
    | Int _ -> return (Val (ln, value))
    | Lambda (param_name, param_typ, free_bindings, term) ->
        push_scope >>>=
        declare param_name >>= fun param_name' ->
        rename_term term >>= fun term' ->
        pop_scope >>>=
        return (Val (ln, Lambda (param_name', param_typ, free_bindings, term')))
    | Wait _ -> return (Val (ln, value))
    | Box (term, free_bindings) -> rename_term term >=> fun term' -> Val (ln, Box (term', free_bindings))
    | Bool _ -> return (Val (ln, value))
    | Construct (name, term) ->
        rename_term term >=> fun term' -> Val (ln, Construct (name, term'))
    )

let empty_state = S {
    renamings = [StringMap.empty];
    next_id = 0
}

let default_state =
    let S es = empty_state in
    let bindings =
        List.map (fun (Default binding) -> (binding.name, binding.name))
        defaults in
    S { es with
        renamings = [StringMap.of_list bindings]
    }

let rename_tops print_error absyn  =
    let rec aux tops acc =
        match tops with
        | [] -> return acc
        | top :: tops -> (
            match top with
            | TypeDef _ -> aux tops (top::acc)
            | TopBind (output_channel, term) ->
                rename_term term >>= fun term' ->
                let acc' = TopBind (output_channel, term') :: acc in
                aux tops acc'
            | TopLet (name, typ_opt, term) ->
                declare name >>= fun name' ->
                rename_term term >>= fun term' ->
                let acc' = TopLet (name', typ_opt, term') :: acc in
                aux tops acc') in
    let rename_m = aux absyn [] >=> List.rev in
    match eval_m rename_m default_state with
    | Ok (tops', _) -> tops'
    | Error(msg,ln) -> print_error msg ln ; raise_problem Other

