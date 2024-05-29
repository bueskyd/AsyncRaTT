open Exceptions
open Absyn
open Type_env
open Type_env_m
open Defaults

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)


(*
    Defines the API for the type system.
*)
module type TypeSystem = sig
    (* type type_definitions = (string * string list * typ) list *)
    val type_term : int term -> (typ * (int*typ)term)
    val type_value : int value -> (typ * (int*typ) value)
    val type_tops : (string -> int option -> unit) -> int top list -> (int*typ) top list	 
end


module Make (PE : Program_env.ProgramEnvironment) : TypeSystem = struct

(* type type_definitions = (string * string list * typ) list *)


let type_string_expanded typ = expand_type typ >>= fun typ -> type_string typ |> return

let print_type message typ =
    type_string_expanded typ >>= fun str -> print_endline (message ^ str); return typ

let try_pattern_match typ ln pattern = (* uses the first line of the match *)
    let rec aux typ pattern res =
        match res with
        | None -> None
        | Some acc -> match typ, pattern with
            | _, P_Any(name,_) -> Some((name, typ) :: acc, P_Any (name, (ln,typ)))
            | _, P_Wild -> Some (acc, P_Wild)
            | T_Fix (_, t), _ -> aux t pattern res
            | T_Int, P_Int n -> Some (acc, P_Int n)
            | T_Bool, P_Bool b -> Some (acc, P_Bool b)
            | T_Signal t, P_Cons(P_Any(head,_), P_Any(tail,_), _) ->
                    Some ([(head, t); (tail, T_Existential (T_Signal t))],
                    P_Cons (P_Any (head, (ln,t)), P_Any (tail, (ln,T_Existential (T_Signal t))), (ln, T_Signal t)))
            | T_Multiplicative(t1, t2), P_Tuple(p1, p2, _) -> (
                match aux t1 p1 res, aux t2 p2 res with
                | None, _ 
                | _, None -> None
                | Some (b0, p1'), Some (b1, p2') -> Some(b0 @ b1, P_Tuple (p1', p2', (ln,T_Multiplicative (t1, t2))))
            )
            | T_Additive(cons), P_Construct(name, p, _) -> (
                match List.find_opt (fun (n,t) -> n = name) cons with
                | Some(_, t) -> (
                    match aux t p res with
                    | Some (bindings, p) -> Some (bindings, P_Construct (name, p, (ln,t)))
                    | None -> None)
                | None -> None
            )
            (* Missing cases go here *)
            | _,_ -> None in
    aux typ pattern (Some [])

let specialize typ =
    let rec replace_type_vars typ specializations =
        expand_type typ >>= fun typ ->
        match typ with
        | T_Poly name -> (
            let specialization_opt = StringMap.find_opt name specializations in
            match specialization_opt with
            | Some specialization -> return (specialization, specializations)
            | None ->
                new_type_var >>= fun specialization ->
                    is_stable_required name >>= fun is_stable_required -> (
                        if is_stable_required
                        then require_stable specialization
                        else return ()) >>>=
                    let specializations' = StringMap.add name specialization specializations in
                    return (specialization, specializations'))
        | T_Unit
        | T_Bool
        | T_String
        | T_Int -> return (typ, specializations)
        | T_Multiplicative(a, b) ->
            replace_type_vars a specializations >>= fun (a', specializations') ->
            replace_type_vars b specializations' >>= fun (b', specializations'') ->
            return ((T_Multiplicative(a', b'), specializations''))
        | T_Named(ts,n) -> (
            if_type_fix n 
                (fun _ -> let typ = StringMap.fold (fun poly subst ty_acc -> type_substitution ty_acc poly subst) specializations typ in return (typ, specializations))
                (fun _ ->
                    let type_map = list_map (fun t -> replace_type_vars t specializations) ts in
                    type_map >>= fun m -> let (a,s) = List.split m in return (T_Named(a,n), List.hd s)
                )
        )
        | T_Additive ts ->
            let type_map = List.map (fun (_,t) -> replace_type_vars t specializations) ts |> sequence in
            let name_map = List.map (fun (n,_) -> return n) ts |> sequence in
            let map = map2 name_map type_map (fun a b ->
                let (ts,spec) = List.split b in 
                (List.combine a ts, spec)
            ) in
            map >>= fun (a,s) -> return (T_Additive a, List.hd s)
        | T_Function(a, b) ->
            replace_type_vars a specializations >>= fun (a', specializations') ->
            replace_type_vars b specializations' >>= fun (b', specializations'') ->
            return (T_Function(a', b'), specializations'')
        | T_Existential t ->
            replace_type_vars t specializations >>= fun (t', specializations') ->
            return ((T_Existential t', specializations'))
        | T_Universal t ->
            replace_type_vars t specializations >>= fun (t', specializations') ->
            return (T_Universal t', specializations')
        | T_Fix(s, t) ->
            type_fix s >>>=
            replace_type_vars t specializations >>= fun (t', specializations') ->
            type_unfix >>>=
            return (T_Fix (s, t'), specializations')
        | T_Boxed t ->
            replace_type_vars t specializations >>= fun (t', specializations') ->
            return (T_Boxed t', specializations') 
        | T_Signal t -> 
            replace_type_vars t specializations >>= fun (t', specializations') ->
            return (T_Signal t', specializations') 
    in
    let rec find_and_replace_typevars typ specializations =
        expand_type typ >>= fun typ ->
        match typ with
        | T_Poly _
        | T_Unit
        | T_Bool
        | T_String
        | T_Int -> return (typ, specializations)
        | T_Named(ts,n) -> 
            if_type_fix n
                (fun _ -> let typ = StringMap.fold (fun poly subst ty_acc -> type_substitution ty_acc poly subst) specializations typ in return (typ, specializations))
                (fun _ -> 
                    return (T_Named(List.map (fun t -> match t with 
                    | T_Poly s -> ( match StringMap.find_opt s specializations with
                        | Some t -> t
                        | None -> t
                    )
                    | _ -> t
                    ) ts,n), specializations)
                )
        | T_Multiplicative(a, b) ->
            find_and_replace_typevars a specializations >>= fun (a', specializations) ->
            find_and_replace_typevars b specializations >>= fun (b', specializations) ->
            return (T_Multiplicative(a', b'), specializations)
        | T_Additive ts ->
            let type_map = list_map (fun (_,t) -> find_and_replace_typevars t specializations) ts in
            let name_map = list_map (fun (n,_) -> return n) ts in
            let map = map2 name_map type_map (fun a b ->
                let (ts,spec) = List.split b in 
                (List.combine a ts, spec)
            ) in
            map >>= fun (a,s) -> return (T_Additive a, List.hd s)
        | T_Function(a, b) ->
            replace_type_vars a specializations >>= fun (a', specializations) ->
            replace_type_vars b specializations >>= fun (b', specializations) ->
            return (T_Function(a', b'), specializations)
        | T_Existential t ->
            find_and_replace_typevars t specializations >>= fun (t', specializations) ->
            return (T_Existential t', specializations)
        | T_Universal t ->
            find_and_replace_typevars t specializations >>= fun (t', specializations) ->
            return (T_Universal t', specializations)
        | T_Fix(s, t) ->
            type_fix s >>>=
            find_and_replace_typevars t specializations >>= fun (t', specializations) ->
            type_unfix >>>=
            return (T_Fix (s, t'), specializations)
        | T_Boxed t ->
            find_and_replace_typevars t specializations >>= fun (t', specializations) ->
            return (T_Boxed t', specializations)
        | T_Signal t ->
            find_and_replace_typevars t specializations >>= fun (t', specializations) ->
            debug_print ("signal: "^type_string t^"->"^type_string t') >>>=
            return (T_Signal t', specializations) 
        in
        expand_type typ >>= fun typ ->
        debug_print ("specializing: " ^ type_string typ) >>>=
        find_and_replace_typevars typ StringMap.empty >>= (fun (typ, _) -> return typ)

let rec fix_into typ = match typ with
    | T_Poly _
    | T_Unit
    | T_String
    | T_Int -> typ
    | T_Multiplicative (t0, t1) -> T_Multiplicative (fix_into t0, fix_into t1)
    | T_Additive cases ->
        let fixed_cases =
            List.map (fun (name, typ) -> (name, fix_into typ)) cases in
        T_Additive fixed_cases
    | T_Function (arg_type, ret_type) ->
        T_Function(fix_into arg_type, fix_into ret_type)
    | T_Existential T_Fix (type_name, typ) -> typ
    | T_Existential typ ->
        T_Existential (fix_into typ)
    | T_Universal typ -> T_Universal (fix_into typ)
    | T_Fix (type_name, typ) -> T_Fix (type_name, fix_into typ)
    | T_Boxed typ -> T_Boxed (fix_into typ)
    | T_Named (types, name) -> typ
    | T_Bool -> typ
    | T_Signal _ -> typ

let fix_out typ =
    let rec replace_named typ0 =
        match typ0 with
        | T_Poly _
        | T_Unit
        | T_String
        | T_Int -> typ0
        | T_Multiplicative (t0, t1) -> T_Multiplicative (replace_named t0, replace_named t1)
        | T_Additive cases ->
            let fixed_cases =
                List.map (fun (name, typ0) -> (name, replace_named typ0)) cases in
            T_Additive fixed_cases
        | T_Function (arg_type, ret_type) ->
            T_Function(replace_named arg_type, replace_named ret_type)
        | T_Existential T_Fix (type_name, typ0) -> typ0
        | T_Existential typ0 ->
            T_Existential (replace_named typ0)
        | T_Universal typ0 -> T_Universal (replace_named typ0)
        | T_Fix (typ0e_name, typ0) -> T_Fix (typ0e_name, replace_named typ0)
        | T_Boxed typ0 -> T_Boxed (replace_named typ0)
        | T_Named (typ0es, name) -> T_Existential typ
        | T_Bool -> typ0 
        | T_Signal _ -> typ0
    in
    match typ with
    | T_Fix (type_name, typ) -> Ok(replace_named typ)
    | _ -> Error "Cannot have non-T_Fix type in an out"

let rec attach_explicit_arg_types typ (Term(ln,t)) : int term = match typ, t with
    | T_Function(arg_ty,ret_ty), Value(Val(ln,Lambda(arg, None, free_bindings, body))) ->
        Value(Val(ln,Lambda(arg, Some arg_ty, free_bindings, attach_explicit_arg_types ret_ty body))) |> term ln
    | T_Function(arg_ty,ret_ty), Fix(fn,Term(ln',Value(Val(ln,Lambda(arg, None, free_bindings, body))))) ->
        Fix(fn,Term(ln',Value(Val(ln, Lambda(arg, Some arg_ty, free_bindings, attach_explicit_arg_types ret_ty body))))) |> term ln
    | _ -> t |> term ln

let unify_type_list ty lst =
    let rec aux ty lst = (match lst with
        | [] -> return ty
        | h::t -> unify ty h >>= fun (res,_) -> aux ty t)
    in 
    aux ty lst

let pattern_binds_type_equal (binds : (string * typ) list list) : unit type_env_m =
    match binds with
    | [] -> fail ("No pattern binds", Typing, None)
    | h::t -> 
        let binding_set binds = StringSet.of_list (List.map fst binds) in
        let bind_set = binding_set h in
        if not(List.for_all (fun a -> StringSet.equal bind_set (binding_set a)) t) then fail ("Unequal binding set", Typing, None)
        else let type_map = StringMap.of_list h in
        list_map (fun bs -> list_map (fun (n,t) -> unify t (StringMap.find n type_map)) bs) t >>>= return ()

let rec pattern_type pat =
    match pat with
    | P_Wild -> new_type_var
    | P_Any(name,_) -> new_type_var
    | P_Int n -> return T_Int
    | P_Bool b -> return T_Bool
    | P_Tuple(p0, p1, _) -> 
        pattern_type p0 >>= fun t0 ->
        pattern_type p1 >>= fun t1 ->
        return (T_Multiplicative (t0, t1))
    | P_Cons(p_hd, p_tl, _) ->
        pattern_type p_hd >>= fun t ->
        return (T_Signal t)
    | P_Construct(name, p, _) ->
        pattern_type p >>= fun t ->
        lookup_constructor_type name t

let typed_term typ ln t = (typ,Term((ln,typ),t))
let typed_val typ ln v = (typ,Val((ln,typ),v))

let rec infer_term_type (Term(ln,t)) : (typ * (int*typ)term) type_env_m =
    line_mark ln (
    match t with
    | Value v -> infer_value_type v >=> fun (typ, v') -> typed_term typ ln (Value(v'))
    | Tuple (t0, t1) ->
        infer_term_type t0 >>= fun (ty0, t0') -> 
        infer_term_type t1 >>= fun (ty1, t1') ->
            let typ = T_Multiplicative(ty0, ty1) in
            return (typed_term typ ln (Tuple(t0', t1')))
    | App (t0, t1) ->
        debug_print "infer App" >>>=
        infer_term_type t0 >>= fun (fn_ty, t0') ->
        infer_term_type t1 >>= fun (arg_ty, t1') ->
        new_type_var >>= fun ret_typ ->
        unify fn_ty (T_Function(arg_ty, ret_typ)) >>= fun (u_typ, _) ->
        return (typed_term ret_typ ln (App(t0', t1')))
    | Let (name, typ_opt, rhs_term, in_term) -> (
        let rhs_term = match typ_opt with 
            | Some ty -> attach_explicit_arg_types ty rhs_term
            | None -> rhs_term 
        in (
        debug_print "infer Let" >>>=
        match typ_opt with
        | Some typ -> return typ
        | None -> new_type_var) >>= fun var_typ ->
        add_var name var_typ
        >>>= push_scope >>>= (
            let Term (_, rhs_term_inner) = rhs_term in
            match rhs_term_inner with
            | Fix _ -> enter_local_function (infer_term_type rhs_term)
            | _ -> infer_term_type rhs_term
        )
        >>= fun (rhs_typ, rhs_term') ->
        debug_print ("rhs: "^type_string rhs_typ)>>>=
        pop_scope
        >>>= unify var_typ rhs_typ
        >>>= infer_term_type in_term >=> fun (in_typ, in_term') -> (typed_term in_typ ln (Let(name, Some var_typ, rhs_term', in_term'))))
    | Match(t, alts) -> ( 
        debug_print "infer Match" >>>=
        list_map (fun (p, _) -> list_map pattern_type p) alts
        >>= fun type_of_patterns ->
        let type_of_patterns = List.flatten type_of_patterns in
        infer_term_type t >>= fun (matched_type, matched_term') ->
        unify_type_list matched_type type_of_patterns >>= fun matched_type ->
        expand_type matched_type >>= fun matched_type ->
                list_map (fun (pats,t) -> 
                    let infos = List.map (fun p -> (
                        match try_pattern_match matched_type ln p with
                        | Some info -> Some(info)
                        | None -> None)
                    ) pats
                    in
                    if List.mem None infos then failwith ("Patterns could not unify")
                    else let (binds, typed_pats) = List.map Option.get infos |> List.split in
                    pattern_binds_type_equal binds >>>= return (t, List.hd binds, typed_pats)
                ) alts 
            >>= fun alt_infos ->
                match alt_infos with (* Also check if patterns are correct, and infer the matched term *)
                | [] -> fail ("Pattern matching with no viable alternatives",Typing,Some ln)
                | [term, binds, typed_patterns] ->
                    push_scope >>>=
                    add_vars binds >>= fun _ ->
                    infer_term_type term >>= fun (alt_typ, term') ->
                    pop_scope >>>=
                    let match_term' =
                        Match (matched_term', [(typed_patterns, term')]) in
                    return (typed_term alt_typ ln match_term')
                | (term, binds, typed_patterns) :: t ->
                    push_scope >>>=
                    add_vars binds >>>=
                    infer_term_type term >>= fun (hd_ty, term') -> 
                    pop_scope >>= fun _ ->
                    list_map (fun (term, binds, typed_patterns) ->
                        push_scope >>>=
                        add_vars binds >>>=
                        infer_term_type term >>= fun (ty, term') ->
                        pop_scope >>>=
                        return (ty, term')) t
                    >=> List.split
                    >>= fun (ty_seq, terms') ->
                    fold_left (fun acc ty ->
                    type_equal ty hd_ty >>= fun res -> return (res && acc)) true ty_seq >>= fun alts_eq ->
                        if alts_eq
                        then
                            let typed_patterns = typed_patterns :: List.map (fun (_, _, typed_pattern) -> typed_pattern) t in
                            let terms'' = term' :: terms' in
                            let alts' = List.combine typed_patterns terms'' in
                            return (typed_term hd_ty ln (Match(matched_term', alts')))
                        else fail ("Alternatives of differing types: "^type_string hd_ty,Typing,Some ln)
    ) 
    | Delay(clock, free_bindings, t) ->
        debug_print "infer Delay" >>>=
            (*if StringSet.is_empty clock then fail ("Empty clock: "^term_string t,Clocking,Some ln) *)
            (
                tick >>>= 
                infer_term_type t >>= fun (term_typ, t') -> 
                untick >>>= 
                let typ = T_Existential term_typ in
                return (typed_term typ ln (Delay(clock, free_bindings, t')))
            )
    | Adv Term(_,Value(Val(vln, Binding n))) -> (
        adv_time (
            lookup_before n >>= fun b_opt -> match b_opt with
            | Some b -> (
                specialize b.typ >>= fun b_typ ->
                new_type_var >>= fun new_type_var ->
                unify b_typ (T_Existential new_type_var) >>>=
                return (typed_term new_type_var ln (Adv(Term((ln,b_typ), Value(Val((vln, b_typ), Binding n)))))))
            | None -> fail ("Could not find "^n,Other,Some ln)))
    | Adv Term(_,Value v) ->
        debug_print "infer Adv" >>>=
        adv_time ( 
            infer_value_type v >>= fun (typ, v') ->
            new_type_var >>= fun new_type_var ->
            unify typ (T_Existential new_type_var) >>>=
            return (typed_term new_type_var ln (Adv(Term((ln, typ), Value v')))))
    | Adv _ -> fail ("Cannot advance a term",Typing,Some ln)
    | Select (_, _, v1, v2) ->
        debug_print "infer Select" >>>=
        adv_time (
            infer_value_type v1 >>= fun (v1_type, v1') ->
            infer_value_type v2 >>= fun (v2_type, v2') ->
            new_type_var >>= fun nt1 ->
            unify v1_type (T_Existential nt1) >>>=
            new_type_var >>= fun nt2 ->
            unify v2_type (T_Existential nt2) >>>=
            let typ = T_Named ([nt1; nt2], "selection") in
            return (typed_term typ ln (Select(empty_clock_set, empty_clock_set, v1', v2'))))
    | Unbox t ->
        debug_print "Infer unbox" >>= fun _ ->
        infer_term_type t >>= fun (term_typ, t') ->
        new_type_var >>= fun new_type_var ->
        unify term_typ (T_Boxed new_type_var) >>= fun (term_typ', _) -> (
        match term_typ' with
        | T_Boxed term_typ'' -> return (typed_term term_typ'' ln (Unbox t'))
        | _ -> fail ("Type " ^ type_string term_typ' ^ " is not boxed", Typing, Some ln))
    | Fix(name, term) ->
        debug_print ("infer Fix."^name) >>>=
        fix name
        >>>= infer_term_type term
        >>= fun (ty, term') ->
        unfix
        >>>= 
        lookup_before name >>= fun bo -> (match bo with
            | Some b -> unify b.typ ty
            | None -> (Printf.printf "Fix failed violently... sorry" ; raise_problem Other )
        ) >>>= return (typed_term ty ln (Fix (name, term')))
    | Never -> 
        debug_print "infer Never" >>>= 
        new_type_var >>= fun typ_var ->
        let typ = T_Existential typ_var in
        return (typed_term typ ln Never)
    | Read c ->
        if PE.is_buffered_channel c
        then
            let buffer_type = PE.input_channel_type c in
            return (typed_term buffer_type ln (Read c))
        else fail ("Reading on non-buffered channel",Other,Some ln)
    | SignalCons(t0, t1) -> (
        infer_term_type t0 >>= fun (ty0, t0') ->
        infer_term_type t1 >>= fun (ty1, t1') -> 
            let tail_type = T_Existential(T_Signal ty0) in
            unify ty1 tail_type >>>=
            let signal_typ = T_Signal ty0 in
            return (typed_term signal_typ ln (SignalCons(t0', t1')))))

and infer_value_type (Val(ln,v) : int value) : (typ * (int*typ)value) type_env_m =
    line_mark ln (
    match v with
    | Binding name ->
        debug_print ("lookup "^name) >>>= (
            if_tick_free (
            lookup_before name >>= fun binding ->
                match binding with
                | None -> fail ("Could not find: "^name,Other,Some ln)
                | Some b ->
                    type_string_expanded b.typ >>= fun str ->
                    debug_print ("found: "^type_string b.typ) >>>=
                    specialize b.typ >>= fun typ' -> return (typ', b.top_level, b.declared_in_normal_context, b.declared_outside_local_recursive)) (
            lookup_after name >>= (fun binding ->
                match binding with
                | Some b ->
                    is_context_stable >>= fun is_context_stable ->
                        debug_print ("found: "^type_string b.typ) >>>=
                        specialize b.typ >>= fun typ' -> return (typ', b.top_level, b.declared_in_normal_context, b.declared_outside_local_recursive)
                | None -> (
                    lookup_before name >>= fun binding -> (
                        match binding with
                        | None -> fail ("Could not find: "^name,Other,Some ln)
                        | Some b ->
                            specialize b.typ >>= fun typ' -> return (typ', b.top_level, b.declared_in_normal_context, b.declared_outside_local_recursive))))))
        >>= fun (typ, top_level, declared_in_normal_context, declared_outside_local_recursive) ->
            (if_fix name
                (fun _ ->
                    if_tick_free
                        (return (T_Universal typ))
                        (return typ))
                (fun _ ->
                    expand_type typ >>= fun typ ->
                    is_context_stable >>= fun is_context_stable -> 
                    is_in_local_function >>= fun is_in_local_function -> (
                    if_tick_free (return false) (return true) >>= fun ticked_context ->
                    let stable_or_ticked = is_context_stable || ticked_context in
                    let x = stable_or_ticked && declared_in_normal_context in
                    let y = is_in_local_function && declared_outside_local_recursive in
                    let z = x || y in
                    match typ, top_level, z with
                    | T_Boxed t, true, _ -> return t
                    | T_Boxed t, false, false -> return typ
                    | T_Boxed t, false, true -> require_stable typ >>>= return typ
                    | _, true, _ -> fail ("Toplevel definition " ^ name ^ " of type " ^ type_string typ ^ " must be stable", Stability, Some ln)
                    | _, false, true -> require_stable typ >>>= return typ
                    | _, false, false -> return typ))) >>= fun typ ->
            specialize typ >>= fun typ ->
            return (typed_val typ ln (Binding name))
    | Unit -> return (typed_val T_Unit ln Unit)
    | Int n -> return (typed_val T_Int ln (Int n))
    | Bool b -> return (typed_val T_Bool ln (Bool b))
    | String str -> return (typed_val T_String ln (String str))
    | Construct (n, t) ->
        infer_term_type t >>= fun (ty, t') ->
        lookup_constructor_type n ty >=> fun c_typ -> (typed_val c_typ ln (Construct(n, t')))
    | Lambda (param_name, param_typ_opt, free_bindings, body) ->
        get_tick >>= fun has_tick ->
            if has_tick then
                fail ("Cannot create a lambda when there is a tick in the context",Typing,Some ln)
            else (
                match param_typ_opt with
                | Some param_typ ->
                    add_type_to_env param_typ >>>=
                    push_scope >>>=
                    add_var param_name param_typ >>>=
                    infer_term_type body >>= fun (body_type, body') ->
                    pop_scope >>>=
                    let lambda_type = T_Function(param_typ, body_type) in
                    return (typed_val lambda_type ln (Lambda(param_name, Some param_typ, free_bindings, body')))
                | None ->
                    new_type_var >>= fun param_typ ->
                    push_scope >>>=
                    add_var param_name param_typ >>>=
                    infer_term_type body >>= fun (body_type, body') ->
                    pop_scope >>>=
                    expand_type (T_Function(param_typ, body_type)) >>>=
                    let lambda_type = T_Function(param_typ, body_type) in
                    return (typed_val lambda_type ln (Lambda(param_name, Some param_typ, free_bindings, body'))))
    | Wait c ->
        if PE.is_push_channel c
        then
            let channel_type = T_Existential(PE.input_channel_type c) in
            return (typed_val channel_type ln (Wait c))
        else fail ("Waiting on non-push channel",Typing,Some ln)
    | Box (t, free_bindings) ->
        debug_print ("Infer Box") >>>=
        box (infer_term_type t) >>= fun (term_type, t') ->
        let typ = T_Boxed term_type in
        return (typed_val typ ln (Box (t', free_bindings))))

let rec expand_all_pattern_types pattern =
    match pattern with
    | P_Wild -> return P_Wild
    | P_Any(name, (ln,typ)) -> expand_type typ >=> fun typ' -> P_Any(name, (ln,typ'))
    | P_Int _
    | P_Bool _ -> return pattern
    | P_Tuple(p0, p1, (ln,typ)) ->
        expand_type typ >>= fun typ' ->
        expand_all_pattern_types p0 >>= fun p0' ->
        expand_all_pattern_types p1 >>= fun p1' ->
        return (P_Tuple(p0', p1', (ln,typ')))
    | P_Cons(p_head, p_tail, (ln,typ)) ->
        expand_type typ >>= fun typ' ->
        expand_all_pattern_types p_head >>= fun p_head' ->
        expand_all_pattern_types p_tail >>= fun p_tail' ->
        return (P_Cons(p_head', p_tail', (ln,typ')))
    | P_Construct(name, pattern, (ln,typ)) ->
        expand_type typ >>= fun typ' ->
        expand_all_pattern_types pattern >>= fun pattern' ->
        return (P_Construct(name, pattern', (ln,typ')))

let rec expand_all_term_types (Term((ln,ty),term)) =
    expand_type ty >>= fun ty' -> 
    match term with
    | Value v ->
        expand_all_value_types v >>= fun v' ->
        return (Term((ln,ty'),Value v'))
    | Tuple (t1, t2) ->
        expand_all_term_types t1 >>= fun t1' ->
        expand_all_term_types t2 >>= fun t2' ->
        return (Term((ln,ty'), Tuple(t1', t2')))
    | Let(name, binding_typ, t1, t2) -> (
        match binding_typ with
        | None -> None |> return 
        | Some b_ty -> expand_type b_ty >>= fun b_ty' -> Some b_ty' |> return)
        >>= fun binding_typ' ->
        expand_all_term_types t1 >>= fun t1' ->
        expand_all_term_types t2 >>= fun t2' ->
        return (Term((ln,ty'), Let(name, binding_typ', t1', t2')))
    | App(t1, t2) ->
        expand_all_term_types t1 >>= fun t1' ->
        expand_all_term_types t2 >>= fun t2' ->
        return (Term((ln,ty'), App(t1', t2')))
    | Delay(clock, free_bindings, t) ->
        expand_all_term_types t >>= fun t' ->
        return (Term((ln,ty'), Delay(clock, free_bindings, t')))
    | Adv t ->
        expand_all_term_types t >>= fun t' ->
        return (Term((ln,ty'), Adv t'))
    | Unbox t ->
        expand_all_term_types t >>= fun t' ->
        return (Term((ln,ty'), Unbox t'))
    | Fix(name, t) ->
        expand_all_term_types t >>= fun t' ->
        return (Term((ln,ty'), Fix(name, t')))
    | Match(t, alts) ->
        expand_all_term_types t >>= fun t' ->
        List.map (fun (pattern, term) ->
            expand_type ty >>= fun ty' ->
            expand_all_term_types term >>= fun term' ->
            list_map expand_all_pattern_types pattern >>= fun pattern_typ' ->
            return (pattern_typ', term')) alts
        |> sequence
        >>= fun alts' ->
        return (Term((ln,ty'), Match(t', alts')))
    | Select(cl0, cl1, v1, v2) ->
        expand_all_value_types v1 >>= fun v1' ->
        expand_all_value_types v2 >>= fun v2' ->
        return (Term((ln,ty'), Select(cl0, cl1, v1', v2')))
    | Never -> Term((ln,ty'), Never ) |> return
    | Read buffer_name -> Term((ln,ty'), Read buffer_name) |> return
    | SignalCons(t1, t2) ->
        expand_all_term_types t1 >>= fun t1' ->
        expand_all_term_types t2 >>= fun t2' ->
        return (Term((ln,ty'), SignalCons(t1', t2')))

and expand_all_value_types (Val((ln,ty),value)) =
    expand_type ty >>= fun ty' -> 
    match value with
    | Binding v ->
        return (Val((ln,ty'), Binding v))
    | Unit -> return (Val((ln,ty'), Unit))
    | Lambda(param_name, param_typ, free_bindings, term) -> (
        match param_typ with
        | None -> return None
        | Some p_ty -> expand_type p_ty >>= fun p_ty' -> Some p_ty' |> return
        ) >>= fun param_typ' ->
        expand_all_term_types term >>= fun term' ->
        return (Val((ln,ty'),Lambda(param_name, param_typ', free_bindings, term')))
    | Bool _  
    | String _
    | Int _ -> return (Val((ln,ty'),value))
    | Construct(name, t) ->
        expand_all_term_types t >>= fun t' ->
        return (Val((ln,ty'), Construct(name, t')))
    | Wait channel_name ->
        return (Val((ln,ty'), Wait channel_name))
    | Box (t, free_bindings) ->
        expand_all_term_types t >>= fun t' ->
        return (Val((ln,ty'), Box (t', free_bindings)))

let default_bindings : (string * binding) list =
    List.map (fun (Default info) ->
        (info.name,
        {
            typ = info.typ;
            top_level = true;
            declared_in_normal_context = true;
            declared_outside_local_recursive = true })) defaults

let infer_and_expand_term_types term =
    infer_term_type term >>= fun (typ, term') ->
    expand_type typ >>= fun typ' ->
    expand_all_term_types term' >>= fun term'' ->
    return (typ', term'')

let infer_and_expand_value_types value =
    infer_value_type value >>= fun (typ, value') ->
    expand_type typ >>= fun typ' ->
    expand_all_value_types value' >>= fun value'' ->
    return (typ', value'')

let add_type_constructs name (polys,typ) acc =
    let rec append_constructs cons acc = match cons with
        | [] -> acc
        | (cn,ty)::t -> append_constructs t (StringMap.add cn (name,polys,ty) acc)
    in
    match typ with
    | T_Fix(_,T_Additive cons)
    | T_Additive cons -> append_constructs cons acc
    | _ -> acc

let add_polys typ acc =
    let rec extract t acc = match t with
    | T_Poly a -> StringMap.add a (T_Poly a) acc
    | T_Unit
    | T_Bool
    | T_String
    | T_Int -> acc
    | T_Additive ts -> List.fold_left (fun acc (_,t) -> extract t acc) acc ts
    | T_Function(t0,t1)
    | T_Multiplicative(t0,t1) -> extract t0 (extract t1 acc)
    | T_Existential t 
    | T_Universal t 
    | T_Fix(_,t)
    | T_Signal t
    | T_Boxed t -> extract t acc
    | T_Named _ -> acc (* I dont think this is correct *)
    in
    extract typ acc

let type_tops print_error tops = 
    let rec aux tops acc env = match tops with
        | [] -> acc
        | h::t -> ( match h with
            | TypeDef(n,ps,ty) -> (
                aux t (TypeDef(n,ps,ty)::acc) ({ env with 
                    type_defs = StringMap.add n (ps,ty) env.type_defs;
                    type_constructs = add_type_constructs n (ps,ty) env.type_constructs;
                    type_vars = add_polys ty env.type_vars;
                })
            )
            | TopBind(oc, term) -> (
                let type_env_m =
                    infer_and_expand_term_types term >>= fun result ->
                    check_stability >>>= return result in
                match eval_type_env_m type_env_m env with
                | Error(msg, p, _) -> print_endline msg; raise_problem p
                | Ok(term_type, term', env') -> (
                    match term_type with
                    | T_Signal sig_type -> ( 
                        match PE.output_channel_type oc with
                        | Some oct -> (
                            match eval_env_m (type_equal sig_type oct) env' with 
                            | Error(msg,p,_) -> raise_problem p
                            | Ok(type_eq,_) -> 
                                let h' = TopBind(oc, term') in
                                if type_eq then aux t (h'::acc) env'
                                else (Printf.printf "Cannot bind a signal of type '%s' to an output channel of type '%s'" (type_string sig_type) (type_string(T_Signal oct)); raise_problem Typing)
                            )
                        | None -> (
                            let h' = TopBind(oc, term') in
                            aux t (h'::acc) env'
                        )
                    )
                    | _ -> Printf.printf "Cannot bind a non-signal type to an output channel: %s\n" (type_string term_type); raise_problem Typing
                )
            )
            | TopLet(name, None, (Term(ln,_) as term)) ->
                let tem = 
                    new_type_var >>= fun typ ->
                    add_top_level name typ >>>=
                        line_mark ln (infer_and_expand_term_types term >>= fun result ->
                        check_stability >>>= add_top_level name (T_Boxed (fst result)) >>>= return result)
                in
                (match eval_type_env_m tem env with
                | Error(msg,p,ln) -> print_error msg ln ; raise_problem p
                | Ok(ty, term', env') -> (
                    let h' = TopLet (name, Some ty, term') in
                    aux t (h'::acc) env'
                ))
            | TopLet(name, Some ex_ty, (Term(ln,_) as term)) -> 
                let term = attach_explicit_arg_types ex_ty term in
                let tem = 
                    add_type_to_env ex_ty >>>=
                    add_top_level name ex_ty >>>= 
                    line_mark ln (infer_and_expand_term_types term >>= fun result ->
                        check_stability >>>= add_top_level name (T_Boxed (fst result)) >>>= return result)
                in
                let (ty, term', env') = match eval_type_env_m tem env with
                    | Error(msg,p,ln) -> print_error msg ln ; raise_problem p
                    | Ok res -> res
                in
                let teqm = 
                    unify ty ex_ty >=> fun (t, _) -> t in
                    let ty = match eval_env_m teqm env' with
                        | Error(msg,p,ln) -> print_error msg ln; raise_problem p
                        | Ok(res,_) -> res
                in 
                let h' = TopLet (name, Some ty, term') in
                aux t (h'::acc) env'
        )
    in
    let env = { (empty_env default_types) with 
        context = ([StringMap.of_list (default_bindings)], None);
    }
    in
    let tops' = aux tops [] env |> List.rev in
    let at_least_one_output_channel_binding =
        List.exists (fun top ->
            match top with
            | TopBind _ -> true
            | _ -> false) tops' in
    if at_least_one_output_channel_binding
    then tops'
    else (print_error "A valid program must write to at least one output channel" None ; raise_problem Other)

let type_term term = 
    match eval_type_env_m (infer_and_expand_term_types term) (empty_env default_types) with
    | Error(msg,p,_) -> raise_problem p
    | Ok(typ, term', _) -> (typ, term')

let type_value value = 
    match eval_type_env_m (infer_and_expand_value_types value) (empty_env default_types) with
    | Error(msg,p,_) -> raise_problem p
    | Ok(typ, value', _) -> (typ, value')
    
end
