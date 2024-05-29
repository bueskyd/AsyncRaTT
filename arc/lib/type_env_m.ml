open Absyn
open Exceptions
open Type_env

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type error = string * problem * int option

module TypeM = Monad.Make(struct
    type s = type_env
    type e = error 
    let debug_info = Some (fun s ->  
        let fix_string =
            "[" ^ (List.map (fun x -> x) s.fix |> String.concat ", ") ^ "]" in
        let type_fix_string = if Option.is_some s.type_fix then Option.get s.type_fix else "_" in
        let info = Printf.sprintf "fix: %s, tfix: %s\n%!" fix_string type_fix_string in
        info
    )
end)
open TypeM

type 'a type_env_m = 'a TypeM.monad 

let (>>=) = TypeM.(>>=)
let (>>>=) = TypeM.(>>>=)
let (>=>) = TypeM.(>=>)
let fail = TypeM.fail
let return = TypeM.return
let join = TypeM.join
let map = TypeM.map
let map2 = TypeM.map2
let combine = TypeM.combine
let sequence = TypeM.sequence
let list_map = TypeM.list_map
let fold_left = TypeM.fold_left
let undo = TypeM.undo
let eval_m = TypeM.eval_m
let debug_print = TypeM.debug_print

let extract_type_defs tdefs = 
    let rec aux tds acc = match tds with
        | [] -> acc
        | h::t -> ( match h with
            | (n,polys,ty) -> aux t ((n,(polys,ty))::acc)
        )
    in 
    aux tdefs []

let line_mark ln (M monad) =
    M (fun env ->
        match monad env with
        | Ok res -> Ok res
        | Error(msg,p,None) -> Error(msg,p,Some ln)
        | error -> error
    )

let extract_type_constructs tdefs =
    let rec append_constructors type_name polys cons acc = match cons with
        | [] -> acc
        | (n,ty)::t -> append_constructors type_name polys t ((n,(type_name,polys,ty))::acc)
    in
    let rec aux tds acc = match tds with
    | [] -> acc
    | h::t -> ( match h with
        | (n,polys,T_Fix(_,T_Additive cons))
        | (n,polys,T_Additive cons) -> aux t (append_constructors n polys cons acc)
        | (_,_,_) -> aux t acc
    )
    in 
    aux tdefs []

let extract_poly_types typ =
    let rec extract t acc = match t with
        | T_Poly a -> StringSet.add a acc
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
        | T_Named _ -> acc in
    extract typ StringSet.empty

let extract_top_def_poly_types tdefs =
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
    let rec aux tds acc =
        match tds with
        | [] -> acc
        | h::t -> (
            match h with
            | (_,_,ty) -> aux t (extract ty acc))
    in 
    aux tdefs StringMap.empty

let empty_env tdefs = 
    {
        type_vars = extract_top_def_poly_types tdefs;
        next_type_var_id = 0;
        type_defs = StringMap.of_list (extract_type_defs tdefs);
        type_constructs = StringMap.of_list (extract_type_constructs tdefs);
        type_fix = None;
        fix = [];
        context = ([StringMap.empty], None);
        required_stable = StringSet.empty;
        is_stable = false;
        in_local_function = false
    }

let entire_context env =
    match env.context with
    | (ve, None) -> ve
    | (ve, Some ve') -> ve @ ve'

let tick =
    M (fun env ->
        match env.context with
        | (ve, Some _) -> Error("There can be at most one tick in a context",Typing,None)
        | (ve, None) -> Ok((), { env with context = (ve, Some [StringMap.empty]) })
    )

let get_tick =
    M (fun env -> 
        Ok (env.context |> snd |> Option.is_some, env))

let untick =
    M (fun env -> 
        match env.context with
        | (_, None) -> Error("There was no tick to look before",Other,None)
        | (ve, Some _) -> Ok((),{ env with context = (ve, None) })
    )

let if_tick_free (M tma) (M tmb) =
    M (fun env -> match env.context with
        | ve, None -> tma env
        | ve, Some ve' -> tmb env
    )

let rec lookup_varenv name vars =
    match vars with
    | [] -> None
    | scope :: scopes ->
        let var_opt = StringMap.find_opt name scope in
        match var_opt with
        | Some binding -> var_opt
        | None -> lookup_varenv name scopes 

let lookup_before name =
    M (fun env -> 
        let var_env = match env.context with
            | ve, _ -> ve
        in
        Ok(lookup_varenv name var_env, env)
    )

let lookup_after name =
    M (fun env -> 
        match env.context with
        | _, Some ve -> Ok(lookup_varenv name ve, env)
        | _, _ -> Error("No tick to look after",Other,None)
    )

let fix name =
    M (fun env ->
        let env' = { env with fix = name :: env.fix } in
        Ok((), env')
    )

let get_fix_name =  
    M (fun env ->
        let str = match env.type_fix with
        | Some n -> n
        | None -> "none"
        in
        Ok(str, env)
    )

let unfix =
    M (fun env ->
        let env' = { env with fix = List.tl env.fix } in
        Ok((), env')
    )

let type_fix name =
    M (fun env ->
        let env' = { env with type_fix = Some name } in
        Ok((), env')
    )

let get_type_fix_name =  
    M (fun env ->
        let str = match env.type_fix with
        | Some n -> n
        | None -> "none"
        in
        Ok(str, env)
    )

let type_unfix =
    M (fun env ->
        let env' = { env with type_fix = None } in
        Ok((), env')
    )

let if_fix name (f_tm1) (f_tm2)  =
    M (fun env ->
        let M tm =
            match List.find_opt (fun n -> n = name) env.fix with
            | Some _ -> f_tm1 ()
            | None -> f_tm2 ()
        in
        tm env
    )

let if_type_fix name (f_tm1) (f_tm2)  =
    M (fun env ->
        let M tm = match env.type_fix with
        | Some n when name = n -> f_tm1 ()
        | _ -> f_tm2 ()
        in
        tm env
    )

let enter_local_function (M tm) =
    M (fun env ->
        let previously_in_local_function = env.in_local_function in
        let env' = { env with in_local_function = true } in
        match tm env' with
        | Ok(res, env'') ->
            Ok(res, { env'' with in_local_function = previously_in_local_function })
        | Error e -> Error e
    )

let is_in_local_function =
    M (fun env ->
        Ok (env.in_local_function, env))

let adv_time (M tm) = 
    M (fun env ->
        match env.context with
        | _, None -> Error("Advance outside delay",Typing,None)
        | ve, Some _ -> ( let adv_env = { env with context = (ve, None)} in    
            match tm adv_env with
            | Ok(res,env') -> Ok(res, { env' with context = (fst env'.context, snd env.context) })
            | Error e -> Error e
        )
    )

let box (M m) =
    M (fun env ->
        if env.is_stable then Error ("Cannot have a box in a box", Other, None)
        else
            let stable_env = { env with is_stable = true } in
            match m stable_env with
            | Ok (result, env') -> Ok (result, { env' with is_stable = false })
            | Error e -> Error e)

let is_context_stable =
    M (fun env ->
        Ok (env.is_stable, env))

let rec can_be_stable typ =
    match typ with
    | T_Poly _
    | T_Unit
    | T_String
    | T_Int -> true
    | T_Multiplicative (t0, t1) ->
        can_be_stable t0 && can_be_stable t1
    | T_Additive types ->
        List.for_all (fun (_, typ) -> can_be_stable typ) types
    | T_Function _ -> false
    | T_Existential _ -> false
    | T_Universal _
    | T_Fix _ -> true
    | T_Boxed _ -> true
    | T_Named (types, _) -> 
        List.for_all (fun typ -> can_be_stable typ) types
    | T_Bool -> true
    | T_Signal _ -> false

let require_stable typ =
    M (fun env ->
        if can_be_stable typ then
            let required_stable = extract_poly_types typ in
            let required_stable' =
                StringSet.union env.required_stable required_stable in
            let env' = { env with required_stable = required_stable' } in
            Ok ((), env')
        else
            Error ("Type \"" ^ type_string typ ^ "\" is not stable", Stability, None))

let is_stable_required type_name =
    M (fun env ->
        let is_stable_required_opt = StringSet.find_opt type_name env.required_stable in
        match is_stable_required_opt with
        | Some _ -> Ok (true, env)
        | None -> Ok (false, env))

let is_stable_or_ticked =
    if_tick_free (return false) (return true) >>= fun has_tick ->
    is_context_stable >>= fun stable_context ->
    return (has_tick || stable_context)

let add_var' name typ is_top_level fail_on_conflict =
    let error_msg = "A binding with that name has already been declared in the current scope" in
    is_stable_or_ticked >>= fun stable_or_ticked ->
    is_in_local_function >>= fun is_in_local_function ->
    M (fun env ->
        let binding = {
            typ = typ;
            top_level = is_top_level;
            declared_in_normal_context = not stable_or_ticked;
            declared_outside_local_recursive = not is_in_local_function
        } in
        match env.context with
        | (ve, None) -> (
            if fail_on_conflict && StringMap.mem name (List.hd ve) then Error(error_msg,Other,None)
            else let env = { env with context = ((StringMap.add name binding (List.hd ve)) :: List.tl ve, None) } in
            Ok((), env)
        )
        | (ve', Some ve) -> (
            if fail_on_conflict && StringMap.mem name (List.hd ve) then Error(error_msg,Other,None)
            else if StringMap.mem name (List.hd ve') then Error(error_msg,Other,None)
            else let env = { env with context = (ve', Some (StringMap.add name binding (List.hd ve) :: List.tl ve)) } in
            Ok((), env)
        )
    )

let add_var name typ = add_var' name typ false true

let add_top_level name typ = add_var' name typ true false

let add_vars binds =
    M ( fun env ->
        let (M tm) = 
            List.fold_left (fun m (n,t) -> add_var n t >>>= m) (return ()) binds 
        in tm env
    )

let push_scope =
    M (fun env -> match env.context with
        | (ve,None) -> Ok((), { env with context = (StringMap.empty :: ve, None) })
        | (ve',Some ve) -> Ok((), { env with context = (ve', Some (StringMap.empty :: ve)) })
    )

let pop_scope =
    M (fun env -> match env.context with
        | (ve, None) -> Ok((), { env with context = (List.tl ve, None) })
        | (ve', Some []) -> Ok((), { env with context = (ve', Some [StringMap.empty])})
        | (ve', Some ve) -> Ok((), { env with context = (ve', Some (List.tl ve))})
    )

let is_existential typ = match typ with
    | T_Existential _ -> true
    | _ -> false

let lookup_type_var_opt name =
    M (fun env ->
        let typ_opt = StringMap.find_opt name env.type_vars in
        Ok(typ_opt, env)
    )

let lookup_type_var name =
    lookup_type_var_opt name >>= fun typ_opt -> (
        match typ_opt with
        (* If the found type_var_kind is the root of a union then return the type *)
        | Some typ -> return typ
        (* If 'name' is not found in the current scope then look for it in the outer scope *)
        | None -> fail ("Undeclared type variable: " ^ name,Other,None))
        
let lookup_type_def name = 
    M (fun env ->
        match StringMap.find_opt name env.type_defs with
        | Some typ -> Ok(typ, env)
        | None -> Error("Could not find definition of: "^name,Other,None)
    )
    
let new_named_type_var name =
    M (fun env ->
        let type_var = T_Poly name in
        let type_vars' =
            StringMap.add name type_var env.type_vars in
        let env' = { env with type_vars = type_vars' } in
        Ok(type_var, env')
    )        
        
let new_type_var =
    M (fun env ->
        let type_var_id = env.next_type_var_id + 1 in
        let type_var_name = "tyvar_" ^ string_of_int type_var_id in
        let env' = { env with next_type_var_id = type_var_id } in
        Ok(type_var_name, env')
    )
    >>= new_named_type_var

let rec is_circular name typ =
    match typ with
    | T_Poly n -> n = name
    | T_Unit
    | T_Int
    | T_String -> false
    | T_Multiplicative (t0, t1) -> is_circular name t0 || is_circular name t1
    | T_Additive bindings ->
        List.exists (fun (_, typ) -> is_circular name typ) bindings
    | T_Function (t0, t1) -> is_circular name t0 || is_circular name t1
    | T_Existential t -> is_circular name t
    | T_Universal t -> is_circular name t
    | T_Fix (_, t) -> is_circular name t
    | T_Boxed t -> is_circular name t
    | T_Named (types, _) ->
        List.exists (fun typ -> is_circular name typ) types
    | T_Bool -> false
    | T_Signal t -> is_circular name t

let replace target substitute =
    M (fun env ->
        let typ_opt = StringMap.find_opt target env.type_vars in
        match typ_opt with
        | Some typ ->
            let type_vars' = StringMap.add target substitute env.type_vars in
            let env' = { env with type_vars = type_vars' } in
            Ok((), env')
        | None -> Error("Undeclared type variable: " ^ target, Other, None))

let rec type_substitution (ty:typ) (poly:string) (subst:typ) : typ = match ty with
    | T_Poly s -> if s = poly then subst else ty
    | T_Unit
    | T_Int
    | T_String
    | T_Bool -> ty
    | T_Multiplicative(t1,t2) -> T_Multiplicative(type_substitution t1 poly subst, type_substitution t2 poly subst)
    | T_Additive(cons) -> T_Additive(List.map (fun (cn,t) -> (cn, type_substitution t poly subst)) cons)
    | T_Function(t1,t2) -> T_Function(type_substitution t1 poly subst, type_substitution t2 poly subst)
    | T_Existential t -> T_Existential(type_substitution t poly subst)
    | T_Universal t -> T_Universal(type_substitution t poly subst)
    | T_Fix(s,t) -> T_Fix(s, type_substitution t poly subst)
    | T_Boxed t -> T_Boxed(type_substitution t poly subst)
    | T_Named(typs,name) -> T_Named(List.map (fun t -> type_substitution t poly subst) typs,name)
    | T_Signal t -> T_Signal(type_substitution t poly subst)
 
let expand_type typ =
    let rec expand_type typ expanded_tyvars =
        match typ with
        | T_Poly name -> (
            match StringSet.find_opt name expanded_tyvars with
            | Some _ -> fail ("Circular type", Typing, None)
            | None ->
                lookup_type_var name >>= (fun typ ->
                    match typ with
                    | T_Poly name' when name' = name -> return (typ, expanded_tyvars)
                    | typ' ->
                        expand_type typ' (StringSet.add name expanded_tyvars)
                        >=> fun (typ'', _) -> (typ'', expanded_tyvars)))
        | T_Unit
        | T_Bool
        | T_String
        | T_Int -> return (typ, expanded_tyvars)
        (*| T_Named([],n) -> return typ*)
        | T_Named(types,n) -> ( 
            let error_msg n polys types = n^" requires "^(List.length polys |> string_of_int)^" type arguments, but was given "^(List.length types |> string_of_int) in
            if_type_fix n (fun _ -> (
                lookup_type_def n >>= (fun (polys, ty) ->
                    match List.length types = List.length polys with
                    | false -> fail (error_msg n polys types,Typing,None)
                    | true -> return (typ, expanded_tyvars)))) (fun _ -> (
                lookup_type_def n >>= (fun (polys, ty) ->
                    match List.length types = List.length polys with
                    | false -> fail (error_msg n polys types,Typing,None)
                    | true ->
                        let substitutes = List.combine polys types in
                        let t =
                            List.fold_left (fun ty_acc (poly,subst) ->
                                type_substitution ty_acc poly subst) ty substitutes in
                        expand_type t expanded_tyvars
                ))))
        | T_Multiplicative(a, b) ->
            expand_type a expanded_tyvars >>= (fun (a', expanded_tyvars) ->
            expand_type b expanded_tyvars >>= (fun (b', expanded_tyvars) ->
            (T_Multiplicative(a', b'), expanded_tyvars) |> return))
        | T_Additive ts ->
            List.fold_left
                (fun acc (name, t) ->
                    acc >>= fun (types, acc') ->
                    expand_type t acc' >>= fun (t', acc'') ->
                    return ((name, t') :: types, acc''))
                (return ([], StringSet.empty))
                ts
            >>= fun (ts', expanded_tyvars') ->
            return (T_Additive ts', expanded_tyvars')
        | T_Function(a, b) ->
            expand_type a expanded_tyvars >>= (fun (a', expanded_tyvars) ->
            expand_type b expanded_tyvars >>= (fun (b', expanded_tyvars) ->
            (T_Function(a', b'), expanded_tyvars) |> return))
        | T_Existential t -> expand_type t expanded_tyvars >>= fun (typ, expanded_tyvars) -> (T_Existential typ, expanded_tyvars) |> return
        | T_Universal t -> expand_type t expanded_tyvars >>= fun (typ, expanded_tyvars) -> (T_Universal typ, expanded_tyvars) |> return
        | T_Fix (s, t) -> type_fix s >>>= expand_type t expanded_tyvars >>= fun (typ, expanded_tyvars) -> type_unfix >>>= return ((T_Fix (s, typ), expanded_tyvars)) (* Using fix here is probably wrong *)
        | T_Boxed t -> expand_type t expanded_tyvars >>= fun (typ, expanded_tyvars) -> (T_Boxed typ, expanded_tyvars) |> return
        | T_Signal t -> expand_type t expanded_tyvars >>= fun (typ, expanded_tyvars) -> (T_Signal typ, expanded_tyvars) |> return in
    expand_type typ StringSet.empty >=> fun (typ, _) -> typ

let eval_type_env_m tm type_env =
    let M tm' = tm >>= fun (typ, x) -> expand_type typ >=> fun typ' -> (typ', x) in
    match tm' type_env with
    | Ok((typ, term'), s) -> Ok(typ, term', s)
    | Error error -> Error error

let eval_env_m (M tm) type_env =
    tm type_env

let rec add_type_to_env typ =
    match typ with
    | T_Poly name -> lookup_type_var_opt name >>= fun type_var_opt -> (
        match type_var_opt with
        | Some type_var -> return ()
        | None -> new_named_type_var name >>>= return ())
    | T_Unit
    | T_String
    | T_Int -> return ()
    | T_Multiplicative(a, b) -> add_type_to_env a >>>= add_type_to_env b
    | T_Additive constructors ->
        List.map (fun (name, typ) -> add_type_to_env typ) constructors |> sequence >>>= return ()
    | T_Function(a, b) -> add_type_to_env a >>>= add_type_to_env b
    | T_Existential t -> add_type_to_env t
    | T_Universal t -> add_type_to_env t
    | T_Fix(s, t) -> add_type_to_env t
    | T_Boxed t -> add_type_to_env t
    | T_Named(type_list, name) -> List.map add_type_to_env type_list |> sequence >>>= return ()
    | T_Bool -> return ()
    | T_Signal t -> add_type_to_env t

let unify typ0 typ1 =
    let rec unify typ0 typ1 in_boxed_type : ((typ * (string * typ) list) monad) =
        (match typ0 with
        | T_Poly name -> lookup_type_var name
        | _ -> expand_type typ0)
        >>= fun typ0' -> (
            match typ1 with
            | T_Poly name -> lookup_type_var name
            | _ -> expand_type typ1)
        >>= fun typ1' -> (
            match typ0', typ1' with
            (* No need to do anything if the types are equal *)
            | a, b when a = b -> return (a,[])
            (* If both types are functions then unify the parameters and the return types *)
            | T_Fix(n,t1), T_Fix(m,t2) when n = m -> type_fix n >>>= unify t1 t2 in_boxed_type >>= fun (a,s) -> type_unfix >>>= return (T_Fix(n,a),s) 

            (* These two cases might be wrong *)
            | _, T_Fix(n,tt)
            | T_Fix(n,tt), _ -> type_fix n >>>= unify tt typ1 in_boxed_type >>= fun (a,s) -> type_unfix >>>= return (T_Fix(n,a),s)
            | T_Named(ts1,n1), T_Named(ts2,n2) -> 
                if n1 = n2 && List.length ts1 = List.length ts2
                then List.map (fun (t1,t2) -> unify t1 t2 in_boxed_type) (List.combine ts1 ts2) |> sequence >>= fun a -> let (ts,substs) = List.split a in (T_Named(ts,n1),List.flatten substs) |> return
                else fail ("T_Named unification failure",Typing,None)

            (* These two cases might be wrong *)
            | T_Named _, _ 
            | _, T_Named _ -> unify typ0' typ1' in_boxed_type
            | T_Additive ts1, T_Additive ts2 -> (if List.length ts1 = List.length ts2 
                then (
                    let ts2_map = StringMap.of_list ts2 in
                    let constructor_matches = List.map (fun (n,t) -> match StringMap.find_opt n ts2_map with
                        | None -> Error("Constructor missing: " ^ n)
                        | Some t' -> Ok(n, unify t t' in_boxed_type)
                    ) ts1 in
                    match List.find_opt Result.is_error constructor_matches with
                    | Some Error msg -> fail (msg,Typing,None)
                    | _ -> 
                        let (ns,extract) = List.map Result.get_ok constructor_matches |> List.split in 
                        map2 (return ns) (sequence extract) (fun a b -> (a, b)) >>= fun (a,b) -> 
                        let (ts,ss) = List.split b in 
                            return (T_Additive(List.combine a ts), List.flatten ss)
                )
                else fail ("T_Additive unification failure: differing constructor amount",Typing,None)
            )
            | T_Signal t1, T_Signal t2 -> unify t1 t2 in_boxed_type >>= fun (t,substs) -> return (T_Signal t, substs)
            | T_Boxed t1, T_Boxed t2 -> unify t1 t2 true >>= fun (t,substs) -> return (T_Boxed t, substs)
            | T_Function (p0, r0), T_Function (p1, r1) ->
                unify p0 p1 in_boxed_type >>= fun (p1', subst1) -> 
                unify r0 r1 in_boxed_type >>= fun (r1', subst2) ->
                return (T_Function (p1', r1'), subst1@subst2)
            | T_Multiplicative(f0,s0), T_Multiplicative(f1,s1) ->
                unify f0 f1 in_boxed_type >>= fun (f', subst1) ->
                unify s0 s1 in_boxed_type >>= fun (s', subst2) ->
                return (T_Multiplicative (f', s'), subst1@subst2)
            | T_Universal t0, T_Universal t1 -> unify t0 t1 in_boxed_type >>= fun (a,s) -> (T_Universal a, s) |> return
            | T_Existential t0, T_Existential t1 -> unify t0 t1 in_boxed_type >>= fun (a,s) -> (T_Existential a, s) |> return
            (* If both types are polymorphic then they must be equal *)
            | T_Poly a, T_Poly b ->
                (*is_stable_required a >>= fun is_typ0_stable_required -> (
                    if is_typ0_stable_required && not in_boxed_type
                    then require_stable typ1'
                    else return ()) >>>=
                is_stable_required b >>= fun is_typ1_stable_required -> (
                    if is_typ1_stable_required && not in_boxed_type
                    then require_stable typ0'
                    else return ()) >>>=*)
                replace a typ1 >>>= return (typ1', [a, typ1'])
            | T_Poly a, _ ->
                (*is_stable_required a >>= fun is_stable_required -> (
                    (*print_endline "stable";*)
                    if is_stable_required && not in_boxed_type
                    then (print_endline "stable"; require_stable typ1')
                    else (print_endline "not stable"; return ())) >>= fun _ ->*)
                (*print_endline "Fuck2";*)
                replace a typ1' >>>= return (typ1', [a, typ1'])
            | _, T_Poly b ->
                    (*print_endline "Fuck3";*)
                (*is_stable_required b >>= fun is_stable_required -> (
                    (*print_endline "stable";*)
                    if is_stable_required && not in_boxed_type
                    then require_stable typ0'
                    else return ()) >>= fun _ ->*)
                    (*print_endline "Fuck4";*)
                replace b typ0' >>>= return (typ0', [b, typ0'])
            | _ -> fail ("Unification failure on: " ^ type_string typ0' ^ " | " ^ type_string typ1',Typing,None)) in
    unify typ0 typ1 false

let lookup_constructor_type name arg_typ =
    M (fun env ->
        match StringMap.find_opt name env.type_constructs with
        | None -> Error ("No such constructor: "^name,Typing,None)
        | Some (supertyp_name,polys,typ) ->
            let type_vars = List.fold_left (fun acc poly -> StringMap.add poly (T_Poly poly) acc) env.type_vars polys in
            let M tm = unify typ arg_typ in
            match tm {env with type_vars = type_vars} with
            | Error e -> Error e
            | Ok((tt,substs),ee) -> (
                (*let substs = if not(polys = []) && substs = [] then List.map (fun p -> (p,T_Poly p)) polys else substs in*)
                let substs = List.map (fun p -> match List.find_opt (fun (n,_) -> n = p) substs with
                    | Some(n,t) -> (n,t)
                    | None -> (p, T_Poly p)
                ) polys in
                let applied_types = List.fold_left (fun acc (n,t) -> t::acc) [] substs in
                let supertype = T_Named(applied_types |> List.rev,supertyp_name) in
                Ok(supertype, {env with type_vars = StringMap.merge (fun k a b -> a) env.type_vars (StringMap.of_list substs) })
            )
    )

let rec type_equal typ0 typ1 = 
    debug_print ("checking: "^type_string typ0^" = "^type_string typ1) >>>=
    match typ0, typ1 with
    (*| T_Poly a, T_Poly b -> a = b |> return*)
    | _, T_Poly _
    | T_Poly _, _ -> true |> return
    | T_Unit, T_Unit -> true |> return
    | T_Int, T_Int -> true |> return
    | T_Bool, T_Bool -> true |> return
    | T_String, T_String -> true |> return
    | T_Signal t0, T_Signal t1 -> type_equal t0 t1
    | T_Multiplicative(t0_0, t0_1), T_Multiplicative(t1_0, t1_1) -> 
        type_equal t0_0 t1_0 >>= fun res0 -> 
        type_equal t0_1 t1_1 >>= fun res1 -> 
            (res0 && res1) |> return
    | T_Function(t0_a, t0_r), T_Function(t1_a, t1_r) -> 
        type_equal t0_a t1_a >>= fun res0 ->
        type_equal t0_r t1_r >>= fun res1 -> 
            (res0 && res1) |> return
    | T_Existential t0, T_Existential t1
    | T_Boxed(t0), T_Boxed(t1)
    | T_Universal(t0), T_Universal(t1) -> type_equal t0 t1
    | T_Additive cons, T_Named(ts,n)
    | T_Named(ts,n), T_Additive cons -> 
        lookup_type_def n >>= fun (polys,ty) -> 
            let substitutes = List.combine polys ts in List.fold_left (fun ty_acc (poly,subst) -> type_substitution ty_acc poly subst ) ty substitutes |> expand_type >>= fun t ->
            type_equal t (T_Additive cons) 
    | T_Named(ts0,n0), T_Named(ts1,n1) -> 
        List.map (fun (t0, t1) -> type_equal t0 t1) (List.combine ts0 ts1) |> sequence >>= fun comps -> 
            (List.for_all (fun c -> c) comps && n0 = n1) |> return
    | T_Additive(cons0), T_Additive(cons1) -> 
        let combined = List.combine cons0 cons1 in
        let name_comp = List.for_all (fun (n0,n1) -> n0 = n1) combined in
        List.map (fun ((_,t0), (_,t1)) -> type_equal t0 t1 ) combined |> sequence >>= fun comps -> 
            (List.for_all (fun c -> c = true) comps && name_comp) |> return
    | T_Fix(f0,_), T_Fix(f1,_) -> f0 = f1 |> return
    | (T_Fix(_, t)), ty 
    | ty, (T_Fix(_, t)) -> expand_type t >>= fun et -> type_equal et ty
    | _ -> false |> return

let rec expand_all_pattern_types pattern =
    match pattern with
    | P_Wild -> return P_Wild
    | P_Any (name, typ) -> expand_type typ >=> fun typ' -> P_Any (name, typ')
    | P_Int _
    | P_Bool _ -> return pattern
    | P_Tuple (p0, p1, typ) ->
        expand_type typ >>= fun typ' ->
        expand_all_pattern_types p0 >>= fun p0' ->
        expand_all_pattern_types p1 >>= fun p1' ->
        return (P_Tuple (p0', p1', typ'))
    | P_Cons (p_head, p_tail, typ) ->
        expand_type typ >>= fun typ' ->
        expand_all_pattern_types p_head >>= fun p_head' ->
        expand_all_pattern_types p_tail >>= fun p_tail' ->
        return (P_Cons (p_head', p_tail', typ'))
    | P_Construct (name, pattern, typ) ->
        expand_type typ >>= fun typ' ->
        expand_all_pattern_types pattern >>= fun pattern' ->
        return (P_Construct (name, pattern', typ'))

let rec expand_all_term_types term =
    let Term (typ, term) = term in
    match term with
    | Value v ->
        expand_type typ >>= fun typ' ->
        expand_all_value_types v >>= fun v' ->
        return (Term (typ', Value v'))
    | Tuple (t1, t2) ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t1 >>= fun t1' ->
        expand_all_term_types t2 >>= fun t2' ->
        return (Term (typ', Tuple (t1', t2')))
    | Let (name, binding_typ_opt, t1, t2) -> (
        match binding_typ_opt with
        | Some binding_typ -> expand_type binding_typ >=> fun binding_typ' -> Some binding_typ'
        | None -> return binding_typ_opt) >>= fun binding_typ_opt' ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t1 >>= fun t1' ->
        expand_all_term_types t2 >>= fun t2' ->
        return (Term (typ', Let (name, binding_typ_opt', t1', t2')))
    | App (t1, t2) ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t1 >>= fun t1' ->
        expand_all_term_types t2 >>= fun t2' ->
        return (Term (typ', App (t1', t2')))
    | Delay (clock, free_bindings, t) ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t >>= fun t' ->
        return (Term (typ', Delay (clock, free_bindings, t')))
    | Adv t ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t >>= fun t' ->
        return (Term (typ', Adv t'))
    | Unbox t ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t >>= fun t' ->
        return (Term (typ', Unbox t'))
    | Fix (name, t) ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t >>= fun t' ->
        return (Term (typ', Fix (name, t')))
    | Match (t, alts) ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t >>= fun t' ->
        List.map (fun (patterns, term) ->
            expand_all_term_types term >>= fun term' ->
            list_map expand_all_pattern_types patterns >>= fun pattern_typ' ->
            return (pattern_typ', term')) alts
        |> sequence
        >>= fun alts' ->
        return (Term (typ', Match (t', alts')))
    | Select (cl0, cl1, v1, v2) ->
        expand_type typ >>= fun typ' ->
        expand_all_value_types v1 >>= fun v1' ->
        expand_all_value_types v2 >>= fun v2' ->
        return (Term (typ', Select (cl0, cl1, v1', v2')))
    | Never ->
        expand_type typ >=> fun typ' -> Term (typ', Never)
    | Read buffer_name ->
        expand_type typ >=> fun typ' -> Term (typ', Read buffer_name)
    | SignalCons (t1, t2) ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t1 >>= fun t1' ->
        expand_all_term_types t2 >>= fun t2' ->
        return (Term (typ', SignalCons (t1', t2')))

and expand_all_value_types value =
    let Val (typ, value) = value in
    match value with
    | Binding v ->
        expand_type typ >>= fun typ' ->
        return (Val (typ', Binding v))
    | Unit -> return (Val (typ, Unit))
    | Lambda (param_name, param_typ_opt, free_bindings, term) -> (
        match param_typ_opt with
        | Some param_typ -> expand_type param_typ >=> fun param_typ' -> Some param_typ'
        | None -> return param_typ_opt) >>= fun param_typ_opt' ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types term >>= fun term' ->
        return (Val (typ', Lambda (param_name, param_typ_opt', free_bindings, term')))
    | Bool _
    | String _
    | Int _ -> return (Val (typ, value))
    | Construct (name, t) ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t >>= fun t' ->
        return (Val (typ', Construct (name, t')))
    | Wait channel_name ->
        expand_type typ >>= fun typ' ->
        return (Val (typ', Wait channel_name))
    | Box (t, free_bindings) ->
        expand_type typ >>= fun typ' ->
        expand_all_term_types t >>= fun t' ->
        return (Val (typ', Box (t', free_bindings)))

let check_stability =
    M (fun env -> Ok (env.required_stable, env)) >>= fun required_stable ->
    StringSet.to_list required_stable
    |> List.map (fun type_name ->
        expand_type (T_Poly type_name) >>= fun typ ->
            if can_be_stable typ then
                return ()
            else
                fail (
                    ("Type " ^ type_string typ ^ " is not stable"),
                    Stability, None))
    |> sequence
    >>>= return ()
