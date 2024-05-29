open Absyn


let is_binop s = match s with
  | "+" | "-" | "*" | "=" | "!=" | "<" | ">" | "<=" | ">=" | "^" | "&&" | "||" -> true
  | _ -> false
  
let direct_match t p r = 
  let rec aux t p = match t, p with
    | _, P_Any _
    | _, P_Wild -> Some(Some p, r)
    | Term(_,Value(Val(_,Bool a))), P_Bool b -> if a = b then Some(None,r) else None
    | Term(_,Value(Val(_,Int a))), P_Int b -> if a = b then Some(None,r) else None
    | Term(_,Tuple(a0,a1)), P_Tuple(b0,b1,_) -> ( match aux a0 b0, aux a1 b1 with
      | None,_
      | _,None -> None
      | Some(Some _,_), _
      | _, Some(Some _,_) -> Some(Some p, r)
      | _ -> Some(None,r)
    )
    | _ -> None
  in aux t p 

let rec viable_match (Term(x,t) as term) p =
  match t,p with
  | Value(Val(_,Int a)), P_Int b -> a = b
  | Value(Val(_,Bool a)), P_Bool b -> a = b
  | Value(Val(_,Construct(nv,tv))), P_Construct(np,pp,_) -> nv = np && viable_match tv pp
  | Tuple(a,b), P_Tuple(ap,bp,_) -> viable_match a ap && viable_match b bp 
  | _ -> true

let rec variable_term (Term(_,t)) = match t with
  | Value v -> variable_value v
  | Tuple(a,b) -> variable_term a || variable_term b
  | App(a,b) -> true
  | Let(_,_,_,b) -> variable_term b
  | Match(a,alts) -> List.mem true (List.map (fun (_,t) -> variable_term t) alts)
  | Delay(_, _, t) -> variable_term t
  | Adv t -> variable_term t
  | Select(_,_,v0,v1) -> variable_value v0 || variable_value v1
  | Unbox t -> variable_term t
  | Fix(_,t) -> variable_term t
  | Read _ -> true
  | SignalCons(a,b) -> variable_term a || variable_term b
  | _ -> false

and variable_value (Val(_,v)) = match v with
  | Binding _ -> true
  | Lambda(_, _, _, t) -> variable_term t
  | Box (t, free_bindings) -> variable_term t
  | Wait _ -> true
  | Construct(_,t) -> variable_term t
  | _ -> false

let pattern_bindings p =
  let rec aux p acc = match p with
  | P_Any(x,_) -> StringSet.add x acc
  | P_Tuple(a,b,_)
  | P_Cons(a,b,_) -> aux a (aux b acc)
  | P_Construct(_,p,_) -> aux p acc
  | _ -> acc
  in
  aux p StringSet.empty

let uses_any bs t =
  let rec uses_any_term (Term(_,t)) = match t with
  | Value v -> uses_any_value v
  | Tuple(a,b)
  | App(a,b)
  | Let(_,_,a,b) -> uses_any_term a || uses_any_term b
  | Match(a,alts) -> uses_any_term a || List.exists (fun (_,t) -> uses_any_term t) alts
  | Delay(_, _, t) 
  | Adv t -> uses_any_term t
  | Select(_,_,a,b) -> uses_any_value a || uses_any_value b
  | Unbox t 
  | Fix(_,t) -> uses_any_term t
  | Never -> false
  | Read _ -> false
  | SignalCons(a,b) -> uses_any_term a || uses_any_term b
  and uses_any_value (Val(_,v)) = match v with
  | Binding v -> StringSet.mem v bs
  | Unit 
  | Int _
  | Bool _
  | String _ -> false
  | Lambda(_, _, _, t) -> uses_any_term t
  | Wait _ -> false
  | Box (t, _) -> uses_any_term t
  | Construct(_,t) -> uses_any_term t
  in
  uses_any_term t

let simplify_match a alts =
  List.find_map (fun (ps,t) -> 
    List.find_map (fun p -> direct_match a p t) ps
  ) alts

let rec optimize_term (Term(x,t)) = Term(x, optimize_term_inner t)
and optimize_term_inner t = match t with
  | Value v -> Value(optimize_value v)
  | Tuple(a,b) -> Tuple(optimize_term a, optimize_term b)
  | Let(n,ty,e,b) -> Let(n,ty,optimize_term e, optimize_term b)
  | Match(a,alts) -> (
    let a = optimize_term a in
    let alts = List.filter_map (fun (ps,t) -> 
      let ps = List.filter_map (fun p -> if viable_match a p then Some p else None) ps in
      if ps = [] then None else Some(ps, optimize_term t)) alts
    in
    if variable_term a then Match(a, alts)
    else match simplify_match a alts with
      | None -> Match(a, alts)
      | Some(None,Term(_,t)) -> optimize_term_inner t
      | Some(Some p, (Term(_,t) as term)) ->
        if uses_any (pattern_bindings p) term then Match(a, [[p], term]) else t
  )
  | Delay(cl, free_bindings, t) -> Delay(cl, free_bindings, optimize_term t)
  | Adv t -> Adv(optimize_term t)
  | Select(cl0,cl1,v0,v1) -> Select(cl0,cl1,optimize_value v0,optimize_value v1)
  | Unbox t -> Unbox(optimize_term t)
  | Fix(n,t) -> Fix(n,optimize_term t)
  | Read _
  | Never -> t
  | SignalCons(x,xs) -> SignalCons(optimize_term x, optimize_term xs)
  | App(Term(x0, App(Term(x1, Value(Val(x2, Binding (op)))), a)), b) when is_binop op-> (
    match op, optimize_term a, optimize_term b with
    | "+", Term(_,Value(Val(_,Int a))), Term(_,Value(Val(_,Int b))) -> Value(Val(x0,Int (a + b)))
    | "-", Term(_,Value(Val(_,Int a))), Term(_,Value(Val(_,Int b))) -> Value(Val(x0,Int (a - b)))
    | "*", Term(_,Value(Val(_,Int a))), Term(_,Value(Val(_,Int b))) -> Value(Val(x0,Int (a * b)))
    | "<", Term(_,Value(Val(_,Int a))), Term(_,Value(Val(_,Int b))) -> Value(Val(x0,Bool (a < b)))
    | ">", Term(_,Value(Val(_,Int a))), Term(_,Value(Val(_,Int b))) -> Value(Val(x0,Bool (a > b)))
    | "<=", Term(_,Value(Val(_,Int a))), Term(_,Value(Val(_,Int b))) -> Value(Val(x0,Bool (a <= b)))
    | ">=", Term(_,Value(Val(_,Int a))), Term(_,Value(Val(_,Int b))) -> Value(Val(x0,Bool (a >= b)))
    | "&&", Term(_,Value(Val(_,Bool a))), Term(_,Value(Val(_,Bool b))) -> Value(Val(x0,Bool (a && b)))
    | "||", Term(_,Value(Val(_,Bool a))), Term(_,Value(Val(_,Bool b))) -> Value(Val(x0,Bool (a || b)))
    | "^", Term(_,Value(Val(_,String a))), Term(_,Value(Val(_,String b))) -> Value(Val(x0,String (a ^ b)))
    | "=", Term(_,Value(Val(_,a))), Term(_,Value(Val(_,b))) -> Value(Val(x0,Bool (a = b)))
    | "!=", Term(_,Value(Val(_,a))), Term(_,Value(Val(_,b))) -> Value(Val(x0,Bool (a != b)))
    | _,oa,ob -> App(Term(x0, App(Term(x1, Value(Val(x2, Binding op))), oa)), ob)
  )
  | App(a,b) -> App(optimize_term a, optimize_term b)

and optimize_value (Val(x,v)) = Val(x,optimize_value_inner v)
and optimize_value_inner v = match v with
  | Binding _
  | Unit
  | Wait _
  | Bool _
  | String _
  | Int _ -> v
  | Lambda(a, ty, free_bindings, t) -> Lambda(a, ty, free_bindings, optimize_term t)
  | Box (t, free_bindings) -> Box (optimize_term t, free_bindings)
  | Construct(n,t) -> Construct(n, optimize_term t)

and optimize_top t = match t with
  | TopLet(n,ty,t) -> TopLet(n,ty, optimize_term t)
  | TopBind(c,t) -> TopBind(c, optimize_term t)
  | TypeDef _ -> t
