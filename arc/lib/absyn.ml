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
