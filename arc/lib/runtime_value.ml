open Absyn

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type clock = C of StringSet.t
type typed_term = (int*typ) term

let empty_clock = C StringSet.empty
let singleton_clock channel_name = C (StringSet.singleton channel_name)
let union_clocks (C c0) (C c1) = C (StringSet.union c0 c1)

type runtime_value =
    | Binding_rv of string
    | Unit_rv
    | Int_rv of int
    | Bool_rv of bool
    | String_rv of string
    | Tuple_rv of runtime_value * runtime_value
    | Closure of string * value_env * typed_term
    | Construct_rv of string * runtime_value
    | Built_in_1 of (runtime_value -> runtime_value)
    | Built_in_2 of (runtime_value -> runtime_value -> runtime_value)
    | Location of int * clock
    | Box of typed_term * value_env
    | Signal_rv of runtime_value * runtime_value
    | Wait_rv
    | Rec of typed_term

and value_env = VE of { vars : runtime_binding StringMap.t }

and runtime_binding = B of {
    value : runtime_value;
    clock : clock;
    top_level : bool
}

let empty_value_env = VE { vars = StringMap.empty }

type delayed = Delayed of {
    value_env : value_env;
    term : typed_term;
    clock : clock
}

let rec runtime_value_string (value : runtime_value) : string =
    match value with
    | Binding_rv name -> name
    | Unit_rv -> "()"
    | Int_rv n -> string_of_int n
    | Bool_rv b -> if b then "true" else "false"
    | String_rv str -> "\""^str^"\""
    | Tuple_rv (v0, v1) -> "(" ^ runtime_value_string v0 ^ ", " ^ runtime_value_string v1 ^ ")"
    | Closure (param_name, VE value_env, term) ->
        let bindings_list = (StringMap.to_list value_env.vars) in
        let env_string = (
            match bindings_list with
            | [] -> ""
            | _ ->
                let env_string = List.fold_left
                    (fun acc (name, B binding) -> acc ^ ", " ^ name ^ " <- " ^ runtime_value_string binding.value)
                    ""
                    (List.tl bindings_list) in
                let (fst_name, B fst_binding) = List.hd bindings_list in
                fst_name ^ " <- " ^ runtime_value_string fst_binding.value ^ env_string) in
        "closure " ^ "[" ^ env_string ^ "]"
    | Construct_rv (name, v) -> name ^ "(" ^ runtime_value_string v ^ ")"
    | Built_in_2 build_in -> "built_in2"
    | Built_in_1 build_in -> "built_in1"
    | Location (location, clock) -> "Loc" ^ string_of_int location
    | Box _ -> "[]"
    | Signal_rv (head, tail) -> runtime_value_string head ^ " :: " ^ runtime_value_string tail
    | Wait_rv -> "wait"
    | Rec term -> "rec"
