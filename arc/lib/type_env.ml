open Absyn

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type binding = {
    typ : typ;
    top_level : bool;
    declared_in_normal_context : bool;
    declared_outside_local_recursive : bool
}

type var_env = binding StringMap.t list

type type_env = {
    type_vars : typ StringMap.t;
    next_type_var_id : int;
    type_defs: (string list * typ) StringMap.t;
    type_constructs: (string * string list * typ) StringMap.t;
    type_fix: string option;
    fix: string list;
    context : var_env * (var_env option);
    required_stable : StringSet.t;
    is_stable : bool;
    in_local_function : bool
}
