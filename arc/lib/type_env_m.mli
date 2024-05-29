open Exceptions
open Type_env
open Absyn

type 'a type_env_m
type error = string * problem * int option

val (>>=) : 'a type_env_m -> ('a -> 'b type_env_m) -> 'b type_env_m
val (>>>=) : 'a type_env_m -> 'b type_env_m -> 'b type_env_m
val (>=>) : 'a type_env_m -> ('a -> 'b) -> 'b type_env_m
val fail : error -> 'a type_env_m
val line_mark : int -> 'a type_env_m -> 'a type_env_m
val return : 'a -> 'a type_env_m
val sequence : 'a type_env_m list -> 'a list type_env_m
val map2 : 'a type_env_m -> 'b type_env_m -> ('a -> 'b -> 'c) -> 'c type_env_m
val fold_left : ('a -> 'b -> 'a type_env_m) -> 'a -> 'b list -> 'a type_env_m
val list_map : ('a -> 'b type_env_m) -> 'a list -> 'b list type_env_m
val combine : 'a type_env_m -> 'b type_env_m -> ('a * 'b) type_env_m
val undo : 'a type_env_m -> 'a type_env_m
val adv_time : 'a type_env_m -> 'a type_env_m
val enter_local_function : 'a type_env_m -> 'a type_env_m
val is_in_local_function : bool type_env_m
val box : 'a type_env_m -> 'a type_env_m
val is_context_stable : bool type_env_m
val require_stable : typ -> unit type_env_m
val is_stable_required : string -> bool type_env_m
val lookup_before : string -> binding option type_env_m
val lookup_after : string -> binding option type_env_m
val unify : typ -> typ -> (typ * (string * typ) list) type_env_m

val expand_type : typ -> typ type_env_m
val eval_type_env_m : (typ * 'a) type_env_m -> type_env -> (typ * 'a * type_env, error) result
val eval_env_m :'a type_env_m -> type_env -> ('a * type_env, error) result
val empty_env : (string * string list * typ) list -> type_env
val is_existential : typ -> bool
val new_type_var : typ type_env_m
val add_var : string -> typ -> unit type_env_m
val add_top_level : string -> typ -> unit type_env_m
val add_vars : (string * typ) list -> unit type_env_m
val push_scope : unit type_env_m
val pop_scope : unit type_env_m
val get_tick : bool type_env_m
val tick : unit type_env_m
val untick : unit type_env_m
val if_tick_free : 'a type_env_m -> 'a type_env_m -> 'a type_env_m
val fix : string -> unit type_env_m
val type_fix : string -> unit type_env_m
val if_fix : string -> (unit -> 'a type_env_m) -> (unit -> 'a type_env_m) -> 'a type_env_m
val if_type_fix : string -> (unit -> 'a type_env_m) -> (unit -> 'a type_env_m) -> 'a type_env_m
val unfix : unit type_env_m
val type_unfix : unit type_env_m
val lookup_constructor_type : string -> typ -> typ type_env_m
val add_type_to_env : typ -> unit type_env_m
val type_substitution : typ -> string -> typ -> typ
val type_equal : typ -> typ -> bool type_env_m
val expand_all_pattern_types : typ pattern -> typ pattern type_env_m
val expand_all_term_types : typ term -> typ term type_env_m
val expand_all_value_types : typ value -> typ value type_env_m
val check_stability : unit type_env_m

val debug_print : string -> unit type_env_m
