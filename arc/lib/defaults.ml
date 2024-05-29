open Absyn open Runtime_value

type default = Default of {
    name : string;
    value : runtime_binding;
    typ : typ
}

let add_integers a b =
    match a, b with
    | Int_rv a, Int_rv b -> Int_rv (a + b)
    | _ -> failwith "Not integers"

let sub_integers a b =
    match a, b with
    | Int_rv a, Int_rv b -> Int_rv (a - b)
    | _ -> failwith "Not integers"

let multiply_integers a b =
    match a, b with
    | Int_rv a, Int_rv b -> Int_rv (a * b)
    | _ -> failwith "Not integers"

let concat_strings a b =
    match a, b with
    | String_rv a, String_rv b -> String_rv (a ^ b)
    | _ -> failwith "Not integers"

let bool_and a b =
    match a, b with
    | Bool_rv a, Bool_rv b -> Bool_rv (a && b)
    | _ -> failwith "Not integers"

let bool_or a b =
    match a, b with
    | Bool_rv a, Bool_rv b -> Bool_rv (a || b)
    | _ -> failwith "Not integers"

let poly_eq a b =
    match a, b with
    | Bool_rv a, Bool_rv b -> Bool_rv(a = b)
    | Int_rv a, Int_rv b -> Bool_rv(a = b)
    | String_rv a, String_rv b -> Bool_rv(a = b)
    | _ -> failwith "Could not compare"

let poly_neq a b =
    match a, b with
    | Bool_rv a, Bool_rv b -> Bool_rv(a != b)
    | Int_rv a, Int_rv b -> Bool_rv(a != b)
    | String_rv a, String_rv b -> Bool_rv(a != b)
    | _ -> failwith "Could not compare"

let binop t = T_Boxed (T_Function (t, T_Function (t, t)))
let comp t = T_Boxed (T_Function (t, T_Function (t, T_Bool)))

let operator op f t =
    Default {
        name = op;
        value = B { value = Built_in_2 f; clock = empty_clock; top_level = true };
        typ = t }

let int_comp f a b =
    match a, b with
    | Int_rv a, Int_rv b -> Bool_rv(f a b)
    | _ -> failwith "Could not compare"

let bool_binop f a b =
    match a, b with
    | Bool_rv a, Bool_rv b -> Bool_rv (f a b)
    | _ -> failwith "Not integers"

let int_binop f a b =
    match a, b with
    | Int_rv a, Int_rv b -> Int_rv (f a b)
    | _ -> failwith "Not integers"

let println value =
    print_endline (runtime_value_string value);
    Unit_rv

let default_types = [
    ("selection", ["a";"b"], T_Additive[
        "Left", T_Multiplicative(T_Poly "a", T_Existential(T_Poly "b"));
        "Right", T_Multiplicative(T_Existential(T_Poly "a"), T_Poly "b");
        "Both", T_Multiplicative(T_Poly "a", T_Poly "b");
    ]);
    ("option", ["a"], T_Additive[
        "Some", T_Poly "a";
        "None", T_Unit
    ]);
]

let defaults = [
    Default {
        name = "=";
        value = B { value = Built_in_2 poly_eq; clock = empty_clock; top_level = true };
        typ = T_Boxed (T_Function (T_Poly "a", T_Function (T_Poly "a", T_Bool))) };
    Default {
        name = "!=";
        value = B { value = Built_in_2 poly_neq; clock = empty_clock; top_level = true };
        typ = T_Boxed (T_Function (T_Poly "a", T_Function (T_Poly "a", T_Bool))) };
    operator "<" (int_comp (<)) (comp T_Int);
    operator ">" (int_comp (>)) (comp T_Int);
    operator "<=" (int_comp (<=)) (comp T_Int);
    operator ">=" (int_comp (>=)) (comp T_Int);
    operator "+" (int_binop (+)) (binop T_Int);
    operator "-" (int_binop (-)) (binop T_Int);
    operator "/" (int_binop (/)) (binop T_Int);
    operator "*" (int_binop (fun a b -> a*b)) (binop T_Int);
    Default {
        name = "^";
        value = B { value = Built_in_2 concat_strings; clock = empty_clock; top_level = true };
        typ = T_Boxed (T_Function (T_String, T_Function (T_String, T_String))) };
    operator "&&" (bool_binop (&&)) (binop T_Bool);
    operator "||" (bool_binop (||)) (binop T_Bool);
    Default {
        name = "println";
        value = B { value = Built_in_1 println; clock = empty_clock; top_level = true };
        typ = T_Boxed (T_Function (T_Int, T_Function (T_Int, T_Unit))) };
]
