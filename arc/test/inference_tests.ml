open Arclib.Absyn
open Arclib.Exceptions
(* open Inference *)

module ProgramEnv = Arclib.Program_env.Make(Example.Simulator)
module TypeSystem = Arclib.Inference.Make(ProgramEnv)


let success_cases = [
    (
        "test_successor_function",
        "let f = \\x -> x in f 0",
        T_Int
    );
    (
        "test_binding_assignments",
        "
        let a = 0 in
        let b = a in
        let c = b in
        let d = c in
        d
        ",
        T_Int
    );
    (
        "test_higher_order_function",
        "let f = \\g -> g 0 in f (\\x -> x)",
        T_Int
    );
    (
        "test_explicit_binding_type",
        "let x : int = 0 in x",
        T_Int
    );
    (
        "test_explicit_function_type",
        "let f : int -> int = \\x -> x in f 0",
        T_Int
    );
    (
        "test_polymorthic_function_application",
        "let f = \\a b -> (a,b) in f 0 0",
        T_Multiplicative(T_Int,T_Int)
    );
    (
        "test_polymorthic_function",
        "let f = \\a b -> (a,b) in f",
        T_Function(T_Poly "a",T_Function(T_Poly "b", T_Multiplicative(T_Poly "a", T_Poly "b")))
    );
    (
        "test_identity_function",
        "let f = \\g -> g in f",
        T_Function(T_Poly "a", T_Poly "a")
    );
    (
        "test_identity_function_higher_order",
        "let f = \\g -> g in f (\\x -> 0)",
        T_Function(T_Poly "a", T_Int)
    );
    (
        "test_identity_function_self_application",
        "let f = \\g -> g in f f",
        T_Function(T_Poly "a", T_Poly "a")
    );
    (
        "test_multiple_applications_of_same_function",
        "let f = \\a -> (a,a) in f (f 0)",
        T_Multiplicative(T_Multiplicative(T_Int,T_Int),T_Multiplicative(T_Int,T_Int))
    );
    (
        "test_explicit_function_type_attachment",
        "let f : int -> int = \\x -> x in f",
        T_Function(T_Int,T_Int)
    );
    (    
        "test_explicit_function_type_attachment_poly",
        "let f : 'a -> int = \\x -> 0 in f",
        T_Function(T_Int,T_Poly "a")
    );
    (
        "test_adt",
        "Some 2",
        T_Named([T_Int], "option")
    );
    (
        "test_poly_adt",
        "None",
        T_Named([T_Poly "a"], "option")
    );
    (
        "test_if",
        "if true then 2 else 1",
        T_Int
    );

]

let failure_cases = [
    (
        "test_function_parameter_not_generalized",
        "let f = \\g -> (g 0, g ()) in f (\\x -> x)",
        Typing
    );
    (
        "test_recursive_function_not_generalized_in_own_body",
        "let f = \\x -> (f 0, f ()) in f 0",
        Typing
    );
    (
        "test_simple_let_type_mismatch",
        "let x : bool = 0 in x",
        Typing
    );
    (
        "test_failing_explicit_function_type_attachment",
        "let f : int -> int = \\(x : bool) -> x in f",
        Typing
    );
    (
        "test_if_not_bool_cond",
        "if 2 then 2 else 1",
        Typing
    );
    (
        "test_if_cases_type_differ",
        "if true then 2 else \"one\"",
        Typing
    );
]

let test_all () =
    let test_success (case, term_string, expected) =
        try
            let term = Arclib.Parser.standalone_term (Arclib.Lexer.start "standalone") (Lexing.from_string term_string) in
            let checker = Term(0,Let("checker", Some expected, term, Term(0,Value(Val(0, Binding "checker"))))) in
            let _ = TypeSystem.type_term checker in ("OK:"^case)
        with
        | Problem t -> "!!Inference failed, case: "^case^", had a problem: "^problem_string t
        | Failure msg -> "!!Inference failed, case: "^case^", threw an exception: "^msg
        | _ -> "!!Inference failed, case: "^case^", threw an exception"
    in
    let test_failure (case, term_string, expected_problem_type) =
        try
            let term = Arclib.Parser.standalone_term (Arclib.Lexer.start "standalone") (Lexing.from_string term_string) in
            let checker = Term(0,Let("checker", None, term, Term(0,Value(Val(0, Binding "checker"))))) in
            let (res_typ,_) = TypeSystem.type_term checker in
            let res_string = type_string res_typ in
            "!!Inference succeded unexpectedly, case: "^case^", got: "^res_string
        with
        | Problem typ -> if typ = expected_problem_type then "OK: "^case else "!!"^case^": Wrong problem type: "^problem_string typ
        | Failure msg -> "!!"^case^": Threw failure with: "^msg
        | _ -> "!!"^case^": !!Did not throw a Problem"
    in
    let rec run_tests func cases acc = match cases with
        | [] -> acc
        | c::t -> run_tests func t (func c::acc)
    in
    let results = 
        "# Success" :: run_tests test_success success_cases
        ("# Failure":: (run_tests test_failure failure_cases [])) in
    List.iter (Printf.printf "%s\n") results
    
