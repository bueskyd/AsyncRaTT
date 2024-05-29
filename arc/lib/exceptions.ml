
type problem =
  | Typing
  | Clocking
  | Parsing
  | Interpretation
  | Stability
  | Other


let problem_string = function
  | Typing -> "Typing"
  | Clocking -> "Clocking"
  | Parsing -> "Parsing"
  | Interpretation -> "Interpretation"
  | Stability -> "Stability"
  | Other -> "Other"

exception Problem of problem  (* file, line, explanation *)

let raise_problem typ = raise (Problem typ)

let problem_string = function
  | Typing -> "Typing"
  | Clocking -> "Clocking"
  | Parsing -> "Parsing"
  | Interpretation -> "Interpretation"
  | Stability -> "Stability"
  | Other -> "Other"
