%{
  open Absyn
  open Lexing

  module StringSet = Set.Make(String)

  let unfold_lambda info (Term(ln,_) as body) =
    let rec aux is c acc = match is with
      | [] -> acc
      | (P_Any(n,_),ty)::t -> aux t (c+1) (Value(Val(ln,Lambda(n,ty, StringSet.empty, acc))) |> term ln)
      | (P_Wild,ty)::t -> aux t (c+1) (Value(Val(ln,Lambda("arg_"^(string_of_int c), ty, StringSet.empty, acc))) |> term ln)
      | (p,ty)::t -> 
        let arg_name = "arg_"^(string_of_int c) in 
        aux t (c+1) (Value(Val(ln,Lambda(arg_name, ty, StringSet.empty, Term(ln,Match(Term(ln,Value(Val(ln, Binding arg_name))), [[p],acc]))))) |> term ln)
    in
    match aux (List.rev info) 0 body with
    | Term(_, Value(Val(_,v))) -> v
    | _ -> failwith "Failed unwrapping lambda"

  let rec is_rec_type name typ = match typ with
    | T_Poly _ 
    | T_Unit
    | T_Bool
    | T_String
    | T_Int -> false
    | T_Multiplicative (t1,t2)
    | T_Function (t1,t2) -> is_rec_type name t1 || is_rec_type name t2
    | T_Additive ts -> List.exists (fun (_,t) -> is_rec_type name t) ts
    | T_Existential t 
    | T_Universal t
    | T_Fix(_,t) 
    | T_Signal t 
    | T_Boxed t -> is_rec_type name t 
    | T_Named(_,n) -> n = name

  let parse_type_def name polys typ =
    if is_rec_type name typ then TypeDef(name,polys,T_Fix(name,typ))
    else TypeDef(name,polys,typ)
%}
%token <int> CSTINT
%token <string> NAME
%token <string> CONSTRUCT
%token <string> CSTSTRING
%token TRUE FALSE
%token LPAR RPAR LBRAKE RBRAKE
%token PLUS MINUS TIMES EQ NEQ LT GT LTEQ GTEQ CONS CARAT AND OR FSLASH
%token PIPE
%token COMMA COLON EOF
%token MATCH WITH LET REC IN IF THEN ELSE
%token UNDERSCORE SEMI
%token L_ARROW R_ARROW LAMBDA
%token DELAY NEVER ADV BOX UNBOX SELECT WAIT READ
%token INT BOOL STRING SIGNAL UNIT TYPE OF LATER BOXED TICK

/*Low precedence*/
%nonassoc IN ELSE
%left R_ARROW
%right CONS 
%left CARAT
//%nonassoc ADV BOX UNBOX WAIT READ DELAY
%left EQ NEQ GT LT GTEQ LTEQ 
%left AND OR
%left PLUS MINUS
%left TIMES FSLASH
%left BOXED LATER SIGNAL
/*High precedence*/

%start main
%type <((int Absyn.top) list)> main  /* terms with an int, for line */
%start standalone_term
%type <int Absyn.term> standalone_term
%%
main:
  top+ EOF     { $1 }
;
standalone_term:
  term EOF { $1 }
;

output_binding:
  NAME L_ARROW term { TopBind($1, $3) }
;

top:
  | top_term SEMI { $1 }
  | output_binding SEMI { $1 }
  | type_def SEMI { $1 }
;

top_term:
  | LET NAME EQ term_with_match { TopLet ($2, None, $4) }
  | LET NAME COLON typ EQ term_with_match { TopLet ($2, Some $4, $6) }
  | LET REC NAME EQ term_with_match { TopLet ($3, None, Term($symbolstartpos.pos_lnum,Fix($3, $5))) }
  | LET REC NAME COLON typ EQ term_with_match { TopLet ($3, Some $5, Term($symbolstartpos.pos_lnum,Fix($3, $7))) }
;

type_def:
  TYPE poly_type_def NAME EQ typ { parse_type_def $3 $2 $5 }
  | TYPE poly_type_def NAME EQ adt_cons+ { parse_type_def $3 $2 (T_Additive $5) }
;

poly_type_def:
  { [] }
  | TICK NAME poly_type_def { $2::$3 }
;

typ:
  | simple_typ { $1 }
  | typ TIMES typ { T_Multiplicative($1,$3) } 
  | simple_typ R_ARROW typ { T_Function($1,$3) }
  | LPAR typ COMMA seperated(COMMA,typ) RPAR NAME { T_Named($2::$4,$6) } 
;

simple_typ:
  INT { T_Int }
  | BOOL { T_Bool }
  | STRING { T_String }
  | NAME { T_Named([], $1) }
  | UNIT { T_Unit }
  | TICK NAME { T_Poly $2 }
  | LPAR typ RPAR { $2 }
  | typ BOXED { T_Boxed $1 }
  | typ LATER { T_Existential $1 }
  | typ SIGNAL { T_Signal $1 }
  | simple_typ NAME { T_Named([$1], $2) }
;

%public seperated(S,C):
  | C  {[$1]}
  | C S seperated(S,C) {$1::$3}
;

adt_cons:
  PIPE CONSTRUCT { ($2, T_Unit) }
  | PIPE CONSTRUCT OF typ { ($2, $4) }
;

term:
  term_inner  { Term($symbolstartpos.pos_lnum, $1) }
;
term_inner:
  term binop term { App(Term($symbolstartpos.pos_lnum, App(Term($symbolstartpos.pos_lnum, Value(Val($symbolstartpos.pos_lnum, Binding $2))), $1)), $3) }
  | term CONS term { SignalCons($1, $3) }
  | DELAY simple_value_or_term { Delay(empty_clock_set, StringSet.empty, $2) }
  | ADV simple_value_or_term { Adv $2 }
  | UNBOX simple_value_or_term { Unbox $2 }
  | SELECT simple_value simple_value { Select(empty_clock_set, empty_clock_set, $2, $3) }
  | READ NAME { Read $2 }
  | simple_term_inner { $1 }
  | value { Value $1 }
  | app_inner { $1 }
  | let_term_inner { $1 }
  | IF term THEN term ELSE term { Match($2, [
    ([P_Bool true], $4);
    ([P_Bool false], $6);
  ]) }
;

app:
  app_inner   { Term($symbolstartpos.pos_lnum, $1) }
;
app_inner:
  simple_value_or_term simple_value_or_term { App($1,$2) }
  //| CONSTRUCT simple_value_or_term { Value(Val($symbolstartpos.pos_lnum, Construct($1,$2))) }
  | app simple_value_or_term { App($1,$2) }
;

let_term:
  let_term_inner   { Term($symbolstartpos.pos_lnum, $1) }
;
let_term_inner:
  | LET NAME EQ term IN term { Let ($2, None, $4, $6) }
  | LET NAME COLON typ EQ term IN term { Let ($2, Some $4, $6, $8) }
  | LET REC NAME EQ term IN term { Let ($3, None, Term($symbolstartpos.pos_lnum, Fix($3, $5)), $7) }
  | LET REC NAME COLON typ EQ term IN term { Let ($3, Some $5, Term($symbolstartpos.pos_lnum, Fix($3, $7)), $9) }
;

simple_term:
  simple_term_inner   { Term($symbolstartpos.pos_lnum, $1) }
;
simple_term_inner:
  LPAR term_with_match COMMA term_with_match RPAR { Tuple($2,$4) }
  | LPAR term_with_match_inner RPAR { $2 }
  | NEVER { Never }
;

term_with_match:
  term_with_match_inner   { Term($symbolstartpos.pos_lnum, $1) }
;
term_with_match_inner:
  MATCH term WITH alt+ { Match($2,List.flatten $4) }
  | MATCH term WITH pattern R_ARROW term { Match($2, [[$4],$6]) }
  | term_inner { $1 }
;

value:
  BOX simple_value_or_term { Val($symbolstartpos.pos_lnum, Box ($2, StringSet.empty)) }
  | LAMBDA lambda_arg+ R_ARROW term { Val($symbolstartpos.pos_lnum, unfold_lambda $2 $4) }
  | WAIT NAME { Val($symbolstartpos.pos_lnum, Wait $2) }
  | CONSTRUCT simple_value_or_term { Val($symbolstartpos.pos_lnum, Construct($1,$2)) }
  | simple_value { $1 }
;

simple_value:
  NAME { Val($symbolstartpos.pos_lnum, Binding $1) }
  | TRUE { Val($symbolstartpos.pos_lnum, Bool true) }
  | FALSE { Val($symbolstartpos.pos_lnum, Bool false) }
  | LPAR RPAR { Val($symbolstartpos.pos_lnum, Unit) }
  | CSTINT { Val($symbolstartpos.pos_lnum, Int $1) }
  | CSTSTRING { Val($symbolstartpos.pos_lnum, String $1) }
  | CONSTRUCT { Val($symbolstartpos.pos_lnum, Construct($1, Term($symbolstartpos.pos_lnum, Value(Val($symbolstartpos.pos_lnum, Unit))))) }
  | LPAR value RPAR { $2 }
;


simple_value_or_term:
  simple_value_or_term_inner   { Term($symbolstartpos.pos_lnum, $1) }
;
simple_value_or_term_inner:
  simple_term_inner { $1 }
  | simple_value { Value $1 }
;

lambda_arg:
  simple_pattern { ($1, None) }
  | LPAR simple_pattern COLON typ RPAR { ($2,Some $4) }
;


%inline binop:
  | PLUS    { ("+") }
  | MINUS   { ("-") }
  | TIMES   { ("*") } 
  | FSLASH  { ("/") }
  | EQ      { ("=") }
  | NEQ     { ("!=") }
  | LT      { ("<") }
  | GT      { (">") }
  | LTEQ    { ("<=") }
  | GTEQ    { (">=") }
  | CARAT   { ("^") }
  | AND     { ("&&") }
  | OR      { ("||") }
;

alt:
  PIPE seperated(PIPE,pattern) R_ARROW term { [$2,$4] }
;

pattern:
  simple_pattern { $1 }
  | pattern CONS pattern { P_Cons($1,$3,$symbolstartpos.pos_lnum) }
  | CONSTRUCT simple_pattern { P_Construct($1,$2,$symbolstartpos.pos_lnum) }
  | CONSTRUCT { P_Construct($1,P_Wild,$symbolstartpos.pos_lnum) }
;

simple_pattern:
  UNDERSCORE { P_Wild }
  | NAME { P_Any($1, $symbolstartpos.pos_lnum) }
  | CSTINT { P_Int $1 }
  | TRUE { P_Bool true }
  | FALSE { P_Bool false }
  | LPAR pattern COMMA pattern RPAR { P_Tuple($2,$4,$symbolstartpos.pos_lnum) }
  | LPAR pattern RPAR { $2 }
;
