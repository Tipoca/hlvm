open Printf
open Expr
open Hlvm

let rec ty : ty -> Hlvm.Type.t = function
  | `Unit -> `Unit
  | `Bool -> `Bool
  | `Int -> `Int
  | `Float -> `Float
  | `Tuple tys -> `Struct(List.map ty tys)

let rec destructure arg rest = function
  | PVar s -> Expr.Let(s, arg, rest)
  | PTup ps -> destructures arg rest 0 ps
and destructures arg rest i = function
  | [] -> rest
  | p::ps ->
      let rest = destructures arg rest (i+1) ps in
      destructure (Expr.GetValue(arg, i)) rest p

let rec compile = function
  | Unit -> Expr.Unit
  | Int n -> Expr.Int n
  | Float x -> Expr.Float x
  | Var s -> Expr.Var s
  | Apply(f, x) -> Expr.Apply(compile f, [compile x])
  | Tuple xs -> Expr.Struct(List.map compile xs)
  | UnArith(`Neg, x) -> Expr.UnArith(`Neg, compile x)
  | BinArith(op, x, y) ->
      let op = (op :> [`Add | `Div | `Mod | `Mul | `Sub]) in
      Expr.BinArith(op, compile x, compile y)
  | Cmp(op, x, y) -> Expr.Cmp(op, compile x, compile y)
  | If(p, t, f) -> Expr.If(compile p, compile t, compile f)
  | LetIn(x, f, g) -> Expr.Let(x, compile f, compile g)

let lexbuf = Lexing.from_channel stdin

open Parse

let token lexbuf =
  let tok = Lex.token lexbuf in
  let s =
    match tok with
    | LET -> "LET"
    | REC -> "REC"
    | IN -> "IN"
    | IF -> "IF"
    | THEN -> "THEN"
    | ELSE -> "ELSE"
    | PIPE -> "PIPE"
    | COMMA -> "COMMA"
    | OPEN -> "OPEN"
    | CLOSE -> "CLOSE"
    | LT -> "LT"
    | LE -> "LE"
    | EQ -> "EQ"
    | NE -> "NE"
    | GE -> "GE"
    | GT -> "GT"
    | PLUS -> "PLUS"
    | MINUS -> "MINUS"
    | TIMES -> "TIMES"
    | DIVIDE -> "DIVIDE"
    | CONS -> "CONS"
    | INT n -> "INT "^n
    | FLOAT x -> "FLOAT "^x
    | IDENT s -> "IDENT \""^s^"\""
    | SEMI -> "SEMI"
    | SEMISEMI -> "SEMISEMI"
    | _ -> "<tok>" in
  printf "Token: %s\n%!" s;
  tok

let rec repl() =
  List.iter Hlvm.eval
    [`Extern("putchar", [`Int], `Unit);
     `Function("print_char", ["c", `Int], `Unit,
	       Expr.Apply(Expr.Var "putchar", [Expr.Var "c"]));
     `Function("float_of_int", ["n", `Int], `Float,
	       Expr.FloatOfInt(Expr.Var "n"));
     `Function("int_of_float", ["x", `Float], `Int,
	       Expr.IntOfFloat(Expr.Var "x"))
    ];
  printf "# %!";
  begin
    try
      let f = Parse.toplevel token lexbuf in
      let ch = open_out "expr.dat" in
      output_value ch f;
      close_out ch;
      match f with
      | Expr f -> Hlvm.eval(`Expr(compile f))
      | Defun(f, p, ty_x, ty_ret, body) ->
	  let dummy = "frontend`arg" in
	  Hlvm.eval(`Function(f, [dummy, ty ty_x], ty ty_ret,
			      destructure (Expr.Var dummy) (compile body) p))
    with exn ->
      printf "Error: %s\n%!" (Printexc.to_string exn)
  end;
  repl()

let () =
(*
  Hlvm.debug := true;
*)
  repl()
