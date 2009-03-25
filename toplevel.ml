open Printf
open Expr
open Camlp4.PreCast

let expr = Gram.Entry.mk "expr"

EXTEND Gram
  expr:
  [ "sum" LEFTA
      [ e1 = expr; "+"; e2 = expr -> e1 +: e2
      | e1 = expr; "-"; e2 = expr -> e1 -: e2 ]
  | "product" LEFTA
      [ e1 = expr; "*"; e2 = expr -> e1 *: e2
      | e1 = expr; "/"; e2 = expr -> e1 /: e2 ]
  | "simple" NONA
      [ n = INT -> Int(int_of_string n)
      | x = FLOAT -> Float(float_of_string x)
      | "("; e = expr; ")" -> e ] ];
  END

let try_input_line ch =
  try Some(input_line ch) with End_of_file -> None

let rec toploop() =
  printf "> %!";
  let line = try_input_line stdin in
  match line with
  | None ->
      printf "\n%!";
  | Some string ->
      begin
	try
	  let expr = Gram.parse expr Loc.ghost (Stream.of_string string) in
	  try
	    Hlvm.eval (`Expr expr)
	  with exn ->
	    printf "Eval error: %s\n%!" (Printexc.to_string exn)
	with exn ->
	  printf "Parse error: %s\n%!" (Printexc.to_string exn)
      end;
      toploop()

let () =
  toploop()
