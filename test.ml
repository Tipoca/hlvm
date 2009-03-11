open Expr

(** Integer Fibonacci benchmark *)
let fib : Hlvm.state Hlvm.t list =
  let n = Var "n" in
  [`Function
     ("fib", ["n", `Int], `Int,
      If(n >: Int 1,
	 Apply(Var "fib", [n -: Int 2]) +: Apply(Var "fib", [n -: Int 1]),
	 n));

   `Expr(Apply(Var "fib", [Int 40]), `Int)]

(** Float-based Fibonacci benchmark *)
let ffib : Hlvm.state Hlvm.t list =
  let n = Var "n" in
  [`Function
     ("fib", ["n", `Float], `Float,
      If(n >: Float 1.0,
	 Apply(Var "fib", [n -: Float 2.0]) +:
	   Apply(Var "fib", [n -: Float 1.0]),
	 n));

   `Expr(Apply(Var "fib", [Float 40.]), `Float)]

let fill (x, ty) =
  [`Function
     ("fill", [ "a", `Array ty;
		"i", `Int ], `Unit,
      If(Var "i" <: Length(Var "a"),
	 compound
	   [ Set(Var "a", Var "i", x);
	     Apply(Var "fill", [Var "a"; Var "i" +: Int 1]) ],
	 Unit))]

(** Sieve of Eratosthenes. *)
let sieve i : Hlvm.state Hlvm.t list =
  fill(Bool true, `Bool) @
    [`Function
       ("last", ["a", `Array `Bool; "i", `Int], `Int,
	If(Get(Var "a", Var "i"), Var "i",
	   Apply(Var "last", [Var "a"; Var "i" -: Int 1])));
     
     `Function
       ("loop2", ["a", `Array `Bool; "i", `Int; "di", `Int], `Unit,
	If(Var "i" >=: Length(Var "a"), Unit,
	   compound
	     [ Set(Var "a", Var "i", Bool false);
	       Apply(Var "loop2",
		     [Var "a"; Var "i" +: Var "di"; Var "di"]) ]));

     `Function
       ("loop1", ["a", `Array `Bool; "i", `Int], `Unit,
	If(Var "i" =: Length(Var "a"), Unit,
	   compound
	     [ If(Get(Var "a", Var "i"),
		  Apply(Var "loop2", [Var "a"; Int 2 *: Var "i"; Var "i"]),
		  Unit);
	       Apply(Var "loop1", [Var "a"; Var "i" +: Int 1]) ]));
     
     `Expr(Let("a", Alloc(Int i, `Bool),
	       compound
		 [ Apply(Var "fill", [Var "a"; Int 0]);
		   Apply(Var "loop1", [Var "a"; Int 2]);
		   Apply(Var "last", [Var "a"; Length(Var "a") -: Int 1]) ]),
	   `Int)]

let mandelbrot n : Hlvm.state Hlvm.t list =
  [`Function
     ("pixel", ["n", `Int;
		"zr", `Float; "zi", `Float;
		"cr", `Float; "ci", `Float], `Unit,
      If(Var "n" =: Int 65536, Printf(" ", []),
	 If(Var "zr" *: Var "zr" +: Var "zi" *: Var "zi" >=: Float 4.0,
	    Printf(".", []),
	    Apply(Var "pixel",
		  [Var "n" +: Int 1;
		   Var "zr" *: Var "zr" -:
		     Var "zi" *: Var "zi" +: Var "cr";
		   Float 2.0 *: Var "zr" *: Var "zi" +: Var "ci";
		   Var "cr"; Var "ci"]))));
   
   `Function
     ("row", ["i", `Int; "j", `Int; "n", `Int], `Unit,
      If(Var "i" >: Var "n", Unit,
	 compound
	   [ Apply(Var "pixel",
		   [Int 0;
		    Float 0.0; Float 0.0;
		    Float 2.0 *: FloatOfInt(Var "i") /: FloatOfInt(Var "n") -:
		      Float 1.5;
		    Float 2.0 *: FloatOfInt(Var "j") /: FloatOfInt(Var "n") -:
		      Float 1.0]);
	     Apply(Var "row", [Var "i" +: Int 1; Var "j"; Var "n"])]));

   `Function
     ("col", ["j", `Int; "n", `Int], `Unit,
      If(Var "j" >: Var "n", Unit,
	 compound
	   [ Apply(Var "row", [Int 0; Var "j"; Var "n"]);
	     Printf("\n", []);
	     Apply(Var "col", [Var "j" +: Int 1; Var "n"])]));

   `Expr(Apply(Var "col", [Int 0; Int n]), `Unit)]

let mandelbrot2 n : Hlvm.state Hlvm.t list =
  let complex = `Struct[`Float; `Float] in
  let re z = GetValue(Var z, 0) in
  let im z = GetValue(Var z, 1) in
  [`Function("znorm2", ["z", complex], `Float,
             re "z" *: re "z" +: im "z" *: im "z");

   `Function("zsqr", ["z", complex], complex,
             Struct[re "z" *: re "z" -: im "z" *: im "z";
                    Float 2.0 *: re "z" *: im "z"]);

   `Function("zadd", ["z1", complex; "z2", complex], complex,
             Struct[re "z1" +: re "z2"; im "z1" +: im "z2"]);

   `Function
     ("pixel", ["n", `Int; "z", complex; "c", complex], `Unit,
      If(Var "n" =: Int 65536, Printf(" ", []),
         If(Apply(Var "znorm2", [Var "z"]) >=: Float 4.0,
            Printf(".", []),
	    Apply(Var "pixel",
                  [Var "n" +: Int 1;
                   Apply(Var "zadd", [Apply(Var "zsqr", [Var "z"]); Var "c"]);
                   Var "c"]))));

   `Function
     ("row", ["i", `Int; "j", `Int; "n", `Int], `Unit,
      If(Var "i" >: Var "n", Unit,
         compound
           [ Apply(Var "pixel",
                   [Int 0;
                    Struct[Float 0.0; Float 0.0];
                    Struct[Float 2.0 *: FloatOfInt(Var "i") /:
                             FloatOfInt(Var "n") -: Float 1.5;
                           Float 2.0 *: FloatOfInt(Var "j") /:
                             FloatOfInt(Var "n") -: Float 1.0]]);
             Apply(Var "row", [Var "i" +: Int 1; Var "j"; Var "n"])]));

   `Function
     ("col", ["j", `Int; "n", `Int], `Unit,
      If(Var "j" >: Var "n", Unit,
	 compound
	   [ Apply(Var "row", [Int 0; Var "j"; Var "n"]);
	     Printf("\n", []);
	     Apply(Var "col", [Var "j" +: Int 1; Var "n"])]));

   `Expr(Apply(Var "col", [Int 0; Int n]), `Unit)]

let mandelbrot3 n : Hlvm.state Hlvm.t list =
  let complex = `Struct[`Float; `Float] in
  let re z = GetValue(Var z, 0) in
  let im z = GetValue(Var z, 1) in
  [`Function("znorm2", ["z", complex], `Float,
             re "z" *: re "z" +: im "z" *: im "z");

   `Function("zsqr", ["z", complex], complex,
             Struct[re "z" *: re "z" -: im "z" *: im "z";
                    Float 2.0 *: re "z" *: im "z"]);

   `Function("zadd", ["z1", complex; "z2", complex], complex,
             Struct[re "z1" +: re "z2"; im "z1" +: im "z2"]);

   `Function
     ("pixel", ["nzc", `Struct[`Int; complex; complex]], `Unit,
      Let("n", GetValue(Var "nzc", 0),
	  Let("z", GetValue(Var "nzc", 1),
	      Let("c", GetValue(Var "nzc", 2),
      If(Var "n" =: Int 65536, Printf(" ", []),
         If(Apply(Var "znorm2", [Var "z"]) >=: Float 4.0,
            Printf(".", []),
	    Apply(Var "pixel",
		  [Struct
                     [Var "n" +: Int 1;
                      Apply(Var "zadd", [Apply(Var "zsqr", [Var "z"]); Var "c"]);
                      Var "c"]])))))));

   `Function
     ("row", ["i", `Int; "j", `Int; "n", `Int], `Unit,
      If(Var "i" >: Var "n", Unit,
         compound
           [ Apply(Var "pixel",
		   [Struct
                      [Int 0;
                       Struct[Float 0.0; Float 0.0];
                       Struct[Float 2.0 *: FloatOfInt(Var "i") /:
				FloatOfInt(Var "n") -: Float 1.5;
                              Float 2.0 *: FloatOfInt(Var "j") /:
				FloatOfInt(Var "n") -: Float 1.0]]]);
             Apply(Var "row", [Var "i" +: Int 1; Var "j"; Var "n"])]));

   `Function
     ("col", ["j", `Int; "n", `Int], `Unit,
      If(Var "j" >: Var "n", Unit,
	 compound
	   [ Apply(Var "row", [Int 0; Var "j"; Var "n"]);
	     Printf("\n", []);
	     Apply(Var "col", [Var "j" +: Int 1; Var "n"])]));

   `Expr(Apply(Var "col", [Int 0; Int n]), `Unit)]

let tco n : Hlvm.state Hlvm.t list =
  [`Function("even", ["odd", `Function([`Int], `Int); "n", `Int], `Int,
             Apply(Var "odd", [Var "n" +: Int 1]));

   `Function("odd", ["n", `Int], `Int,
	     If(Var "n" <: Int n,
		Apply(Var "even", [Var "odd"; Var "n" +: Int 1]),
		Var "n"));

   `Expr(Apply(Var "even", [Var "odd"; Int 0]), `Int)]

let tuples : Hlvm.state Hlvm.t list =
  [`Function("id", ["s", `Struct[`Float; `Int]], `Struct[`Float; `Int],
	     Var "s");

   `Function("id2", ["s", `Struct[`Float; `Int]], `Struct[`Float; `Int],
	     Apply(Var "id", [Var "s"]));

   `Function("rev", ["s", `Struct[`Int; `Float]], `Struct[`Float; `Int],
	     Apply(Var "id", [Struct[GetValue(Var "s", 1);
				     GetValue(Var "s", 0)]]));

   `Expr(Apply(Var "rev", [Struct[Int 2; Float 3.4]]), `Struct[`Float; `Int])]

let trig : Hlvm.state Hlvm.t list =
  let triple = `Struct[`Float; `Float; `Float] in
  [`Extern("sin", [`Float], `Float);
   `Extern("cos", [`Float], `Float);
   `Function("test", ["f", `Function([`Float], `Float)], triple,
	     Struct[Apply(Var "f", [Float 0.1]);
		    Apply(Var "f", [Float 0.2]);
		    Apply(Var "f", [Float 0.3])]);
   `Expr(compound[Print(Apply(Var "test", [Var "sin"]));
		  Print(Apply(Var "test", [Var "cos"]))], `Unit)]

(*
  OCaml: 4.53s recursive
  OCaml: 3.63s loop
  HLVM:  3.35s
  HLVM:  2.42s substitute "f"
  HLVM:  2.29s fully inlined and reduced fold
*)
let fold n : Hlvm.state Hlvm.t list =
  let fold ty1 ty2 =
    [`Function("fold_aux", ["n", `Int;
			    "f", `Function([ty1; ty2], ty1);
			    "y", ty1;
			    "xs", `Array ty2], ty1,
	       If(Var "n" <: Length(Var "xs"),
		  Apply(Var "fold_aux",
			[Var "n" +: Int 1;
			 Var "f";
			 Apply(Var "f", [Var "y"; Get(Var "xs", Var "n")]);
			 Var "xs"]),
		  Var "y"));
     `Function("fold", ["f", `Function([ty1; ty2], ty1);
			"y", ty1;
			"xs", `Array ty2], ty1,
	       Apply(Var "fold_aux", [Int 0; Var "f"; Var "y"; Var "xs"]))] in

  fold (`Struct[`Float; `Float]) `Float @
    fill(Float 1., `Float) @
    [`Function("f", ["x", `Struct[`Float; `Float];
		     "y", `Float], `Struct[`Float; `Float],
	       Struct[GetValue(Var "x", 0) +:
			Var "y" /: (Float 1.0 +: GetValue(Var "x", 1));
		      GetValue(Var "x", 1) +: Float 1.]);
     `Expr(Let("xs", Alloc(Int n, `Float),
	       compound
		 [ Apply(Var "fill", [Var "xs"; Int 0]);
		   Apply(Var "fold",
			 [Var "f"; Struct[Float 0.; Float 0.]; Var "xs"])]),
	   `Struct[`Float; `Float])]

let fold n : Hlvm.state Hlvm.t list =
  fill(Float 1., `Float) @
    [`Function("fold_aux", ["n", `Int;
			    "y", `Struct[`Float; `Float];
			    "xs", `Array `Float], `Struct[`Float; `Float],
	       If(Var "n" <: Length(Var "xs"),
		  Let("i", GetValue(Var "y", 1),
		      Apply(Var "fold_aux",
			    [Var "n" +: Int 1;
			     Struct[GetValue(Var "y", 0) +:
				      Get(Var "xs", Var "n") /:
				      (Float 1.0 +: Var "i");
				    Var "i" +: Float 1.];
			     Var "xs"])),
		  Var "y"));

     `Expr(Let("xs", Alloc(Int n, `Float),
	       compound
		 [ Apply(Var "fill", [Var "xs"; Int 0]);
		   Apply(Var "fold_aux",
			 [Int 0; Struct[Float 0.; Float 0.]; Var "xs"])]),
	   `Struct[`Float; `Float])]

(** Type of a list. *)
let ty_list ty =
  [ `Type("Cons", `Struct[ty; `Reference]);
    `Type("Nil", `Unit) ]

let nil = Construct("Nil", Unit)
let cons h t = Construct("Cons", Struct[h; t])

let cond_list list h t k_nil k_cons =
  If(IsType(Var list, "Nil"), k_nil,
     Let(h^t, Cast(Var list, "Cons"),
	 Let(h, GetValue(Var (h^t), 0),
	     Let(t, GetValue(Var (h^t), 1),
		 k_cons))))

let list_fold_left a b =
  `Function("fold_left", ["f", `Function([a; b], a);
			  "x", a;
			  "list", `Reference], a,
	    cond_list "list" "h" "t"
	      (Var "x")
	      (Apply(Var "fold_left",
		     [Var "f";
		      Apply(Var "f", [Var "x"; Var "h"]);
		      Var "t"])))

let list n : Hlvm.state Hlvm.t list =
  ty_list `Int @
    [ `Function("add", ["n", `Int; "m", `Int], `Int, Var "n" +: Var "m");
      
      `Function("init", ["t", `Reference; "n", `Int], `Reference,
		Let("t", cons (Var "n") (Var "t"),
		    If(Var "n" =: Int 0, Var "t",
		       Apply(Var "init", [Var "t"; Var "n" -: Int 1]))));
      
      list_fold_left `Int `Int;
      
      `Expr(Let("list", Apply(Var "init", [nil; Int n]),
		Apply(Var "fold_left", [Var "add"; Int 0; Var "list"])), `Int);
      
      `Expr(Apply(Var "init", [nil; Int 10]), `Reference);

      `Function("print", ["x", `Reference], `Unit,
		compound
		  [ Printf("Visiting: ", []);
		    Print(AddressOf(Var "x"));
		    Printf(" ", []);
		    Print(Var "x");
		    Printf("\n", []);
		    Apply(Visit(Var "x"), [Var "print"; Var "x"]) ]);

      `Expr(Let("list", Apply(Var "init", [nil; Int 10]),
		Apply(Visit(Var "list"), [Var "print"; Var "list"])), `Unit)]

(** Type of a closure. *)
let ty_closure(ty1, ty2) =
  `Struct[`Function([`Reference; ty1], ty2); `Reference]

(** Apply a closure. *)
let apply(f, x) =
  Apply(GetValue(f, 0), [GetValue(f, 1); x])

let curry : Hlvm.state Hlvm.t list =
  let ty_ret = `Struct[`Int; `Float] in
  [`Function("f_uncurried", ["x", `Int; "y", `Float], ty_ret,
	     Struct[Var "x"; Var "y"]);

   `Type("Int", `Int);

   `Function("f_apply_2", ["env", `Reference; "y", `Float], ty_ret,
	     Apply(Var "f_uncurried", [Cast(Var "env", "Int"); Var "y"]));

   `Function("f_apply_1", ["x", `Int], ty_closure(`Float, ty_ret),
	     Struct[Var "f_apply_2"; Construct("Int", Var "x")]);

   `Expr(Let("g", Apply(Var "f_apply_1", [Int 3]),
	     Struct[apply(Var "g", Float 2.3);
		    apply(Var "g", Float 3.4)]), `Struct[ty_ret; ty_ret])]

let list_filter ty : Hlvm.state Hlvm.t =
  `Function("filter", ["pred", ty_closure(ty, `Bool);
		       "list", `Reference], `Reference,
	    cond_list "list" "h" "t"
	      (Var "list")
	      (Let("t", Apply(Var "filter", [Var "pred"; Var "t"]),
		   If(apply(Var "pred", Var "h"),
		      cons (Var "h") (Var "t"),
		      Var "t"))))

let list_length ty : Hlvm.state Hlvm.t =
  `Function("length", ["list", `Reference], `Int,
	    cond_list "list" "h" "t"
	      (Int 0)
	      (Int 1 +: Apply(Var "length", [Var "t"])))

let list_length ty : Hlvm.state Hlvm.t =
  `Function("length", ["list", `Reference], `Int,
	    cond_list "list" "h" "t"
	      (Int 0)
	      (cond_list "t" "h" "t"
		 (Int 1)
		 (Int 2 +: Apply(Var "length", [Var "t"]))))

let queens n =
  let x1 = Var "x1" and x2 = Var "x2" and y1 = Var "y1" and y2 = Var "y2" in
  let ty_pos = `Struct[`Int; `Int] in
  let rec init n f = if n=0 then [] else f(n-1) :: init (n-1) f in
  let ps = List.flatten (init n (fun i -> init n (fun j -> i, j))) in
  let rec expr_of_list = function
    | [] -> nil
    | (i, j)::t -> cons (Struct[Int i; Int j]) (expr_of_list t) in
  let ps = expr_of_list ps in
  ty_list ty_pos @
    [ list_filter ty_pos;

      list_length ty_pos;

      `Function("safe", ["p1", ty_pos; "p2", ty_pos], `Bool,
		Let("x1", GetValue(Var "p1", 0),
		    Let("y1", GetValue(Var "p1", 1),
			Let("x2", GetValue(Var "p2", 0),
			    Let("y2", GetValue(Var "p2", 1),
				(x1 <>: x2) &&:
				  (y1 <>: y2) &&:
				  (x2 -: x1 <>: y2 -: y1) &&:
				  (x1 -: y2 <>: x2 -: y1))))));

      `Type("IntInt", ty_pos);

      `Function("safe_2", ["env", `Reference; "p2", ty_pos], `Bool,
		Let("p1", Cast(Var "env", "IntInt"),
		    Apply(Var "safe", [Var "p1"; Var "p2"])));

      `Function("safe_1", ["p1", ty_pos], ty_closure(ty_pos, `Bool),
		Struct[Var "safe_2"; Construct("IntInt", Var "p1")]);

      `Function("search", ["f", `Function([`Reference; `Int], `Int);
			   "n", `Int;
			   "qs", `Reference;
			   "ps", `Reference;
			   "accu", `Int], `Int,
		cond_list "ps" "q" "ps"
		  (If(Apply(Var "length", [Var "qs"]) =: Var "n",
		      Apply(Var "f", [Var "qs"; Var "accu"]),
		      Var "accu"))
		  (Apply(Var "search",
			 [Var "f";
			  Var "n";
			  cons (Var "q") (Var "qs");
			  Apply(Var "filter",
				[Apply(Var "safe_1", [Var "q"]);
				 Var "ps"]);
			  Apply(Var "search",
				[Var "f";
				 Var "n";
				 Var "qs";
				 Var "ps";
				 Var "accu"])])));

      `Function("f", ["", `Reference; "n", `Int], `Int, Var "n" +: Int 1);

      `Expr(Apply(Var "search", [Var "f"; Int n; nil; ps; Int 0]),
	    `Int)]
(*
let queens n =
  let x1 = Var "x1" and x2 = Var "x2" and y1 = Var "y1" and y2 = Var "y2" in
  let ty_pos = `Struct[`Int; `Int] in
  let rec init n f = if n=0 then [] else f(n-1) :: init (n-1) f in
  let ps = List.flatten (init n (fun i -> init n (fun j -> i, j))) in
  let rec expr_of_list = function
    | [] -> nil
    | (i, j)::t -> cons (Struct[Int i; Int j]) (expr_of_list t) in
  let ps = expr_of_list ps in
  ty_list ty_pos @
  [ list_length ty_pos;

   `Function("safe", ["p1", ty_pos; "p2", ty_pos], `Bool,
	     Let("x1", GetValue(Var "p1", 0),
		 Let("y1", GetValue(Var "p1", 1),
		     Let("x2", GetValue(Var "p2", 0),
			 Let("y2", GetValue(Var "p2", 1),
			     (x1 <>: x2) &&:
			       (y1 <>: y2) &&:
			       (x2 -: x1 <>: y2 -: y1) &&:
			       (x1 -: y2 <>: x2 -: y1))))));

   `Function("filter", ["p1", ty_pos;
			"list", `Reference], `Reference,
	     cond_list "list" "p2" "t"
	       (Var "list")
	       (Let("t", Apply(Var "filter", [Var "p1"; Var "t"]),
		    If(Apply(Var "safe", [Var "p1"; Var "p2"]),
		       cons (Var "p2") (Var "t"),
		       Var "t"))));

   `Function("search", ["f", `Function([`Reference; `Int], `Int);
			"n", `Int;
			"qs", `Reference;
			"ps", `Reference;
			"accu", `Int], `Int,
	     cond_list "ps" "q" "ps"
	       (If(Apply(Var "length", [Var "qs"]) =: Var "n",
		   Apply(Var "f", [Var "qs"; Var "accu"]),
		   Var "accu"))
	       (Apply(Var "search",
		      [Var "f";
		       Var "n";
		       cons (Var "q") (Var "qs");
		       Apply(Var "filter",
			     [Var "q";
			      Var "ps"]);
		       Apply(Var "search",
			     [Var "f";
			      Var "n";
			      Var "qs";
			      Var "ps";
			      Var "accu"])])));

   `Function("f", ["", `Reference; "n", `Int], `Int, Var "n" +: Int 1);

   `Expr(Apply(Var "search", [Var "f"; Int n; nil; ps; Int 0]),
	 `Int)]
*)
(** Insert debug information at the beginning of each function. *)
let rec trace : Hlvm.state Hlvm.t list -> Hlvm.state Hlvm.t list = function
  | `Function(f, args, ty_ret, body)::t ->
      `Function
	(f, args, ty_ret,
	 compound
	   [Printf(f^" ", []);
	    Print(Struct(List.map (fun (x, _) -> Var x) args));
	    Printf("\n", []);
	    body]) :: trace t
  | h::t -> h :: trace t
  | [] -> []

(** Main program. *)
let () =
  begin
    match Sys.argv with
    | [|_; "--debug"|] -> Hlvm.debug := true
    | _ -> ()
  end;
  Hlvm.compile_and_run
    ((
       fib @
	 ffib @
	 sieve 10000000 @
	 mandelbrot 77 @
	 mandelbrot2 77 @
	 mandelbrot3 77 @
	 tco 1000000 @
	 tuples @
	 trig @
	 fold 100000000 @
	 list 10000 @
	 curry @
	 queens 8 @
	 queens 9 @
	 queens 10 @
	 queens 11 @
	 []
     ))
