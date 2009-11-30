(** Test programs for HLVM. *)

open Hlvm
open Expr

(** Integer Fibonacci benchmark *)
let fib ns : Hlvm.t list =
  let n = Var "n" in
  [ `Function
      ("fib", ["n", `Int], `Int,
       If(n >: Int 1,
          Apply(Var "fib", [n -: Int 2]) +: Apply(Var "fib", [n -: Int 1]),
          n)) ] @
    List.map
    (fun n ->
       `Expr
	 (compound
            [ Printf("\nInteger Fibonacci function: fib(%d)\n", [Int n]);
              Apply(Var "fib", [Int n]) ]))
    ns

(** Float-based Fibonacci benchmark *)
let ffib ns : Hlvm.t list =
  let n = Var "n" in
  [ `Function
      ("ffib", ["n", `Float], `Float,
       If(n >: Float 1.0,
	  Apply(Var "ffib", [n -: Float 2.0]) +:
	    Apply(Var "ffib", [n -: Float 1.0]),
	  n)) ] @
    List.map
    (fun n ->
       let n = Float n in
       `Expr
	 (compound
            [ Printf("\nFloating-point Fibonacci function: fib(%f)\n", [n]);
              Apply(Var "ffib", [n]) ]))
    ns

let fill ty =
  [`Function
     ("fill", [ "a", `Array ty;
		"x", ty;
		"i", `Int ], `Unit,
      If(Var "i" <: Length(Var "a"),
	 compound
	   [ Set(Var "a", Var "i", Var "x");
	     Apply(Var "fill", [Var "a"; Var "x"; Var "i" +: Int 1]) ],
	 Unit))]

(** Sieve of Eratosthenes. *)
let sieve is : Hlvm.t list =
  fill `Bool @
    [ `Function
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
		Apply(Var "loop1", [Var "a"; Var "i" +: Int 1]) ])) ] @
    List.map
    (fun i ->
       `Expr(Let("a", Alloc(Int i, Bool false),
		 compound
		   [ Printf("\nSieve of Eratosthenes\n", []);
                     Apply(Var "fill", [Var "a"; Bool true; Int 0]);
		     Apply(Var "loop1", [Var "a"; Int 2]);
		     Apply(Var "last", [Var "a"; Length(Var "a") -: Int 1]) ])))
    is

let mandelbrot ns : Hlvm.t list =
  [ `Function
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
	      Apply(Var "col", [Var "j" +: Int 1; Var "n"])])) ] @
    List.map
    (fun n ->
       `Expr
	 (compound
            [ Printf("\nMandelbrot with inline complex arithmetic\n", []);
              Apply(Var "col", [Int 0; Int n]) ]))
    ns

let mandelbrot2 ns : Hlvm.t list =
  let complex = `Struct[`Float; `Float] in
  let re z = GetValue(Var z, 0) in
  let im z = GetValue(Var z, 1) in
  [ `Function("znorm2", ["z", complex], `Float,
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
	      Apply(Var "col", [Var "j" +: Int 1; Var "n"])])) ] @
    List.map
    (fun n ->
       `Expr
	 (compound
            [ Printf("\nMandelbrot with complex arithmetic functions\n", []);
              Apply(Var "col", [Int 0; Int n]) ]))
    ns

let tco n : Hlvm.t list =
  [ `Function("even", ["odd", `Function([`Int], `Int); "n", `Int], `Int,
              Apply(Var "odd", [Var "n" +: Int 1]));

    `Function("odd", ["n", `Int], `Int,
	      If(Var "n" <: Int n,
		 Apply(Var "even", [Var "odd"; Var "n" +: Int 1]),
		 Var "n"));

    `Expr
      (compound
         [ Printf("\nTesting tail call elimination across a higher-order function\n", []);
           Apply(Var "even", [Var "odd"; Int 0]) ])]

let tuples : Hlvm.t list =
  [ `Function("id", ["s", `Struct[`Float; `Int]], `Struct[`Float; `Int],
	      Var "s");

    `Function("id2", ["s", `Struct[`Float; `Int]], `Struct[`Float; `Int],
	      Apply(Var "id", [Var "s"]));

    `Function("rev", ["s", `Struct[`Int; `Float]], `Struct[`Float; `Int],
	      Apply(Var "id", [Struct[GetValue(Var "s", 1);
				      GetValue(Var "s", 0)]]));

    `Expr
      (compound
         [ Printf("\nTesting structs (should give (3.4, 2))\n", []);
           Apply(Var "rev", [Struct[Int 2; Float 3.4]]) ]) ]

let trig : Hlvm.t list =
  let triple = `Struct[`Float; `Float; `Float] in
  [ `Extern("sin", [`Float], `Float);

    `Extern("cos", [`Float], `Float);

    `Function("test", ["f", `Function([`Float], `Float)], triple,
	      Struct[Apply(Var "f", [Float 0.1]);
		     Apply(Var "f", [Float 0.2]);
		     Apply(Var "f", [Float 0.3])]);

    `Expr
      (compound
         [ Printf("\nTesting FFI\n", []);
           Print(Apply(Var "test", [Var "sin"]));
	   Print(Apply(Var "test", [Var "cos"])) ]) ]

(*
  OCaml: 4.53s recursive
  OCaml: 3.63s loop
  HLVM:  3.35s
  HLVM:  2.42s substitute "f"
  HLVM:  2.29s fully inlined and reduced fold
*)
let fold ns : Hlvm.t list =
  let fold ty1 ty2 =
    [ `Function("fold_aux", ["n", `Int;
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
		Apply(Var "fold_aux", [Int 0; Var "f"; Var "y"; Var "xs"])) ]
  in

  fold (`Struct[`Float; `Float]) `Float @
    fill `Float @
    [ `Function("f", ["x", `Struct[`Float; `Float];
		      "y", `Float], `Struct[`Float; `Float],
		Struct[GetValue(Var "x", 0) +:
			 Var "y" /: (Float 1.0 +: GetValue(Var "x", 1));
		       GetValue(Var "x", 1) +: Float 1.]) ] @
    List.map
    (fun n ->
       `Expr
	 (Let("xs", Alloc(Int n, Float 1.0),
	      compound
		[ Printf("\nArray.fold over %d elements with tuple accumulator\n", [Int n]);
		  Apply(Var "fold",
			[Var "f"; Struct[Float 0.; Float 0.]; Var "xs"]) ])))
    ns

(** Type of a list. *)
let ty_list ty =
  [ `Type("Cons", `Struct[ty; `Reference]);
    `Type("Nil", `Unit) ]

let nil = Construct("Nil", Unit)
let cons h t = Construct("Cons", Struct[h; t])

(* Pattern match over empty or non-empty list. *)
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

let list ns : Hlvm.t list =
  ty_list `Int @
    [ `Function("add", ["n", `Int; "m", `Int], `Int, Var "n" +: Var "m");
      
      `Function("init", ["t", `Reference; "n", `Int], `Reference,
		Let("t", cons (Var "n") (Var "t"),
		    If(Var "n" =: Int 0, Var "t",
		       Apply(Var "init", [Var "t"; Var "n" -: Int 1]))));
      
      list_fold_left `Int `Int;
      
      `Expr(Apply(Var "init", [nil; Int 10])) ] @
    List.map
    (fun n ->
       `Expr
	 (compound
	    [ Printf("\nList.init and fold over %d elements\n", [Int n]);
	      Let("list", Apply(Var "init", [nil; Int n]),
		  Apply(Var "fold_left", [Var "add"; Int 0; Var "list"])) ]))
    ns
       
(** Type of a closure. *)
let ty_closure(ty1, ty2) =
  `Struct[`Function([`Reference; ty1], ty2); `Reference]

(** Apply a closure. *)
let apply(f, x) =
  Apply(GetValue(f, 0), [GetValue(f, 1); x])

let curry : Hlvm.t list =
  let ty_ret = `Struct[`Int; `Float] in
  [ `Function("f_uncurried", ["x", `Int; "y", `Float], ty_ret,
	      Struct[Var "x"; Var "y"]);

    `Type("Int", `Int);

    `Function("f_apply_2", ["env", `Reference; "y", `Float], ty_ret,
	      Apply(Var "f_uncurried", [Cast(Var "env", "Int"); Var "y"]));

    `Function("f_apply_1", ["x", `Int], ty_closure(`Float, ty_ret),
	      Struct[Var "f_apply_2"; Construct("Int", Var "x")]);

    `Expr
      (compound
	 [ Printf("\nTest partial application of curried functions\n", []);
	   Let("g", Apply(Var "f_apply_1", [Int 3]),
	       Struct[apply(Var "g", Float 2.3);
		      apply(Var "g", Float 3.4)]) ]) ]
     
let list_filter ty : Hlvm.t =
  `Function("filter", ["pred", ty_closure(ty, `Bool);
		       "list", `Reference], `Reference,
	    cond_list "list" "h" "t"
	      (Var "list")
	      (Let("t", Apply(Var "filter", [Var "pred"; Var "t"]),
		   If(apply(Var "pred", Var "h"),
		      cons (Var "h") (Var "t"),
		      Var "t"))))

let list_length ty : Hlvm.t =
  `Function("length", ["list", `Reference], `Int,
	    cond_list "list" "h" "t"
	      (Int 0)
	      (Int 1 +: Apply(Var "length", [Var "t"])))

let queens ns =
  let x1 = Var "x1" and x2 = Var "x2" and y1 = Var "y1" and y2 = Var "y2" in
  let ty_pos = `Struct[`Int; `Int] in
  let rec init n f = if n=0 then [] else f(n-1) :: init (n-1) f in
  let ps n = List.flatten (init n (fun i -> init n (fun j -> i, j))) in
  let rec expr_of_list = function
    | [] -> nil
    | (i, j)::t -> cons (Struct[Int i; Int j]) (expr_of_list t) in
  let ps n = expr_of_list(ps n) in
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

      `Function("f", ["", `Reference; "n", `Int], `Int, Var "n" +: Int 1)] @
    List.map
    (fun n ->
       `Expr
	 (compound
	    [ Printf("\nSolve %d-queens problem using lists\n", [Int n]);
	      Apply(Var "search", [Var "f"; Int n; nil; ps n; Int 0]) ]))
    ns

let gc ns =
  let append ty =
    [ `Function("aux", ["a", `Array ty;
			"b", `Array ty;
			"i", `Int;
			"x", ty], `Array ty,
		If(Var "i" <: Length(Var "a"),
		   compound
		     [ Set(Var "b", Var "i", Get(Var "a", Var "i"));
		       Apply(Var "aux", [Var "a";
					 Var "b";
					 Var "i" +: Int 1;
					 Var "x"]) ],
		   Var "b"));

      `Function("append", ["a", `Array ty; "x", ty], `Array ty,
		Apply(Var "aux", [Var "a";
				  Alloc(Length(Var "a") +: Int 1, Var "x");
				  Int 0;
				  Var "x"])) ] in
  let q = 16381 in
  let ty_bkt = `Array(`Struct[`Reference; `Bool]) in
  append (`Struct[`Reference; `Bool]) @
    fill(`Struct[`Int; ty_bkt]) @
    [ `Type("Int", `Int);

      `Function
	("clear1", [ "a", ty_bkt; "i", `Int; "n", `Int ], `Unit,
	 If(Var "i" =: Var "n", Unit,
	    compound
	      [ Let("x", Get(Var "a", Var "i"),
		    Set(Var "a", Var "i",
			Struct[GetValue(Var "x", 0); Bool false]));
		Apply(Var "clear1", [Var "a"; Var "i" +: Int 1; Var "n"]) ]));

      `Function("clear", [ "a", `Array(`Struct[`Int; ty_bkt]);
			   "i", `Int ], `Unit,
		If(Var "i" =: Length(Var "a"), Unit,
		   compound
		     [ Let("nb", Get(Var "a", Var "i"),
			   Apply(Var "clear1", [ GetValue(Var "nb", 1);
						 Int 0;
						 GetValue(Var "nb", 0) ]));
		       Apply(Var "clear", [Var "a"; Var "i" +: Int 1]) ]));

      `Function("abs", ["n", `Int], `Int,
		If(Var "n" >=: Int 0, Var "n", Int 0 -: Var "n"));

      (* Add the reference to the hash table. *)
      `Function("add", [ "a", `Array(`Struct[`Int; ty_bkt]);
			 "p", `Reference ], `Unit,
		Let("h", Apply(Var "abs", [AddressOf(Var "p") %: Int q]),
		    Set(Var "a", Var "h",
			Let("nb", Get(Var "a", Var "h"),
			    Struct
			      [ GetValue(Var "nb", 0) +: Int 1;
				Apply(Var "append",
				      [ GetValue(Var "nb", 1);
					Struct[Var "p"; Bool false ] ])]))));

      `Function
	("mark1", [ "a", ty_bkt;
		    "p", `Reference;
		    "i", `Int ], `Bool,
	 Let("n", Length(Var "a"),
	     If(Var "i" =: Var "n",
		compound
		  [ Printf("WARNING: Pointer not found: ", []);
		    Print(AddressOf(Var "p"));
		    Printf("\n", []);
		    Bool false ],
		Let("p2", Get(Var "a", Var "i"),
		    If(AddressOf(GetValue(Var "p2", 0)) =:
			AddressOf(Var "p"),
		       If(GetValue(Var "p2", 1), Bool false,
			  compound
			    [ Set(Var "a", Var "i",
				  Struct[GetValue(Var "p2", 0);
					 Bool true]);
			      Bool true ]),
		       Apply(Var "mark1", [ Var "a";
					    Var "p";
					    Var "i" +: Int 1 ]))))));

      `Function("mark0", [ "a", `Array(`Struct[`Int; ty_bkt]);
			   "p", `Reference ], `Bool,
		Let("h", Apply(Var "abs", [AddressOf(Var "p") %: Int q]),
		    Apply(Var "mark1", [ GetValue(Get(Var "a", Var "h"), 1);
					 Var "p";
					 Int 0 ])));

      `Function
	("sweep1", [ "a", ty_bkt; "i", `Int; "n", `Int ], `Struct[`Int; ty_bkt],
	 If(Var "i" =: Var "n", Struct[Var "n"; Var "a"],
	    Let("p", Get(Var "a", Var "i"),
		compound
		  [ If(GetValue(Var "p", 1),
		       Apply(Var "sweep1", [ Var "a";
					     Var "i" +: Int 1;
					     Var "n" ]),
		       compound
			 [ Print(GetValue(Var "p", 0));
			   Printf("\n", []);
			   Set(Var "a", Var "i",
			       Get(Var "a", Length(Var "a") -: Int 1));
			   Apply(Var "sweep1", [ Var "a";
						 Var "i";
						 Var "n" -: Int 1 ]) ])])));

      `Function("sweep", [ "a", `Array(`Struct[`Int; ty_bkt]);
			   "i", `Int ], `Unit,
		If(Var "i" =: Length(Var "a"), Unit,
		   compound
		     [ Set(Var "a", Var "i",
			   Let("nb", Get(Var "a", Var "i"),
			       Apply(Var "sweep1",
				     [ GetValue(Var "nb", 1);
				       Int 0;
				       GetValue(Var "nb", 0) ])));
		       Apply(Var "sweep", [ Var "a";
					    Var "i" +: Int 1 ]) ]));

      `Function("loop1", [ "a", `Array(`Struct[`Int; ty_bkt]);
			   "b", `Array `Reference;
			   "n", `Int ], `Unit,
		If(Var "n" =: Length(Var "b"), Unit,
		   Let("x", Construct("Int", Var "n"),
		       compound
			 [ Apply(Var "add", [Var "a"; Var "x"]);
			   Set(Var "b", Var "n", Var "x");
			   Apply(Var "loop1",
				 [ Var "a";
				   Var "b";
				   Var "n" +: Int 1 ])])));

      `Function("loop2", [ "a", `Array(`Struct[`Int; ty_bkt]);
			   "b", `Array `Reference;
			   "i", `Int ], `Unit,
		If(Var "i" =: Length(Var "b"), Unit,
		   compound
		     [ Apply(Var "mark0", [ Var "a";
					    Get(Var "b", Var "i") ]);
		       Apply(Var "loop2", [ Var "a";
					    Var "b";
					    Var "i" +: Int 1 ]) ])) ] @
    List.map
    (fun n ->
       `Expr(Let("a", Alloc(Int q, Struct[Int 0; Alloc(Int 0, Struct[Construct("Int", Int 0); Bool false])]),
		 Let("b", Alloc(Int n, Construct("Int", Int 0)),
		     compound
		       [ Printf("\nHash table benchmark: n=%d\n", [Int n]);
			 Apply(Var "add", [Var "a"; Construct("Int", Int(-1))]);
			 Print(Var "a");
			 Printf("\n", []);
			 Apply(Var "loop1", [ Var "a";
					      Var "b";
					      Int 0 ]);
			 Apply(Var "add", [Var "a"; Construct("Int", Int(-2))]);
			 Apply(Var "clear", [ Var "a"; Int 0 ]);
			 Apply(Var "loop2", [ Var "a";
					      Var "b";
					      Int 0 ]);
			 Apply(Var "sweep", [ Var "a"; Int 0 ]);
		       ]))))
    ns

let bubble_sort ns =
  let ty = `Float in
  [ `Function
      ("bubble_sort_loop2", ["a", `Array ty; "i", `Int; "j", `Int], `Unit,
       If(Var "j" >: Var "i", Unit,
          Let("aj0", Get(Var "a", Var "j"),
              Let("aj1", Get(Var "a", Var "j" +: Int 1),
                  compound
                    [ If(Var "aj0" >=: Var "aj1", Unit,
                        compound
                          [ Set(Var "a", Var "j", Var "aj1");
                            Set(Var "a", Var "j" +: Int 1, Var "aj0") ]);
                      Apply(Var "bubble_sort_loop2",
                            [Var "a"; Var "i"; Var "j" +: Int 1]) ]))));

    `Function
      ("bubble_sort_loop1", ["a", `Array ty; "i", `Int], `Unit,
       If(Var "i" <: Int 0, Unit,
          compound
            [ Apply(Var "bubble_sort_loop2", [Var "a"; Var "i"; Int 0]);
              Apply(Var "bubble_sort_loop1", [Var "a"; Var "i" -: Int 1]) ]));

    `Function
      ("bubble_sort", ["a", `Array ty], `Unit,
       Apply(Var "bubble_sort_loop1", [Var "a"; Length(Var "a") -: Int 2]));

    `Extern("sin", [`Float], `Float);

    `Function
      ("init", ["a", `Array ty; "i", `Int], `Array ty,
       If(Var "i" =: Length(Var "a"), Var "a",
          compound
            [ Set(Var "a", Var "i", Apply(Var "sin", [Float 3.0 *: (FloatOfInt(Var "i") /: FloatOfInt(Length(Var "a")))]));
              Apply(Var "init", [Var "a"; Var "i" +: Int 1]) ])) ] @
    List.map
    (fun n ->
       `Expr
	 (compound
	    [ Printf("\nBubble sort benchmark: n=%d\n", [Int n]);
	      Let("a", Apply(Var "init", [Alloc(Int 10000, Float 0.0); Int 0]),
		  Apply(Var "bubble_sort", [Var "a"])) ]))
    ns

let threads n =
  [ `Function("worker", ["id", `Int], `Unit,
	      Printf("worker id=%d\n", [Var "id"]));

    `Function("mk_thread", ["i", `Int], `Unit,
	      If(Var "i" =: Int 0, Unit,
		 compound
		   [ JoinThread(CreateThread(Var "worker", Var "i"));
		     Apply(Var "mk_thread", [Var "i" -: Int 1]) ]));

    `Expr
      (compound
	 [ Printf("Creating %d threads\n", [Int n]);
	   Apply(Var "mk_thread", [Int n]) ]) ] @

  [ `Function("worker", ["id", `Int], `Unit,
	      Printf("worker id=%d\n", [Var "id"]));

    `Function("mk_thread", ["ij", `Struct[`Int; `Int]], `Unit,
	      Let("i", GetValue(Var "ij", 0),
		  Let("j", GetValue(Var "ij", 1),
		      If(Var "i" =: Var "j", Unit,
			 If(Var "i" +: Int 1 =: Var "j",
			    Apply(Var "worker", [Var "i"]),
			    Let("m", Var "i" +: (Var "j" -: Var "i") /: Int 2,
				Let("thread", CreateThread(Var "mk_thread", Struct[Var "i"; Var "m"]),
				    compound
				      [ Apply(Var "mk_thread", [Struct[Var "m"; Var "j"]]);
					JoinThread(Var "thread") ])))))));

    `Expr
      (compound
	 [ Printf("Creating %d threads\n", [Int n]);
	   Apply(Var "mk_thread", [Struct[Int 0; Int n]]) ]) ] @

    [ `Function
	("fib", ["n", `Int], `Int,
	 let n = Var "n" in
	 If(n >: Int 1,
	    Apply(Var "fib", [n -: Int 2]) +: Apply(Var "fib", [n -: Int 1]),
	    n));
      
      `Function("worker", ["id", `Int], `Unit,
		Printf("%d\n", [Apply(Var "fib", [Var "id"])]));
      
      `Expr(Let("t1", CreateThread(Var "worker", Int n),
		Let("t2", CreateThread(Var "worker", Int n),
		    Let("t3", CreateThread(Var "worker", Int n),
			Let("t4", CreateThread(Var "worker", Int n),
			    Let("t5", CreateThread(Var "worker", Int n),
				Let("t6", CreateThread(Var "worker", Int n),
				    Let("t7", CreateThread(Var "worker", Int n),
					Let("t8", CreateThread(Var "worker", Int n),
					    compound
					      [ JoinThread(Var "t1");
						JoinThread(Var "t2");
						JoinThread(Var "t3");
						JoinThread(Var "t4");
						JoinThread(Var "t5");
						JoinThread(Var "t6");
						JoinThread(Var "t7");
						JoinThread(Var "t8") ]))))))))) ] @
  [ `Function
      ("worker", ["args", `Struct[`Int; `Array `Int; `Int]], `Unit,
       Let("m", GetValue(Var "args", 0),
	   Let("a", GetValue(Var "args", 1),
	       Let("i", GetValue(Var "args", 2),
		   compound
		     [ lockMutex(Var "m");
		       Set(Var "a", Int 0, Int 1 +: Get(Var "a", Int 0));
		       UnlockMutex(Var "m");
		       If(Var "i" =: Int 100000, Unit,
			  Apply(Var "worker",
				[Struct[Var "m";
					Var "a";
					Var "i" +: Int 1]]))]))));

    `Expr(Let("m", CreateMutex,
	      Let("a", Alloc(Int 1, Int 0),
		  compound
		    [ Printf("fork\n", []);
		      Let("args", Struct[Var "m"; Var "a"; Int 1],
			  Let("t1", CreateThread(Var "worker", Var "args"),
			      Let("t2", CreateThread(Var "worker", Var "args"),
				  compound
				    [ JoinThread(Var "t1");
				      JoinThread(Var "t2") ])));
		      Printf("join\n", []);
		      Printf("n=%d\n", [Get(Var "a", Int 0)]) ]))) ]

(** Main program. *)
let () =
  let defs =
    threads 10 @
      tco 1000000 @
      tuples @
      trig @
      curry @
      fib [10; 40] @
      ffib [10.0; 40.0] @
      sieve [1000; 100000000] @
      mandelbrot [1; 77] @
      mandelbrot2 [1; 77] @
      fold [1000; 100000000] @
      queens [8;8;9;10] @
      bubble_sort [100; 100000] @
      gc [1000; 1000000] @
      list [1000; 3000000] @
      [] in
  List.iter Hlvm.eval defs;
  Hlvm.save()
