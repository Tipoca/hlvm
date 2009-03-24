(** Expressions of a first-order intermediate language. *)
type t =
  | Unit
      (** The value () of the type unit. *)
  | Bool of bool
      (** A literal boolean value. *)
  | Int of int
      (** A literal native int value. *)
  | Float of float
      (** A literal 64-bit floating point value. *)
  | Struct of t list
      (** A struct literal. *)
  | GetValue of t * int
      (** Extract a field from a struct. *)
  | Var of string
      (** A variable. *)
  | Arith of [`Add|`Sub|`Mul|`Div|`Mod] * t * t
      (** A binary arithmetic operation. *)
  | Cmp of [`Lt|`Le|`Eq|`Ge|`Gt|`Ne] * t * t
      (** A comparison. *)
  | If of t * t * t
      (** An "if" expression. *)
  | Let of string * t * t
      (** Evaluate the first expression, bind the resulting value to the given
	  variable name and evaluate the last expression. *)
  | Alloc of t * Type.t
      (** Allocate an array to store the given number of elements of the given
	  type. The array is initialized to all-bits zero. *)
  | Length of t
      (** Find the length of the given array. *)
  | Get of t * t
      (** Get(a, i) gets the element at index "i" from the array "a". *)
  | Set of t * t * t
      (** Set(a, i, x) sets the element at index "i" in the array "a" to
	  "x". *)
  | Apply of t * t list
      (** Applying the given function pointer to the given list of
	  arguments. *)
  | Printf of string * t list
      (** Call C printf (unsafe). *)
  | IntOfFloat of t
      (** Convert a float to an int. *)
  | FloatOfInt of t
      (** Convert an int to a float. *)
  | Construct of string * t
      (** Construct a boxed value. *)
  | IsType of t * string
      (** Check the type of a value against the type with the given name. *)
  | Print of t
      (** Generic printing of any value. *)
  | Exit of t
      (** Call the C "exit" function. *)
  | AddressOf of t
      (** For internal use only. Return the address of the given reference
	  type as a native integer. *)
  | Cast of t * string
      (** Cast the given reference value to the given type, returning the
	  argument of the type constructor (unsafe). *)
  | Free of t
      (** For internal use only. Deallocate the given value. *)
  | Load of Llvm.llvalue * Type.t
      (** For internal use only. Load a value from an LLVM global variable. *)
  | Store of Llvm.llvalue * t
      (** For internal use only. Store a value to an LLVM global variable. *)
  | Visit of t
      (** For internal use only. Obtain the GC visit function associated with
	  the type of the given value. *)
  | Llvalue of Llvm.llvalue * Type.t
      (** For internal use only. A literal LLVM value. *)
  | Magic of t * Type.t
      (** For internal use only. Convert between the two kinds of reference
	  types: arrays and boxed values. *)
  | Return of t * Type.t
      (** For internal use only. Used to propagate tail calls. *)

(** Helper operators. *)
let ( <: ) f g = Cmp(`Lt, f, g)
let ( <=: ) f g = Cmp(`Le, f, g)
let ( =: ) f g = Cmp(`Eq, f, g)
let ( <>: ) f g = Cmp(`Ne, f, g)
let ( >=: ) f g = Cmp(`Ge, f, g)
let ( >: ) f g = Cmp(`Gt, f, g)
let ( +: ) f g = Arith(`Add, f, g)
let ( -: ) f g = Arith(`Sub, f, g)
let ( *: ) f g = Arith(`Mul, f, g)
let ( /: ) f g = Arith(`Div, f, g)
let ( %: ) f g = Arith(`Mod, f, g)
let ( &&: ) f g = If(f, g, Bool false)
let ( ||: ) f g = If(f, Bool true, g)
let rec compound = function
  | [] -> Unit
  | [h] -> h
  | h::t -> Let("", h, compound t)

open Printf

let logic_to_string () = function
  | `And -> "`And"
  | `Or -> "`Or"

let arith_to_string () = function
  | `Add -> "`Add"
  | `Sub -> "`Sub"
  | `Mul -> "`Mul"
  | `Div -> "`Div"
  | `Mod -> "`Mod"

let cmp_to_string () = function
  | `Lt -> "`Lt"
  | `Le -> "`Le"
  | `Eq -> "`Eq"
  | `Ne -> "`Ne"
  | `Ge -> "`Ge"
  | `Gt -> "`Gt"

let rec list_to_string f sep () = function
  | [] -> ""
  | [h] -> f () h
  | h::t -> sprintf "%a%s%a" f h sep (list_to_string f sep) t

let rec to_string () = function
  | Unit -> "Unit"
  | Bool b -> sprintf "Bool %b" b
  | Int n -> sprintf "Int %d" n
  | Float x -> sprintf "Float %g" x
  | Struct xs ->
      sprintf "Struct[%a]" (to_strings "; ") xs
  | GetValue(s, i) -> sprintf "GetValue(%a, %d)" to_string s i
  | Var s -> sprintf "Var \"%s\"" (String.escaped s)
  | Arith(op, f, g) ->
      sprintf "Arith(%a, %a, %a)" arith_to_string op to_string f to_string g
  | Cmp(op, f, g) ->
      sprintf "Cmp(%a, %a, %a)" cmp_to_string op to_string f to_string g
  | If(p, t, f) ->
      sprintf "If(%a, %a, %a)" to_string p to_string t to_string f
  | Let(x, f, g) ->
      sprintf "Let(\"%s\", %a, %a)" (String.escaped x) to_string f to_string g
  | Alloc(f, ty) ->
      sprintf "Alloc(%a, %a)" to_string f Type.to_string ty
  | Length f ->
      sprintf "Length(%a)" to_string f
  | Get(a, i) ->
      sprintf "Get(%a, %a)" to_string a to_string i
  | Set(a, i, x) ->
      sprintf "Set(%a, %a, %a)" to_string a to_string i to_string x
  | Apply(f, xs) ->
      sprintf "Apply(%a, [%a])" to_string f (to_strings "; ") xs
  | Printf(s, fs) ->
      sprintf "Printf(\"%s\", [%a])" (String.escaped s) (to_strings "; ") fs
  | IntOfFloat f ->
      sprintf "IntOfFloat(%a)" to_string f
  | FloatOfInt f ->
      sprintf "FloatOfInt(%a)" to_string f
  | Return(f, ty) ->
      sprintf "Return(%a, %a)" to_string f Type.to_string ty
  | Construct(constr, f) ->
      sprintf "Construct(\"%s\", %a)" constr to_string f
  | IsType(f, constr) ->
      sprintf "IsType(%a, \"%s\")" to_string f constr
  | Cast(f, constr) ->
      sprintf "Cast(%a, \"%s\")" to_string f constr
  | Visit f ->
      sprintf "Visit(%a)" to_string f
  | Print f ->
      sprintf "Print(%a)" to_string f
  | Exit f ->
      sprintf "Exit(%a)" to_string f
  | Load(_, ty) ->
      sprintf "Load(<llvalue>, %a)" Type.to_string ty
  | Store(_, f) ->
      sprintf "Store(<llvalue>, %a)" to_string f
  | AddressOf f ->
      sprintf "AddressOf(%a)" to_string f
  | Free f ->
      sprintf "Free(%a)" to_string f
  | Llvalue(_, ty) ->
      sprintf "Llvalue(<llvalue>, %a)" Type.to_string ty
  | Magic(f, ty) ->
      sprintf "Magic(%a, %a)" to_string f Type.to_string ty
and to_strings sep = list_to_string to_string sep

let rec rewrite r = function
  | Struct es -> Struct(List.map r es)
  | GetValue(e, i) -> GetValue(r e, i)
  | Arith(op, f, g) -> Arith(op, r f, r g)
  | Cmp(op, f, g) -> Cmp(op, r f, r g)
  | If(p, t, f) -> If(r p, r t, r f)
  | Let(x, body, rest) -> Let(x, r body, r rest)
  | Alloc(n, ty) -> Alloc(r n, ty)
  | Length e -> Length(r e)
  | Get(a, i) -> Get(r a, r i)
  | Set(a, i, x) -> Set(r a, r i, r x)
  | Apply(f, xs) -> Apply(r f, List.map r xs)
  | Printf(s, xs) -> Printf(s, List.map r xs)
  | IntOfFloat x -> IntOfFloat(r x)
  | FloatOfInt x -> FloatOfInt(r x)
  | Construct(c, v) -> Construct(c, r v)
  | IsType(v, c) -> IsType(r v, c)
  | Print e -> Print(r e)
  | Exit x -> Exit(r x)
  | AddressOf x -> AddressOf(r x)
  | Cast(v, c) -> Cast(r v, c)
  | Free x -> Free(r x)
  | Return(x, ty) -> Return(r x, ty)
  | Visit x -> Visit(r x)
  | Magic(v, ty) -> Magic(r v, ty)

  | Unit
  | Bool _
  | Int _
  | Float _
  | Var _
  | Load _
  | Store _
  | Llvalue _ as e -> e

let rec unroll_rule f params body = function
  | Let(x, body, rest) as e when x=f -> e
  | Apply(Var g, args) when f=g ->
      let rec aux (i, t) param =
	i+1, Let(param, GetValue(Var " args", i), t) in
      let _, body = List.fold_left aux (0, body) params in
      Let(" args", Struct args, body)
  | e -> rewrite (unroll_rule f params body) e

let unroll f args body =
  rewrite (unroll_rule f (List.map fst args) body) body
