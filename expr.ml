(** Expressions of a first-order intermediate language. *)
type 'state t =
  | Unit
  | Bool of bool
  | Int of int
  | Float of float
  | Struct of 'state t list
  | GetValue of 'state t * int
  | Var of string
  | Arith of [`Add|`Sub|`Mul|`Div|`Mod] * 'state t * 'state t
  | Cmp of [`Lt|`Le|`Eq|`Ge|`Gt|`Ne] * 'state t * 'state t
  | If of 'state t * 'state t * 'state t
  | Let of string * 'state t * 'state t
  | Alloc of 'state t * Type.t
  | Length of 'state t
  | Get of 'state t * 'state t
  | Set of 'state t * 'state t * 'state t
  | Apply of 'state t * 'state t list
  | Printf of string * 'state t list
  | IntOfFloat of 'state t
  | FloatOfInt of 'state t
  | Return of 'state t * Type.t
  | Construct of string * 'state t
  | IsType of 'state t * string
  | Print of 'state t
  | Exit of 'state t
      (* Unsafe internals: *)
  | AddressOf of 'state t
  | Cast of 'state t * string
  | Free of 'state t
  | Load of Llvm.llvalue * Type.t
  | Store of Llvm.llvalue * 'state t
  | Visit of 'state t
  | Llvalue of Llvm.llvalue * Type.t
  | Magic of 'state t * Type.t

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
