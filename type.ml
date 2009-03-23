(** The type system. *)
type t =
    [ `Unit
    | `Bool
    | `Int
    | `Float
    | `Struct of t list
    | `Array of t
    | `Function of t list * t
    | `Reference ]

let eq (ty1: t) (ty2: t) = ty1=ty2

open Printf

let rec list_to_string f sep () = function
  | [] -> ""
  | [h] -> f () h
  | h::t -> sprintf "%a%s%a" f h sep (list_to_string f sep) t

let rec to_string () : t -> string = function
  | `Unit -> "`Unit"
  | `Bool -> "`Bool"
  | `Int -> "`Int"
  | `Float -> "`Float"
  | `Struct tys -> sprintf "`Struct[%a]" to_strings tys
  | `Array ty -> sprintf "`Array(%a)" to_string ty
  | `Function(tys_arg, ty_ret) ->
      sprintf "`Function([%a], %a)" to_strings tys_arg to_string ty_ret
  | `Reference -> "`Reference"
and to_strings tys = list_to_string to_string "; " tys
