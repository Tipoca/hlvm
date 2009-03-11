open Printf
open Llvm
open Llvm_executionengine
open Llvm_target
open Llvm_scalar_opts
open Llvm_analysis

open Expr

module List = struct
  include List

  let iteri f xs =
    ignore(fold_left (fun i x -> (f i x: unit); i+1) 0 xs)

  let mapi f xs =
    let _, ys = fold_left (fun (i, ys) x -> i+1, f i x::ys) (0, []) xs in
    List.rev ys

  let init n f =
    Array.to_list(Array.init n f)

  let rec between sep xs =
    match xs with
    | [] -> []
    | [x] -> [x]
    | x::xs -> x::sep::between sep xs
end

let debug = ref false

external build_extractvalue :
  llvalue -> int -> string -> llbuilder -> llvalue =
      "llvm_build_extractvalue"
      
external build_insertvalue :
  llvalue -> llvalue -> int -> string -> llbuilder -> llvalue =
      "llvm_build_insertvalue"

external enable_tail_call_opt : unit -> unit = "llvm_enable_tail_call_opt"

let mk_struct state vs =
  let llty = struct_type (Array.of_list(List.map type_of vs)) in
  let aux (i, s) x = i+1, build_insertvalue s x i "" state#bb in
  snd(List.fold_left aux (0, undef llty) vs)

let () = enable_tail_call_opt()

let extractvalue state s i =
  build_extractvalue s i "" state#bb

(** Type of a C-compatible null-terminated string. *)
let string_type = pointer_type i8_type

(** Type of a native int. *)
let int_type = match Sys.word_size with
  | 32 -> i32_type
  | 64 -> i64_type
  | _ -> failwith "Unknown word size"

let is_struct = function
  | `Array _ | `Struct _ | `Reference -> true
  | `Unit | `Bool | `Int | `Float | `Function _ -> false

let is_ref_type = function
  | `Array _ | `Reference -> true
  | `Struct _ | `Unit | `Bool | `Int | `Float | `Function _ -> false

module Ref = struct
(** Representation of reference types. *)
  let lltype =
    struct_type[|string_type; int_type; string_type|]

  let llty = 0
  let tag = 1
  let data = 2

  let mk state llty tag data =
    mk_struct state [ state#bitcast llty string_type;
		      tag;
		      state#bitcast data string_type ]
end

(** Convert a type from our type system into LLVM's type system. *)
let rec lltype_of : Type.t -> lltype = function
  | `Unit | `Int -> int_type
  | `Bool -> i1_type
  | `Float -> double_type
  | `Struct tys -> struct_type_of tys
  | `Function ty -> pointer_type(function_type_of ty)
  | `Array _ | `Reference -> Ref.lltype

(** Representation of function pointers. *)
and function_type_of = function
  | ty_args, ty_ret when is_struct ty_ret ->
      function_type (lltype_of `Unit)
        (Array.of_list (pointer_type(lltype_of ty_ret) ::
                          List.map lltype_of ty_args))
  | ty_args, ty_ret ->
      function_type (lltype_of ty_ret)
	(Array.of_list (List.map lltype_of ty_args))

(** Representation of structs. *)
and struct_type_of tys =
  struct_type (Array.of_list (List.map lltype_of tys))

(** Run-time types. *)
module RTType = struct
  (** The lltype of our run-time types. *)
  let lltype =
    lltype_of
      (`Struct[ `Function([`Function([`Reference], `Unit);
			   `Reference], `Unit);
		`Function([`Reference], `Unit) ])

  let visit = 0
  let print = 1
end

let print_type_of v =
  printf "%s\n%!" (string_of_lltype(type_of v))

(* Create constants. *)
let int n = const_int int_type n
let int32 n = const_int i32_type n
let float64 x = const_float (lltype_of `Float) x
let null = const_null string_type

let find k kvs =
  try List.assoc k kvs with Not_found ->
    eprintf "Unknown '%s'\n%!" k;
    raise Not_found



(** Global LLVM module. *)
let m = create_module "toplevel"

(** Global LLVM module provider. *)
let mp = ModuleProvider.create m

(** Global LLVM execution engine. *)
let ee = ExecutionEngine.create mp

(** The shadow stack is an array of reference types. *)
(* FIXME: Should be dynamically resized. *)
let stack =
  define_global "shadow_stack" (const_null(lltype_of(`Array `Reference))) m

(** Number of references on the shadow stack. *)
let stack_depth = define_global "shadow_stack_depth" (int 0) m

(** The visit stack is an array of unvisited reference types. *)
(* FIXME: Should be dynamically resized. *)
let visit_stack =
  define_global "visit_stack" (const_null(lltype_of(`Array `Reference))) m

(** Number of unvisited references on the visit stack. *)
let n_visit = define_global "n_visit" (int 0) m

(** The allocated list is an array of reference types and their boolean
    states (marked or unmarked). *)
(* FIXME: Should be dynamically resized. *)
let allocated =
  define_global "allocated"
    (const_null(lltype_of(`Array(`Struct[`Reference; `Bool])))) m

(** Number of allocated references. *)
let n_allocated = define_global "n_allocated" (int 0) m

(** Number of allocations required to incur a garbage collection. *)
let quota = define_global "quota" (int 0) m

let llputchar =
  declare_function "putchar" (function_type int_type [|int_type|]) m

let llexit =
  declare_function "exit" (function_type void_type [|int_type|]) m

let llprintf =
  declare_function "printf" (var_arg_function_type int_type [|string_type|]) m

let cc = CallConv.fast

type vars =
    { vals: (string * (llvalue * Type.t)) list }

let vars = { vals = [] }

(** Container of internal types such as wrapper reference types for arrays. *)
let types = Hashtbl.create 1

(** Container of internal functions such as visitors to traverse the heap. *)
let functions = Hashtbl.create 1

let find_type name =
  try Hashtbl.find types name with Not_found as e ->
    eprintf "Type '%s' not found\n%!" name;
    raise e

let add_val x vars = { vals = x :: vars.vals }

let push self stack depth v =
  if !debug then
    printf "state#push\n%!";
  let d = self#load depth [int 0] in
  let data = extractvalue self (self#load stack [int 0]) Ref.data in
  let data = self#bitcast data (pointer_type(type_of v)) in
  self#store data [d] v;
  self#store depth [int 0] (build_add (int 1) d "" self#bb)

let gc_restore self =
  if !debug then
    printf "state#restore\n%!";
  self#store stack_depth [int 0] self#odepth

(** Create a state object. *)
class state func = object (self : 'self)
  val blk = entry_block func
  val odepth = int 0
  val gc_enabled = true
  method blk = blk
  method bb = builder_at_end blk
  method gep a ns = build_gep a (Array.of_list ns) "" self#bb
  method load a ns = build_load (self#gep a ns) "" self#bb
  method store a ns x = ignore(build_store x (self#gep a ns) self#bb)
  method malloc ty n = build_array_malloc ty n "" self#bb
  method free x = ignore(build_free x self#bb)
  method define_global x v = define_global x v m
  method mk s = {< blk = append_block s func >}
  method ret v = ignore(build_ret v self#bb)
  method br (s: 'self) = ignore(build_br s#blk self#bb)
  method bitcast v ty = build_bitcast v ty "" self#bb
  method call cc f args =
    let call = build_call f (Array.of_list args) "" self#bb in
    set_instruction_call_conv cc call;
    call
  method sret = param func 0
  method alloca ty =
    build_alloca ty "" (builder_at_end(entry_block func))
  method gc_root v =
    if gc_enabled then
      push self stack stack_depth v
  method gc_alloc v =
    if gc_enabled then
      push self allocated n_allocated (mk_struct self [v; const_int i1_type 0])
  method gc_restore() =
    if gc_enabled then
      gc_restore self
  method no_gc = {< gc_enabled = false >}
  method odepth = odepth
  method set_depth d = {< odepth = d >}
end

(** Create a state object and save the current shadow stack depth. *)
let mk_state func =
  let state = new state func in
  state#set_depth(state#load stack_depth [int 0])

(** Create a unique string based upon the given string. *)
let uniq =
  let m = Hashtbl.create 1 in
  let rec aux s =
    try
      Hashtbl.find m s;
      aux(s ^ "'")
    with Not_found ->
      Hashtbl.add m s ();
      s in
  aux

exception Returned

type 'a t =
    [ `UnsafeFunction of string * (string * Type.t) list * Type.t * 'a Expr.t
    | `Function of string * (string * Type.t) list * Type.t * 'a Expr.t
    | `Expr of 'a Expr.t * Type.t
    | `Extern of string * Type.t list * Type.t
    | `Type of string * Type.t ]

(** Compile an expression in the context of current vars into the given
    LLVM state. *)
let rec expr vars state e =
  if !debug then
    printf "-> expr %s\n%!" (Expr.to_string () e);
  let state, (x, ty_x) as ret = expr_aux vars state e in
  if !debug then
    printf "<- %s\n%!" (string_of_lltype(type_of x));
  ret
and expr_aux vars state = function
  | Unit -> state, (int 0, `Unit)
  | Bool b -> state, (const_int i1_type (if b then 1 else 0), `Bool)
  | Int n -> state, (int n, `Int)
  | Float x -> state, (float64 x, `Float)
  | Struct fs ->
      let state, (fs, tys_f) = exprs vars state fs in
      state, (mk_struct state fs, `Struct tys_f)
  | GetValue(s, i) ->
      let state, (s, ty_s) = expr vars state s in
      begin
	match ty_s with
	| `Struct tys ->
	    let v = extractvalue state s i in
	    state, (v, List.nth tys i)
	| _ -> assert false
      end
  | Construct(f, x) ->
      let llty, ty = find_type f in
      let state, (x, ty_x) = expr vars state x in
      assert(Type.eq ty ty_x);
      let state, s =
	match ty_x with
	| `Unit -> state, Ref.mk state llty (int 0) null
	| _ ->
	    let state, px = malloc state (lltype_of ty_x) (int 1) in
	    state#store px [int 0] x;
	    let s = Ref.mk state llty (int 0) px in
	    gc_root vars state s `Reference;
	    state#gc_alloc s;
	    state, s in
      state, (s, `Reference)
  | IsType(f, ty_name) ->
      let state, (f, ty_f) = expr vars state f in
      assert(Type.eq ty_f `Reference);
      let llty_f = extractvalue state f Ref.llty in
      let llty_f = state#bitcast llty_f (pointer_type RTType.lltype) in
      let llty, ty = find_type ty_name in
      state, (build_icmp Icmp.Eq llty_f llty "" state#bb, `Bool)
  | Cast(f, ty_name) ->
      (* FIXME: This is unsafe. *)
      let state, (f, ty_f) = expr vars state f in
      assert(Type.eq ty_f `Reference);
      let llty, ty = find_type ty_name in
      let v = extractvalue state f Ref.data in
      let v = state#bitcast v (pointer_type(lltype_of ty)) in
      let v = state#load v [int 0] in
      gc_root vars state v ty;
      state, (v, ty)
  | Var x ->
      let x, ty_x = find x vars.vals in
      state, (x, ty_x)
  | Arith(op, f, g) ->
      let state, (f, f_ty), (g, g_ty) = expr2 vars state f g in
      let build, ty_ret =
	match op, (f_ty, g_ty) with
	| `Add, (`Int, `Int | `Float, `Float) -> build_add, f_ty
	| `Sub, (`Int, `Int | `Float, `Float) -> build_sub, f_ty
	| `Mul, (`Int, `Int | `Float, `Float) -> build_mul, f_ty
	| `Div, (`Int, `Int) -> build_sdiv, `Int
	| `Mod, (`Int, `Int) -> build_srem, `Int
	| `Div, (`Float, `Float) -> build_fdiv, `Float
	| _ -> invalid_arg "expr.arith" in
      state, (build f g "" state#bb, ty_ret)
  | Cmp(op, f, g) ->
      let state, (f, f_ty), (g, g_ty) = expr2 vars state f g in
      let build =
	match op, (f_ty, g_ty) with
	| `Lt, (`Int, `Int) -> build_icmp Icmp.Slt
	| `Le, (`Int, `Int) -> build_icmp Icmp.Sle
	| `Eq, (`Int, `Int) -> build_icmp Icmp.Eq
	| `Ne, (`Int, `Int) -> build_icmp Icmp.Ne
	| `Ge, (`Int, `Int) -> build_icmp Icmp.Sge
	| `Gt, (`Int, `Int) -> build_icmp Icmp.Sgt
	| `Lt, (`Float, `Float) -> build_fcmp Fcmp.Olt
	| `Le, (`Float, `Float) -> build_fcmp Fcmp.Ole
	| `Eq, (`Float, `Float) -> build_fcmp Fcmp.Oeq
	| `Ne, (`Float, `Float) -> build_fcmp Fcmp.One
	| `Ge, (`Float, `Float) -> build_fcmp Fcmp.Oge
	| `Gt, (`Float, `Float) -> build_fcmp Fcmp.Ogt
	| _ -> invalid_arg "expr.cmp" in
      state, (build f g "" state#bb, `Bool)
  | Return(If(p, t, f), ty_ret) ->
      (* Tail expressions in both branches. *)
      let state, (p, ty_p) = expr vars state p in
      assert(Type.eq ty_p `Bool);
      let t_state, f_state = state#mk "pass", state#mk "fail" in
      let _ = build_cond_br p t_state#blk f_state#blk state#bb in
      return vars t_state t ty_ret;
      return vars f_state f ty_ret;
      raise Returned
  | If(p, t, f) ->
      let state, (p, ty_p) = expr vars state p in
      assert(Type.eq ty_p `Bool);
      let t_state, f_state = state#mk "pass", state#mk "fail" in
      let _ = build_cond_br p t_state#blk f_state#blk state#bb in
      let k_state = state#mk "cont" in
      let t_state, (t, ty_t) = expr vars t_state t in
      t_state#br k_state;
      let f_state, (f, ty_f) = expr vars f_state f in
      f_state#br k_state;
      assert(Type.eq ty_t ty_f);
      k_state, (build_phi [t, t_state#blk; f, f_state#blk] "" k_state#bb, ty_t)
  | Return(Let(x, f, g), ty_ret) ->
      (* Tail expression in "rest". *)
      expr vars state (Let(x, f, Return(g, ty_ret)))
  | Let(x, f, g) ->
      let state, (f, ty_f) = expr vars state f in
      let state, (g, ty_g) = expr (add_val (x, (f, ty_f)) vars) state g in
      state, (g, ty_g)
  | Alloc(n, ty) ->
      let state, (n, ty_n) = expr vars state n in
      assert(Type.eq ty_n `Int);
      let state, data = malloc state (lltype_of ty) n in
      let a, ty_a = Ref.mk state (mk_array_type ty) n data, `Array ty in
      gc_root vars state a ty_a;
      state#gc_alloc a;
      state, (a, ty_a)
  | Length a ->
      let state, (a, ty_a) = expr vars state a in
      assert(match ty_a with `Array _ -> true | _ -> false);
      state, (extractvalue state a Ref.tag, `Int)
  | Get(a, i) ->
      let state, (a, ty_a), (i, ty_i) = expr2 vars state a i in
      let ty_elt = match ty_a with
	| `Array ty -> ty
	| _ -> assert false in
      assert(Type.eq ty_i `Int);
      let data = extractvalue state a Ref.data in
      let data = state#bitcast data (pointer_type(lltype_of ty_elt)) in
      let x, ty_x = state#load data [i], ty_elt in
      gc_root vars state x ty_x;
      state, (x, ty_x)
  | Set(a, i, x) ->
      let state, (a, ty_a), (i, ty_i), (x, ty_x) =
	expr3 vars state a i x in
      assert(Type.eq ty_a (`Array ty_x));
      assert(Type.eq ty_i `Int);
      let data = extractvalue state a Ref.data in
      let data = state#bitcast data (pointer_type(lltype_of ty_x)) in
      state#store data [i] x;
      state, (int 0, `Unit)
  | Return(Apply(f, args), ty_ret) ->
      let state, (f, ty_f) = expr vars state f in
      let state, (args, tys_arg) = exprs vars state args in
      state#gc_restore();
      let call = match ty_f with
	| `Function(tys_arg', ty_ret') when is_struct ty_ret' ->
	    (* Tail call returning struct. Pass the sret given to us by our
	       caller on to our tail callee. *)
	    assert(List.for_all2 Type.eq tys_arg tys_arg');
	    assert(Type.eq ty_ret ty_ret');
            state#call cc f (state#sret :: args)
        | `Function(tys_arg', ty_ret') ->
	    (* Tail call returning single value. *)
	    assert(List.for_all2 Type.eq tys_arg tys_arg');
	    assert(Type.eq ty_ret ty_ret');
	    state#call cc f args
        | _ -> assert false in
      set_tail_call true call;
      state#ret call;
      raise Returned
  | Apply(f, args) ->
      let state, (f, ty_f) = expr vars state f in
      let state, (args, tys_arg) = exprs vars state args in
      let ret, ty_ret =
	match ty_f with
	| `Function(tys_arg', ty_ret) when is_struct ty_ret ->
	    (* Non-tail call returning multiple values. *)
            assert(List.for_all2 Type.eq tys_arg tys_arg');
            let ret = state#alloca (lltype_of ty_ret) in
            let _ = state#call cc f (ret :: args) in
            state#load ret [int 0], ty_ret
	| `Function(tys_arg', ty_ret) ->
	    (* Non-tail call returning single value. *)
	    assert(List.for_all2 Type.eq tys_arg tys_arg');
	    state#call cc f args, ty_ret
	| _ -> assert false in
      gc_root vars state ret ty_ret;
      state, (ret, ty_ret)
  | Printf(spec, args) ->
      let spec =
	let str = state#define_global "buf" (const_stringz spec) in
	state#gep str [int32 0; int 0] in
      let state, (args, _) = exprs vars state args in
      let ext x =
	if type_of x <> float_type then x else
	  build_fpext x double_type "" state#bb in
      let args = List.map ext args in
      ignore(state#call CallConv.c llprintf (spec::args));
      state, (int 0, `Unit)
  | IntOfFloat f ->
      let state, (f, ty_f) = expr vars state f in
      assert(Type.eq ty_f `Float);
      state, (build_fptosi f (lltype_of `Int) "" state#bb, `Int)
  | FloatOfInt f ->
      let state, (f, ty_f) = expr vars state f in
      assert(Type.eq ty_f `Int);
      state, (build_sitofp f (lltype_of `Float) "" state#bb, `Float)
  | Print f ->
      let state, (f, ty_f) = expr vars state f in
      let vars = add_val ("x", (f, ty_f)) vars in
      begin
	match ty_f with
	| `Unit -> expr vars state (Printf("()", []))
	| `Bool ->
	    expr vars state
	      (If(Var "x", Printf("true", []), Printf("false", [])))
	| `Int -> expr vars state (Printf("%d", [Var "x"]))
	| `Float -> expr vars state (Printf("%g", [Var "x"]))
	| `Struct tys ->
	    let aux i = Print(GetValue(Var "x", i)) in
	    let xs = List.init (List.length tys) aux in
	    expr vars state
	      (compound
		 [ Printf("(", []);
		   compound(List.between (Printf(", ", [])) xs);
		   Printf(")", []) ])
	| `Function _ -> expr vars state (Printf("<fun>", []))
	| `Array _ -> expr vars state (Printf("[|...|]", []))
	| `Reference ->
	    let llty = extractvalue state f Ref.llty in
	    let llty = state#bitcast llty (pointer_type RTType.lltype) in
	    let llty = state#load llty [int 0] in
	    let p = extractvalue state llty RTType.print in
	    let ty_p = `Function([ty_f], `Unit) in
	    let vars = add_val ("p", (p, ty_p)) vars in
	    expr vars state (Apply(Var "p", [Var "x"]))
      end
  | Visit f ->
      let state, (f, ty_f) = expr vars state f in
      begin
	match ty_f with
	| `Reference ->
	    let llty = extractvalue state f Ref.llty in
	    let llty = state#bitcast llty (pointer_type RTType.lltype) in
	    let llty = state#load llty [int 0] in
	    let p = extractvalue state llty RTType.visit in
	    state, (p, `Function([`Function([`Reference], `Unit);
				  `Reference], `Unit))
	| ty -> assert false
      end
  | Free f ->
      let state, (f, ty_f) = expr vars state f in
      assert(is_ref_type ty_f);
      state#free (extractvalue state f Ref.data);
      state, (int 0, `Unit)
  | Exit f ->
      let state, (f, ty_f) = expr vars state f in
      ignore(state#call CallConv.c llexit [f]);
      state, (int 0, `Unit)
  | Load(addr, ty) -> state, (state#load addr [int 0], ty)
  | Store(addr, f) ->
      let state, (f, ty_f) = expr vars state f in
      state#store addr [int 0] f;
      state, (int 0, `Unit)
  | AddressOf f ->
      let state, (f, ty_f) = expr vars state f in
      let ptr = extractvalue state f Ref.data in
      let ptr = build_ptrtoint ptr int_type "" state#bb in
      state, (ptr, `Int)
  | Llvalue(v, ty) -> state, (v, ty)
  | Magic(f, ty) ->
      let state, (f, ty_f) = expr vars state f in
      assert(is_ref_type ty_f);
      state, (f, ty)
  | Return(f, ty_ret) when is_struct ty_ret ->
      let state, (f, ty_f) = expr vars state f in
      assert(Type.eq ty_ret ty_f);
      state#store state#sret [int 0] f;
      state#gc_restore();
      state#ret (int 0);
      raise Returned
  | Return(f, ty_ret) ->
      let state, (f, ty_f) = expr vars state f in
      assert(Type.eq ty_ret ty_f);
      state#gc_restore();
      state#ret f;
      raise Returned
and expr2 vars state f g =
  let state, f = expr vars state f in
  let state, g = expr vars state g in
  state, f, g
and expr3 vars state f g h =
  let state, f = expr vars state f in
  let state, g = expr vars state g in
  let state, h = expr vars state h in
  state, f, g, h
and exprs vars state fs =
  let aux (state, rfs, rtys_f) f =
    let state, (f, ty_f) = expr vars state f in
    state, f::rfs, ty_f::rtys_f in
  let state, rfs, rtys_f = List.fold_left aux (state, [], []) fs in
  state, (List.rev rfs, List.rev rtys_f)
and return vars state f ty_f =
  try
    let _ = expr vars state (Return(f, ty_f)) in
    failwith "Internal error: return"
  with Returned ->
    ()

and malloc state ty n =
  let data = state#malloc ty n in
  let state, _ =
    let data = build_ptrtoint data int_type "" state#bb in
    expr (add_val ("data", (data, `Int)) vars) state
      (If(Cmp(`Eq, Var "data", Int 0),
	  compound[Printf("Out of memory\n", []); Exit(Int 1)],
	  Unit)) in
  state, data

(** Register all reference types in the given value as live roots for the
    GC. *)
and gc_root vars state v ty =
  if !debug then
    printf "gc_root %s\n%!" (Type.to_string () ty);
  match ty with
  | `Unit | `Bool | `Int | `Float | `Function _ -> ()
  | `Struct tys ->
      let f i ty =
	gc_root vars state (extractvalue state v i) ty in
      List.iteri f tys
  | `Array _  | `Reference ->
      state#gc_root v

(** Define a function with the given calling convention, name, arguments
    and return type using the function argument "k" to fill in the body of the
    defined function. *)
and defun vars cc f args ty_ret k =
  let tys_args = List.map snd args in
  let ty = tys_args, ty_ret in
  let llvm_f = define_function f (function_type_of ty) m in
  set_function_call_conv cc llvm_f;
  
  let entry = mk_state llvm_f in
  let start = entry#mk "start" in

  (* Bind the function name. *)
  let vars = add_val (f, (llvm_f, `Function ty)) vars in

  (* Bind the function arguments in the context of its body. *)
  let _, vals' =
    let aux (i, args) (arg, ty) =
      i+1, (arg, (param llvm_f i, ty))::args in
    let i = if is_struct ty_ret then 1 else 0 in
    List.fold_left aux (i, vars.vals) args in

  k { vals = vals' } start;

  let _ = entry#br start in

  Llvm_analysis.assert_valid_function llvm_f;
  (*
    Llvm_analysis.view_function_cfg llvm_f;
  *)
  vars

(** Compile a top-level definition. *)
and def vars = function
  | `UnsafeFunction(f, args, ty_ret, body) ->
      if !debug then
	eprintf "def %s\n%!" f;

      defun vars cc f args ty_ret
	(fun vars state ->
	   let state = state#no_gc in
	   return vars state body ty_ret)
  | `Function(f, args, ty_ret, body) ->
      if !debug then
	eprintf "def %s\n%!" f;

      defun vars cc f args ty_ret
	(fun vars state ->
	   let state, (ps, ty_ps) =
	     expr vars state
	       (Struct(List.map (fun (s, _) -> Var s) vars.vals)) in
	   gc_root vars state ps ty_ps;
	   let state, _ =
	     expr vars state
	       (If(Load(n_allocated, `Int) <=: Load(quota, `Int), Unit,
		   Apply(Var "gc", []))) in
	   return vars state body ty_ret)
  | `Expr(f, ty_f) ->
      if !debug then
	eprintf "def <expr>\n%!";

      let ty_handler = function_type void_type [|int_type; string_type|] in
      let stackoverflow_install_handler =
	declare_function "stackoverflow_install_handler"
	  (function_type int_type
	     [|pointer_type ty_handler; string_type; int_type|]) m in
      let stackoverflow_deinstall_handler =
	declare_function "stackoverflow_deinstall_handler"
	  (function_type void_type [||]) m in

      let llvm_handler =
	let llvm_f = define_function "handler" ty_handler m in
	let state = mk_state llvm_f in
	String.iter
	  (fun c ->
	     ignore(state#call CallConv.c llputchar [int(Char.code c)]))
	  "Stack overflow\n";
	let _ = state#call CallConv.c llexit [int 1] in
	let _ = build_ret_void state#bb in
	Llvm_analysis.assert_valid_function llvm_f;
	llvm_f in

      let f_name = "main" in
      let vars' =
	defun vars CallConv.c f_name ["", `Unit] `Unit
	  (fun vars state ->
	     let size = 16384 in
	     let stack = state#alloca (array_type i8_type size) in
	     let stack = state#bitcast stack string_type in
	     let _ =
	       state#call CallConv.c stackoverflow_install_handler
		 [llvm_handler; stack; int size] in
	     let f =
	       compound
		 [ Printf("- : <type> = ", []);
		   Print f;
		   Printf("\n", []) ] in
	     let state, _ = expr vars state f in
	     state#gc_restore();
	     let state, _ = expr vars state (Apply(Var "gc", [])) in
	     let state, _ =
	       expr
		 (add_val ("n", (state#load n_allocated [int 0], `Int)) vars)
		 state
		 (Printf("Allocated blocks: %d\n", [Var "n"]))in
	     let _ =
	       state#call CallConv.c stackoverflow_deinstall_handler [] in
	     return vars state Unit `Unit) in
      printf "Writing bitcode\n%!";
      ignore(Llvm_bitwriter.write_bitcode_file m "aout.bc");
      printf "Evaluating\n%!";
      let t = Unix.gettimeofday() in
      let _ =
	let llvm_f, _ = List.assoc f_name vars'.vals in
	ExecutionEngine.run_function llvm_f
	  [|GenericValue.of_int int_type 0|] ee in
      printf "Took %fs\n%!" (Unix.gettimeofday() -. t);

      vars
  | `Extern(_, _, `Struct _) ->
      failwith "Not yet implemented: FFI returning struct"
  | `Extern(f, tys_arg, ty_ret) ->
      if !debug then
	eprintf "def extern %s\n%!" f;
      let fn =
	let ty =
	  function_type (lltype_of ty_ret)
	    (Array.of_list (List.map lltype_of tys_arg)) in
        declare_function f ty m in
      let ty = tys_arg, ty_ret in
      let llvm_f = define_function (uniq("vm_"^f)) (function_type_of ty) m in
      set_function_call_conv cc llvm_f;
      let entry = mk_state llvm_f in
      let start = entry#mk "start" in
      let args = List.init (List.length tys_arg) (param llvm_f) in
      start#ret(start#call CallConv.c fn args);
      let _ = entry#br start in
      Llvm_analysis.assert_valid_function llvm_f;
      add_val (f, (llvm_f, `Function ty)) vars
  | `Type(c, ty) ->
      (* Define a new type constructor. *)
      let name = c ^ Type.to_string () ty in
      if !debug then
	printf "def `Type %s\n%!" name;
      let llty = define_global name (undef RTType.lltype) m in
      Hashtbl.add types c (llty, ty);
      let llvisit = def_visit vars name c ty in
      let llprint = def_print vars name c ty in
      init_type name llty llvisit llprint;
      vars

(** Define a function to traverse a reference. *)
and def_visit vars name c ty =
  let f = "visit_" ^ name in
  let body, vars = visit vars (Var "g") (Var "x") ty in
  let vars =
    def vars
      (`UnsafeFunction(f, ["g", `Function([`Reference], `Unit);
			   "x", `Reference], `Unit,
		       Let("x", Cast(Var "x", c), body))) in
  let llvisit, _ = List.assoc f vars.vals in
  llvisit

and visit vars f v = function
  | `Unit | `Bool | `Int | `Float | `Function _ -> Unit, vars
  | `Struct tys ->
      let f (i, (fs, vars)) ty =
	let f, vars = visit vars f (GetValue(v, i)) ty in
	i+1, (f::fs, vars) in
      let _, (fs, vars) = List.fold_left f (0, ([], vars)) tys in
      compound fs, vars
  | `Array _ -> Apply(f, [Magic(v, `Reference)]), vars
  | `Reference -> Apply(f, [v]), vars

and def_visit_array vars ty =
  let f = "visit_array_"^Type.to_string () ty in
  let body, vars = visit vars (Var "g") (Get(Var "a", Var "i")) ty in
  let llvisitaux =
    let f = f^"aux" in
    mk_fun vars cc f [ "g", `Function([`Reference], `Unit);
		       "a", `Array ty;
		       "i", `Int ] `Unit
      (If(Var "i" =: Length(Var "a"), Unit,
	  compound
	    [body;
	     Apply(Var f, [Var "g"; Var "a"; Var "i" +: Int 1])])) in
  mk_fun vars cc f [ "g", `Function([`Reference], `Unit);
		     "a", `Reference ] `Unit
    (Apply(Llvalue(llvisitaux, `Function([`Function([`Reference], `Unit);
					  `Array ty;
					  `Int], `Unit)),
	   [Var "g"; Magic(Var "a", `Array ty); Int 0]))

(** Define a function to print a type constructor. *)
and def_print vars name c ty =
  let f = "print_" ^ name in
  mk_fun vars cc f ["x", `Reference] `Unit
    (compound
       [Printf(c, []);
	Print(Cast(Var "x", c))])

(** Define a function to print an array. *)
and def_print_array vars ty =
  let f = "print_array_" ^ Type.to_string () ty in
  mk_fun vars cc f ["x", `Reference] `Unit (Print(Magic(Var "x", `Array ty)))

(** Create and memoize a type. Used to create wrapper reference types
    for arrays. *)
and mk_type vars ty =
  let name = "Box("^Type.to_string () ty^")" in
  if !debug then
    printf "mk_type %s\n%!" name;
  try fst(Hashtbl.find types name) with Not_found ->
    let _ = def vars (`Type(name, ty)) in
    let llty, _ = find_type name in
    llty

and mk_array_type ty =
  if !debug then
    printf "mk_array_type %s\n%!" (Type.to_string () ty);
  let name = Type.to_string () (`Array ty) in
  try fst(Hashtbl.find types name) with Not_found ->
    let llty = define_global name (undef RTType.lltype) m in
    Hashtbl.add types name (llty, `Array ty);
    let llvisit = def_visit_array vars ty in
    let llprint = def_print_array vars ty in
    init_type name llty llvisit llprint;
    llty

and init_type name llty llvisit llprint =
  if !debug then
    printf "init_type %s\n%!" name;

  let f = "init_type_"^name in
  let vars =
    defun vars CallConv.c f ["", `Unit] `Unit
      (fun vars state ->
	 let s =
	   Struct
	     [ Llvalue(llvisit, `Function([`Function([`Reference], `Unit);
					   `Reference], `Unit));
	       Llvalue(llprint, `Function([`Reference], `Unit)) ] in
	 let state, _ = expr vars state (Store(llty, s)) in
	 return vars state Unit `Unit) in
  let llvm_f, _ = List.assoc f vars.vals in
  ignore(ExecutionEngine.run_function llvm_f
	   [|GenericValue.of_int int_type 0|] ee)

(** Create and memoize a function. Used to create visitor functions. *)
and mk_fun vars cc f args ty_ret body =
  if !debug then
    printf "mk_fun %s\n%!" f;
  try Hashtbl.find functions f with Not_found ->
    let vars =
      def vars (`UnsafeFunction(f, args, ty_ret, body)) in
    let llty, _ = find f vars.vals in
    Hashtbl.add functions f llty;
    llty

let init() =
  (* Initialize the shadow stack and GC. *)
  let f_name = "init_runtime" in
  let vars' =
    defun vars CallConv.c f_name ["", `Unit] `Unit
      (fun vars state ->
	 let state = state#no_gc in
	 let n = 1 lsl 25 in
	 let body =
	   compound
	     [ Store(stack, Alloc(Int n, `Reference));
	       Store(visit_stack, Alloc(Int n, `Reference));
	       Store(allocated, Alloc(Int n, `Struct[`Reference; `Bool])) ] in
	 return vars state body `Unit) in
  let _ =
    let llvm_f, _ = List.assoc f_name vars'.vals in
    ExecutionEngine.run_function llvm_f
      [|GenericValue.of_int int_type 0|] ee in
  vars

(** Compile and run a list of definitions. *)
let compile_and_run defs =
  let vars = init() in
  let printf(x, y) =
    if !debug then Printf(x, y) else Unit in
  let boot : 'a t list =
    [ (* Clear all of the mark bits in the allocated list. *)
      `UnsafeFunction
	("gc_clear", ["i", `Int], `Unit,
	 Let("a", Load(allocated, `Array(`Struct[`Reference; `Bool])),
	     Let("n", Load(n_allocated, `Int),
		 If(Var "i" =: Var "n", Unit,
		    compound
		      [ Let("x", Get(Var "a", Var "i"),
			    Set(Var "a", Var "i",
				Struct[GetValue(Var "x", 0); Bool false]));
			Apply(Var "gc_clear", [Var "i" +: Int 1]) ]))));

      (* Search the allocated list for the given reference and mark it,
	 returning whether or not it was freshly marked. *)
      `UnsafeFunction
	("gc_mark1", ["p", `Reference;
		      "i", `Int], `Bool,
	 Let("a", Load(allocated, `Array(`Struct[`Reference; `Bool])),
	     Let("n", Load(n_allocated, `Int),
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
			   Apply(Var "gc_mark1", [Var "p";
						  Var "i" +: Int 1])))))));

      (* Push a reference onto the visit stack. *)
      `UnsafeFunction
	("gc_push", ["p", `Reference], `Unit,
	 Let("a", Load(visit_stack, `Array `Reference),
	     Let("n", Load(n_visit, `Int),
		 compound
		   [ Set(Var "a", Var "n", Var "p");
		     Store(n_visit, Var "n" +: Int 1) ])));

      (* Mark this reference in the allocated list and, if it was freshly
	 marked, traverse its children. *)
      `UnsafeFunction
	("gc_mark", ["p", `Reference], `Unit,
	 If(AddressOf(Var "p") =: Int 0, Unit,
	    compound
	      [ If(Apply(Var "gc_mark1", [Var "p"; Int 0]),
		   Apply(Visit(Var "p"), [Var "gc_push"; Var "p"]),
		   Unit);
		Let("n", Load(n_visit, `Int) -: Int 1,
		    If(Var "n" <: Int 0, Unit,
		       Let("a", Load(visit_stack, `Array `Reference),
			   compound
			     [ Store(n_visit, Var "n");
			       Apply(Var "gc_mark",
				     [Get(Var "a", Var "n")]) ]))) ]));
      
      (* Mark all roots on the shadow stack. *)
      `UnsafeFunction
	("gc_markall", ["i", `Int], `Unit,
	 Let("s", Load(stack, `Array `Reference),
	     Let("d", Load(stack_depth, `Int),
		 If(Var "i" =: Var "d", Unit,
		    compound
		      [ Apply(Var "gc_mark", [Get(Var "s", Var "i")]);
			Apply(Var "gc_markall", [Var "i" +: Int 1]) ]))));

      (* Free all unmarked values. When a value is freed the last allocated
	 value is moved over the top of it and the number of allocated values
	 is decremented. *)
      `UnsafeFunction
	("gc_sweep", ["i", `Int], `Unit,
	 Let("a", Load(allocated, `Array(`Struct[`Reference; `Bool])),
	     Let("n", Load(n_allocated, `Int),
		 If(Var "i" =: Var "n", Unit,
		    Let("p", Get(Var "a", Var "i"),
			compound
			  [ If(GetValue(Var "p", 1),
			       Apply(Var "gc_sweep", [Var "i" +: Int 1]),
			       compound
				 [ Free(GetValue(Var "p", 0));
				   Set(Var "a", Var "i",
				       Get(Var "a", Var "n" -: Int 1));
				   Store(n_allocated, Var "n" -: Int 1);
				   Apply(Var "gc_sweep", [Var "i"]) ])])))));

      (* Clear, mark and sweep. *)
      `UnsafeFunction
	("gc", [], `Unit,
	 compound
	   [ printf("GC clearing... %d %d\n", [Load(n_allocated, `Int); Load(stack_depth, `Int)]);
	     Apply(Var "gc_clear", [Int 0]);
	     printf("GC marking...\n", []);
	     Apply(Var "gc_markall", [Int 0]);
	     printf("GC sweeping...\n", []);
	     Apply(Var "gc_sweep", [Int 0]);
	     printf("GC done. %d %d\n", [Load(n_allocated, `Int); Load(stack_depth, `Int)]);
	     Store(quota, Int 2 *: Load(n_allocated, `Int))]) ] in
  let vars = List.fold_left def vars boot in
  let _ = List.fold_left def vars defs in
  ()
