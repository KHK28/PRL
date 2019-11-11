type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty -> match e with
			| CONST n -> [(ty, TyInt)]
  			| VAR x -> [(ty, (TEnv.find tenv x))]
  			| ADD (exp1, exp2) -> [(ty, TyInt)]@(gen_equations tenv exp1 TyInt)@(gen_equations tenv exp2 TyInt)
  			| SUB (exp1, exp2) -> [(ty, TyInt)]@(gen_equations tenv exp1 TyInt)@(gen_equations tenv exp2 TyInt)
  			| MUL (exp1, exp2) -> [(ty, TyInt)]@(gen_equations tenv exp1 TyInt)@(gen_equations tenv exp2 TyInt)
  			| DIV (exp1, exp2) -> [(ty, TyInt)]@(gen_equations tenv exp1 TyInt)@(gen_equations tenv exp2 TyInt)
  			| ISZERO exp1 -> [(ty, TyBool)]@(gen_equations tenv exp1 TyInt)
  			| READ -> [(ty, TyInt)]
  			| IF (exp1, exp2, exp3) -> (gen_equations tenv exp1 TyBool)@(gen_equations tenv exp2 ty)@(gen_equations tenv exp3 ty)
  			| LET (x, exp1, exp2) -> let x_tyvar = fresh_tyvar () in (gen_equations tenv exp1 x_tyvar)@(gen_equations (TEnv.extend (x, x_tyvar) tenv) exp2 ty)
  			| LETREC (f, x, exp1, exp2) -> let f_tyvar = fresh_tyvar () in let x_tyvar = fresh_tyvar () in let e1_tyvar = fresh_tyvar () in (gen_equations (TEnv.extend (f, f_tyvar) (TEnv.extend (x, x_tyvar) tenv)) exp1 e1_tyvar)@(gen_equations (TEnv.extend (f, f_tyvar) tenv) exp2 ty)
  			| PROC (x, exp1) -> let x_tyvar = fresh_tyvar () in let body_tyvar = fresh_tyvar () in [(ty, TyFun(x_tyvar, body_tyvar))]@(gen_equations (TEnv.extend (x, x_tyvar) tenv) exp1 body_tyvar)
  			| CALL (exp1, exp2) -> let new_tyvar = fresh_tyvar () in (gen_equations tenv exp1 (TyFun (new_tyvar, ty)))@(gen_equations tenv exp2 new_tyvar)
			| _ -> raise TypeError

let rec compare_eqns_subs_var v subs
= match subs with
	| hd::tl -> (match hd with 
				| (s, TyInt) -> if s = v then (TyInt) else compare_eqns_subs_var v tl
				| (s, TyBool) -> if s = v then (TyBool) else compare_eqns_subs_var v tl
				| (s, TyFun(e1, e2)) -> if s = v then (TyFun(e1, e2)) else compare_eqns_subs_var v tl
				| (s, TyVar e) -> if s = v then (compare_eqns_subs_var e tl) else compare_eqns_subs_var v tl
				| _ -> compare_eqns_subs_var v tl
				)
	| [] -> (TyVar v)

let rec apply_subst_to_eqns eqns subs
= match eqns with
	| hd::tl -> (match hd with
			| (TyVar v1, TyVar v2) -> [((compare_eqns_subs_var v1 subs), (compare_eqns_subs_var v2 subs))]@(apply_subst_to_eqns tl subs)
			| (TyVar v, TyInt) -> [((compare_eqns_subs_var v subs), TyInt)]@(apply_subst_to_eqns tl subs)
			| (TyVar v, TyBool) -> [((compare_eqns_subs_var v subs), TyBool)]@(apply_subst_to_eqns tl subs)
			| (TyVar v, TyFun(e1, e2)) -> [((compare_eqns_subs_var v subs), TyFun(e1, e2))]@(apply_subst_to_eqns tl subs)
			| (TyInt, TyVar v) -> [(TyInt, (compare_eqns_subs_var v subs))]@(apply_subst_to_eqns tl subs)
			| (TyBool, TyVar v) -> [(TyBool, (compare_eqns_subs_var v subs))]@(apply_subst_to_eqns tl subs)
			| (TyFun(e1, e2), TyVar v) -> [(TyFun(e1, e2), (compare_eqns_subs_var v subs))]@(apply_subst_to_eqns tl subs)
			| _ -> [hd]@(apply_subst_to_eqns tl subs)
			)
	| [] -> []



let rec subst_applied eqns subs
= match eqns with
	| hd::tl -> (match hd with 
				| (TyInt, TyInt) -> subst_applied tl subs
				| (TyBool, TyBool) -> subst_applied tl subs
				| (TyFun(t1, t2), TyFun(t3, t4)) -> subst_applied ([(t1, t3);(t2, t4)]@tl) subs
				| (TyVar v, TyFun (f1, f2)) -> let subs2 = Subst.extend v (TyFun(f1, f2)) subs in subst_applied (apply_subst_to_eqns tl subs2) subs2
				| (TyVar v, TyInt) -> let subs2 = Subst.extend v (TyInt) subs in subst_applied (apply_subst_to_eqns tl subs2) subs2
				| (TyVar v, TyBool) -> let subs2 = Subst.extend v (TyBool) subs in subst_applied (apply_subst_to_eqns tl subs2) subs2
				| (TyVar v1, TyVar v2) -> let subs2 = Subst.extend v1 (TyVar v2) subs in subst_applied (apply_subst_to_eqns tl subs2) subs2
				| (TyFun (f1, f2), TyVar v) -> subst_applied ([(TyVar v, (TyFun(f1, f2)))]@tl) subs
				| (TyInt, TyVar v) -> subst_applied ([(TyVar v, TyInt)]@tl) subs
				| (TyBool, TyVar v) -> subst_applied ([(TyVar v, TyBool)]@tl) subs
				| _ -> raise TypeError
			)
	| [] -> subs

let solve : typ_eqn -> Subst.t
=fun eqns -> subst_applied eqns []

(* typeof: Do not modify this function *)
let typeof : exp -> typ 
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
     print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1)
