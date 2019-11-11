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
  | NEWREF of exp 
  | DEREF of exp
  | SETREF of exp * exp
  | SEQ of exp * exp
  | BEGIN of exp
and var = string

type value = 
    Int of int 
  | Bool of bool 
  | Closure of var * exp * env 
  | RecClosure of var * var * exp * env
  | Loc of loc
and loc = int
and env = (var * value) list
and mem = (loc * value) list

(* conversion of value to string *)
let value2str v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Loc l -> "Loc "^(string_of_int l)
  | Closure (x,e,env) -> "Closure "
  | RecClosure (f,x,e,env) -> "RecClosure "^f

(* environment *)
let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec apply_env e x = 
  match e with
  | [] -> raise (Failure (x ^ " is unbound in Env"))
  | (y,v)::tl -> if x = y then v else apply_env tl x

(* memory *)
let empty_mem = [] 
let extend_mem (l,v) m = (l,v)::m
let rec apply_mem m l = 
  match m with
  | [] -> raise (Failure ("Location " ^ string_of_int l ^ " is unbound in Mem"))
  | (y,v)::tl -> if l = y then v else apply_mem tl l

(* use the function 'new_location' to generate a fresh memory location *)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

(*****************************************************************)
(* TODO: Implement the eval function. Modify this function only. *)
(*****************************************************************)

let rec set_mem : value -> loc -> mem -> mem
= fun v l m -> match m with
	| hd::tl -> (match hd with
			| (var1, e1) -> if l = var1 then [(var1, v)]@tl else [hd]@(set_mem v l tl)) 
	| [] -> raise (Failure ("Location " ^ string_of_int l ^ " is unbound in Mem"))

let rec eval : exp -> env -> mem -> value * mem
=fun exp env mem -> 
	match exp with 
		| CONST n -> (Int n, mem)
  		| VAR x -> (apply_env env x, mem)
 		| ADD (a, b) -> let var1 = eval a env mem in
				(match var1 with
					| (Int n1, m1) -> let var2 = eval b env m1 in 
								(match var2 with
									| (Int n2, m2) -> (Int (n1 + n2), m2)
									| _ -> raise (Failure "Type Error: non-numeric values"))
					| _ -> raise (Failure "Type Error: non-numeric values"))
 		| SUB (a, b) -> let var1 = eval a env mem in
				(match var1 with
					| (Int n1, m1) -> let var2 = eval b env m1 in 
								(match var2 with
									| (Int n2, m2) -> (Int (n1 - n2), m2)
									| _ -> raise (Failure "Type Error: non-numeric values"))
					| _ -> raise (Failure "Type Error: non-numeric values"))
  		| MUL (a, b) -> let var1 = eval a env mem in
				(match var1 with
					| (Int n1, m1) -> let var2 = eval b env m1 in 
								(match var2 with
									| (Int n2, m2) -> (Int (n1 * n2), m2)
									| _ -> raise (Failure "Type Error: non-numeric values"))
					| _ -> raise (Failure "Type Error: non-numeric values"))
  		| DIV (a, b) -> let var1 = eval a env mem in
				(match var1 with
					| (Int n1, m1) -> let var2 = eval b env m1 in 
								(match var2 with
									| (Int n2, m2) -> (Int (n1 / n2), m2)
									| _ -> raise (Failure "Type Error: non-numeric values"))
					| _ -> raise (Failure "Type Error: non-numeric values"))
  		| ISZERO n -> (match (eval n env mem) with 
					| (Int 0, m) -> (Bool true, m) 
					| (_, m) -> (Bool false, m))
  		| READ -> (Int (read_int()), mem)
  		| IF (exp1, exp2, exp3) -> let e1 = eval exp1 env mem in
						(match e1 with
							| (Bool true, m) -> eval exp2 env m
							| (Bool false, m) -> eval exp3 env m
							| _ -> raise (Failure "Type Error: condition must be Bool type"))
  		| LET (n, exp1, exp2) -> let v = eval exp1 env mem in
						(match v with (v1, m1) ->
						 eval exp2 (extend_env (n, v1) env) m1)
  		| LETREC (f, x, exp1, exp2) -> eval exp2 (extend_env (f, RecClosure (f, x, exp1, env)) env) mem
  		| PROC (x, exp1) -> (Closure (x, exp1, env), mem)
  		| CALL (exp1, exp2) -> let r1 = eval exp1 env mem in
						(match r1 with (v1, m1) -> let r2 = eval exp2 env m1 in
							(match r2 with (v2, m2) ->
								(match v1 with 
									| RecClosure (f, x, exp1, env1) -> eval exp1 (extend_env (x, v2) (extend_env (f, RecClosure (f, x, exp1, env1)) env1)) m2
									| Closure (x, exp1, env1) -> eval exp1 (extend_env (x, v2) env1) m2
									| _ -> eval exp1 env m2
								)
        						)
						)
  		| NEWREF exp1 ->  let v1 = eval exp1 env mem in
				  (match v1 with (v, m1) -> let l = new_location () in (Loc l, extend_mem (l, v) m1))
  		| DEREF exp1 -> let r = eval exp1 env mem in
				(match r with 
					| (Loc l, m) -> ((apply_mem m l), m)
					| (_, m) -> raise (Failure "Type Error: Type Error: non-location value"))
  		| SETREF (exp1, exp2) -> let v1 = eval exp1 env mem in
						(match v1 with 
							| (Loc l, m1) -> let v2 = eval exp2 env m1 in (match v2 with (v, m2) -> (v, (set_mem v l m2)))
							| (_, m1) -> raise (Failure "Type Error: Type Error: non-location value"))
  		| SEQ (exp1, exp2) -> let v1 = eval exp1 env mem in
					(match v1 with (v, m1) -> eval exp2 env m1)
  		| BEGIN exp1 -> eval exp1 env mem
		| _ -> raise UndefinedSemantics

(* driver code *)
let run : program -> value
=fun pgm -> (fun (v,_) -> v) (eval pgm empty_env empty_mem) 
