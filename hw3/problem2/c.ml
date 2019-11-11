type aexp = 
  | CONST of int 
  | VAR of var
  | ADD of aexp * aexp 
  | MUL of aexp * aexp 
  | SUB of aexp * aexp
  
and bexp = 
  | TRUE 
  | FALSE 
  | EQ of aexp * aexp 
  | LT of aexp * aexp 
  | NOT of bexp 
  | AND of bexp * bexp

and stmt =
  | ASSIGN of var * aexp 
  | SKIP
  | SEQ of stmt * stmt
  | IF of bexp * stmt * stmt
  | WHILE of bexp * stmt
  | BLOCK of var * aexp * stmt
  | READ of var
  | PRINT of aexp 
and var = string
type program = stmt

type value = Int of int
type loc = Loc of int 
type env = (var * loc) list
type mem = (loc * value) list

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
  | [] -> raise (Failure ("Location " ^ string_of_int ((fun (Loc n) -> n) l) ^ " is unbound in Mem"))
  | (y,v)::tl -> if l = y then v else apply_mem tl l

let counter = ref 0
let new_location () = counter:=!counter+1; Loc (!counter)

exception NotImplemented

let rec get_loc : var -> env -> loc
= fun v e -> match e with
			| hd::tl -> (match hd with (v1, l1) -> if v1 = v then l1 else get_loc v tl)
			| [] -> raise (Failure ("Variable " ^ v ^ "is unbound in Env"))			

let rec update_mem : loc -> value -> mem -> mem
= fun l v m -> match m with
			| hd::tl -> (match hd with (l1, v1) -> if l1 = l then (l1, v)::tl else hd::(update_mem l v tl))
 			| [] -> raise (Failure ("Loc " ^ string_of_int ((fun (Loc n) -> n) l) ^ "is unbound in Mem"))	

let rec eval_aexp : aexp -> env -> mem -> int
=fun a env mem -> match a with 
			| CONST n -> n 
		  	| VAR v -> (fun (Int n) -> n) (apply_mem mem (apply_env env v))
  			| ADD (aexp1, aexp2) -> (eval_aexp aexp1 env mem) + (eval_aexp aexp2 env mem)
  			| MUL (aexp1, aexp2) -> (eval_aexp aexp1 env mem) * (eval_aexp aexp2 env mem)
  			| SUB (aexp1, aexp2) -> (eval_aexp aexp1 env mem) - (eval_aexp aexp2 env mem)

and eval_bexp : bexp -> env -> mem -> bool
=fun b env mem -> match b with
			| TRUE -> true
  			| FALSE -> false
  			| EQ (aexp1, aexp2) -> if (eval_aexp aexp1 env mem) = (eval_aexp aexp2 env mem) then true else false
  			| LT (aexp1, aexp2) -> if (eval_aexp aexp1 env mem) <= (eval_aexp aexp2 env mem) then true else false
  			| NOT bexp1 -> if (eval_bexp bexp1 env mem) = true then false else true
  			| AND (bexp1 ,bexp2) -> let b1 = eval_bexp bexp1 env mem in let b2 = eval_bexp bexp2 env mem
						in if (b1 = true) && (b2 = true) then true else false

let rec eval : stmt -> env -> mem -> mem
=fun s env mem -> 
  match s with
  | READ x -> extend_mem (apply_env env x, Int (read_int())) mem (* Do not modify *)
  | PRINT e -> print_int (eval_aexp e env mem); print_newline(); mem (* Do not modify *)
  | ASSIGN (var1, aexp1) -> let v = eval_aexp aexp1 env mem in let location = get_loc var1 env in update_mem location (Int v) mem
  | SKIP -> mem
  | SEQ (stmt1, stmt2) -> let m = eval stmt1 env mem in eval stmt2 env m
  | IF (bexp1, stmt1, stmt2) -> let b = eval_bexp bexp1 env mem in (match b with
									| true -> eval stmt1 env mem
									| false -> eval stmt2 env mem)
  | WHILE (bexp1, stmt1) -> let b = eval_bexp bexp1 env mem in (match b with
									| true -> eval (WHILE (bexp1, stmt1)) env (eval stmt1 env mem)
									| false -> mem)
  | BLOCK (var1, aexp1, stmt1) -> let a = eval_aexp aexp1 env mem in let l = new_location () in let env1 = extend_env (var1, l) env in let mem1 = extend_mem (l, Int a) mem in eval stmt1 env1 mem1


let execute : program -> unit 
=fun pgm -> ignore (eval pgm empty_env empty_mem)
