type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(********************************)
(*     Handling environment     *)
(********************************)

let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id,l) -> if(x=id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id,binding) -> if (x=id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []


(***************************)
(*     Handling memory     *)
(***************************)

let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise(Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc,v)::tl -> if(l=loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l,v) mem -> (l,v)::mem

let empty_mem = []

(***************************)
(*     Handling record     *)
(***************************)

let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
    | [] -> raise(Failure ("field "^ id ^" is not included in record"))
    | (x,l)::tl -> if(id=x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x,l) record -> (x,l)::record

let empty_record = []

(***************************)

let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec list_fold2 : ('a -> 'b -> 'c -> 'c)-> 'a list -> 'b list -> 'c -> 'c
= fun func l1 l2 acc ->
  match (l1,l2) with
  | ([],[]) -> acc
  | (hd1::tl1,hd2::tl2) -> list_fold2 func tl1 tl2 (func hd1 hd2 acc)
  | _ -> raise (Failure "two lists have different length")

let rec list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
= fun func l acc ->
  match l with
  | [] -> acc
  | hd::tl -> list_fold func tl (func hd acc)

let value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record _ -> "record" 

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1,mem1) = eval env mem e1 in
  let (v2,mem2) = eval env mem1 e2 in
  match (v1,v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
  match e with
  | WRITE e -> 
    let (v1,mem1) = eval env mem e in
    let _ = print_endline(value2str v1) in
    (v1,mem1)
  | NUM n -> (Num n, mem)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | UNIT -> (Unit, mem)
  | VAR x ->  ((lookup_mem (lookup_loc_env x env) mem), mem)
  | ADD (e1, e2) -> eval_aop env mem e1 e2 (fun x y -> x + y)
  | SUB (e1, e2) -> eval_aop env mem e1 e2 (fun x y -> x - y)
  | MUL (e1, e2) -> eval_aop env mem e1 e2 (fun x y -> x * y)
  | DIV (e1, e2) -> eval_aop env mem e1 e2 (fun x y -> x / y)
  | EQUAL (e1, e2) ->
    let (v1,mem1) = eval env mem e1 in
    let (v2,mem2) = eval env mem e2 in
    (match v1, v2 with 
      | Num n1, Num n2 ->(Bool (if n1=n2 then true else false) , mem2)
      | Bool b1, Bool b2 -> (Bool (if b1=b2 then true else false), mem2)
      | Unit, Unit -> (Bool true, mem2)
      | _ -> raise UndefinedSemantics)
  | LESS (e1, e2) ->
    let (v1,mem1) = eval env mem e1 in
    let (v2,mem2) = eval env mem e2 in
    (match (v1, v2) with 
      | Num n1, Num n2 -> (Bool (if n1 < n2 then true else false), mem2)
      | _ -> raise UndefinedSemantics )
  | NOT e -> 
    let (b,mem1) = eval env mem e in 
    (match b with
      | Bool true -> (Bool false, mem1)
      | Bool false -> (Bool true , mem1)
      | _ -> raise UndefinedSemantics)
  | SEQ (e1, e2) ->
    let (v1,mem1) = eval env mem e1 in
    let (v2,mem2) = eval env mem1 e2 in
    (v2, mem2)
  | IF (e, e1, e2) ->
    let (cond, mem1) = eval env mem e in
    (match cond with
      | Bool true -> (eval env mem1 e1)
      | Bool false -> (eval env mem1 e2)
      | _ -> raise UndefinedSemantics)
  | WHILE (e1, e2) ->
    let (cond ,mem_) = eval env mem e1 in
    let (v1, mem1) = eval env mem_ e2 in
    (match cond with
      | Bool true -> eval env mem1 (WHILE (e1, e2))
      | Bool false -> (Unit, mem_)
      | _ -> raise UndefinedSemantics)
  | LETV (x, e1, e2) ->
    let (v, mem1) = eval env mem e1 in
    let l = new_location () in
    let (v1, mem2) = eval (extend_env (LocBind(x, l)) env) (extend_mem (l , v) mem1) e2 in
      (v1, mem2)
  | LETF (f, x_list, e1, e2) -> 
    let proc = (x_list, e1, env) in 
    let (v, mem1) = eval (extend_env (ProcBind(f, proc)) env) mem e2 in
      (v, mem1)
  | CALLV (f, e_list) -> 
    let (x_list, e_, env_) = lookup_proc_env f env in  (*proc*)
    let (ret_env, ret_mem, mem_now) = list_fold2(
      fun x_curr e_curr (ret_env, ret_mem_ex, mem_ex) ->
        let l = new_location () in 
        let (v_curr, mem_curr) = eval env mem_ex e_curr in 
        let record = extend_env (LocBind(x_curr, l)) ret_env in
        let ret_mem = extend_mem (l, v_curr) ret_mem_ex in
          (record, ret_mem, mem_curr)
      ) (x_list) (e_list) (env_, empty_mem, mem) in 
    
    let fin_env = env_ @ ret_env @ [ProcBind(f, (x_list, e_, env_))] in
    let fin_mem = mem_now @ ret_mem in
    let v1, mem1 = eval fin_env fin_mem e_ in
      (v1, mem1)
    
  | CALLR (f, y_list) -> 
    let (x_list, e, env_) = lookup_proc_env f env in  (*proc*)
    
    let ret_env = list_fold2(
        fun x_curr y_curr env_ex ->
          let y_loc = lookup_loc_env y_curr env in
          let env_new = extend_env (LocBind(x_curr, y_loc)) env_ex in
            env_new
        ) (x_list) (y_list) env_ in
    
    let v, mem_ = eval (ret_env @ [ProcBind (f, (x_list, e, env_))]) mem e in
      (v, mem_)
  
  | RECORD lst ->
  if lst = empty_record then (Unit, mem)
  else 
    let (ret_record, ret_mem, mem_now) = list_fold (
      
      fun (x_curr,e_curr) (record_ex, ret_mem_ex, mem_ex)->
        let l = new_location () in 
        let (v_curr, mem_curr) = eval env mem_ex e_curr in 
        let record_curr = extend_record (x_curr, l) record_ex in
        let ret_mem = extend_mem (l, v_curr) ret_mem_ex in
        (record_curr, ret_mem, mem_curr)
        
      ) lst (empty_record, empty_mem, mem) in
      (Record ret_record, mem_now @ ret_mem)
  | FIELD (e, x) ->
    (match eval env mem e with 
      | (Record r, mem1) ->
          let rx_loc = lookup_record x r in
          ( (lookup_mem rx_loc mem1), mem1)
      | _ -> raise UndefinedSemantics)
  | ASSIGN (x, e) ->
    let (v1, mem1) = eval env mem e in
    let l = lookup_loc_env x env in
    let mem2 = extend_mem (l, v1) mem1 in
    (v1, mem2)
  | ASSIGNF (e1, x, e2) ->
    (match eval env mem e1 with
      | (Record r, mem1) ->
        let (v, mem2) = eval env mem1 e2 in
        let l = lookup_record x r in
        let rx_loc = lookup_record x r in
          (v, (extend_mem (rx_loc , v) mem2))
          | _ -> raise UndefinedSemantics)

let runb : exp -> value 
=fun exp -> let (v, _) = eval empty_env empty_mem exp in v;;

(*ex*)
