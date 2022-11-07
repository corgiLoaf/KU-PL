type program = exp
and exp = 
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp      
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp
and var = string

type value = 
  | Unit 
  | Int of int 
  | Bool of bool 
  | List of value list
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
  | MRecProcedure of var * var * exp *
                     var * var * exp * env
and env = (var * value) list

let rec fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun f accu lst ->
  match lst with
  | [] -> accu
  | hd::tl -> fold_left f (f accu hd) tl

let rec map : ('a -> 'b) -> 'a list -> 'b list
= fun f lst ->
  match lst with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)

let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ fold_left (fun s x -> s ^ ", " ^ x) "" (map string_of_value lst) ^ "]"
  | _ -> "(functional value)"

exception UndefinedSemantics

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env")) 
  | (y,v)::tl -> if x = y then v else lookup_env x tl
  
(*    
let converter : value -> exp
= fun v ->
  match v with
    | Int n -> CONST n
    | Bool true -> TRUE
    | Bool false -> FALSE*)

let rec eval : exp -> env -> value
=fun exp env ->
  match exp with
  | PRINT e -> (print_endline (string_of_value (eval e env)); Unit)
  | UNIT -> Unit
  | CONST n -> Int n
  | TRUE -> Bool true
  | FALSE -> Bool false
  | VAR x -> lookup_env x env
  | ADD (e1, e2) -> binop (fun x y -> x + y) env e1 e2
  | SUB (e1, e2) -> binop (fun x y -> x - y) env e1 e2 
  | MUL (e1, e2) -> binop (fun x y -> x * y) env e1 e2 
  | DIV (e1, e2) -> 
    let v1 = (eval e1 env) in let v2 = (eval e2 env) in
      if (v2 = Int 0) then raise UndefinedSemantics else binop (fun x y -> x / y) env e1 e2 
  | EQUAL (e1, e2) -> 
    let v1 = eval e1 env in let v2 = eval e2 env in 
      (match v1, v2 with
      | Int n1, Int n2 -> Bool (if n1=n2 then true else false)
      | Bool b1, Bool b2 -> Bool (if b1=b2 then true else false)
      | _ -> raise UndefinedSemantics)
  | LESS (e1, e2) ->
    let v1 = eval e1 env in let v2 = eval e2 env in 
      (match v1, v2 with
      | Int n1, Int n2 -> Bool (if n1<n2 then true else false)
      | _ -> raise UndefinedSemantics)
  | NOT e ->
      (match eval e env with
      | Bool true -> Bool false
      | Bool false -> Bool true
      | _ -> raise UndefinedSemantics)
  | NIL -> List []
  | CONS (e1, e2) -> 
    (match (eval e1 env), (eval e2 env) with
      | v, List s -> List (v::s)
      | _ -> raise UndefinedSemantics)
  | APPEND (e1, e2) -> 
    (match (eval e1 env), (eval e2 env) with
      | List s1, List s2 -> List (s1@s2)
      | _ -> raise UndefinedSemantics)
  | HEAD e ->
     (match (eval e env) with
       | List [] -> raise UndefinedSemantics
       | List (hd::tl) -> hd
       | _ -> raise UndefinedSemantics)
  | TAIL e ->
     (match (eval e env) with
       | List [] -> raise UndefinedSemantics
       | List (hd::tl) -> List tl
       | _ -> raise UndefinedSemantics)
  | ISNIL e ->
     (match (eval e env) with
       | List [] -> Bool true
       | List (hd::tl) -> Bool false
       | _ -> raise UndefinedSemantics)
  | IF (e1, e2, e3) ->
    (match eval e1 env with
      | Bool true -> eval e2 env
      | Bool false -> eval e3 env
      | _ -> raise UndefinedSemantics)
  | LET (x, e1, e2) ->
    let v1 = eval e1 env in 
      eval e2 (extend_env (x,v1) env)
  | LETREC (f, x, e1, e2) ->
    let rec_v = RecProcedure(f, x, e1, env) in
      eval e2 (extend_env (f,rec_v) env)
  | LETMREC ((f, x, e1),  (g, y, e2), e3) ->
    let f_val = MRecProcedure (f, x, e1, g, y, e2, env) in
    let g_val = MRecProcedure (g, y, e2, f, x, e1, env) in
      eval e3 (extend_env (g, g_val) (extend_env (f, f_val) env))
  | PROC (x, e) -> Procedure (x, e, env)
  | CALL (e1, e2) ->
    let f_res = (eval e1 env) in let v = (eval e2 env) in
      (match f_res with
        | Procedure (x, e, env_) -> eval e (extend_env (x,v) env_)
        | RecProcedure (f, x, e, env_) -> 
          eval e (extend_env (f, RecProcedure (f, x, e, env_)) (extend_env (x,v) env_))
        | MRecProcedure (f, x, e_f, g, y, e_g, env_) -> 
          eval e_f (extend_env (x, v) 
                      (extend_env (f, MRecProcedure(f, x, e_f, g, y, e_g, env_)) 
                        (extend_env (g, MRecProcedure(g, y, e_g, f, x, e_f, env_)) env_)))
        | _ -> raise UndefinedSemantics)
  | SEQ (e1, e2) ->
    let v1 = (eval e1 env) in let v2 = (eval e2 env) in v2
  | _ -> raise (Failure "Not implemented") (* TODO *)
  
  and binop op env e1 e2 = 
    let v1 = (eval e1 env) in 
    let v2 = (eval e2 env) in (*v1, v2 are value type*)
      begin 
        match v1, v2 with
        | Int n1, Int n2 -> Int (op n1 n2)
        | Bool _, _ 
        | _, Bool _ -> raise UndefinedSemantics
      end
  ;;

let runml : program -> value
=fun pgm -> eval pgm empty_env
;;


(*ex*)
let p2 = LETREC ("double", "x",
        IF (EQUAL (VAR "x", CONST 0), CONST 0,
          ADD (CALL (VAR "double", SUB (VAR "x", CONST 1)), CONST 2
          )
        ),  
        CALL (VAR "double", CONST 6)
      )
      in runml p2;;
      

runml (LETREC ("reverse", "l",
      IF (ISNIL (VAR "l"), NIL,
       APPEND (CALL (VAR "reverse", TAIL (VAR "l")), CONS (HEAD (VAR "l"), NIL))),
      CALL (VAR "reverse", CONS (CONST 1, CONS (CONST 2, CONS (CONST 3, NIL))))));;
    