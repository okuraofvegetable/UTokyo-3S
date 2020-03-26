type name = string 
type var = int

type term =
  | EConst of name
  | EFnSymb  of name * (term list)
  | EVar of name
  | ECons of term * term
  | ENil

type fact = EPdSymb of name * (term list)

type rule = fact * (fact list)

type command =
  | CRule    of rule
  | CQuery   of fact list
  | CCont
  | CExit

type subst = (name * term) list

type constraints = (term * term) list

type state = (fact list) * subst
				  
let print_name = print_string

let idx = ref 0
let new_var_id u = idx := !idx+1;!idx
let new_var_name u = let id = new_var_id () in ("_"^(string_of_int id))
let extend x env = x::env
let lookup x sigma = List.assoc x sigma

(* list -> list -> list *)
let rec merge_list s t =
  match t with
  | [] -> s
  | y::ys -> if List.mem y s then merge_list s ys
                 else merge_list (y::s) ys
(* list list -> list *)
let rec concat_merge ll =
  match ll with
  | [] -> []
  | l::res -> merge_list l (concat_merge res)

(* term -> name list *)
let rec get_vars_term t =
  match t with
  | EFnSymb (_,tl) -> concat_merge (List.map (fun s -> get_vars_term s) tl) 
  | EVar id -> [id]
  | ECons (x,y) -> merge_list (get_vars_term x) (get_vars_term y)
  | ENil -> []
  | EConst c -> []

let rec get_vars_fact fac =
  match fac with
  | EPdSymb(_,tl) -> concat_merge (List.map (fun s -> get_vars_term s) tl)

let rec get_vars_fact_list fl = 
  concat_merge (List.map (fun s -> get_vars_fact s) fl)

let rec get_vars_rule r =
  let (f,fl) = r in
  let a = concat_merge (List.map (fun s -> get_vars_fact s) fl) in
  let b = get_vars_fact f in
  merge_list a b

let rec add_env vl  = 
  match vl with
  | [] -> []
  | v::rest -> let id = new_var_name () in
               (id,v)::(add_env rest)

let rec convert_term t sigma =
  match t with
  | EFnSymb (id,tl) -> EFnSymb (id, convert_term_list tl sigma)
  | EVar n -> EVar (List.assoc n sigma)
  | ECons (x,y) -> ECons ((convert_term x sigma),(convert_term y sigma))
  | ENil -> ENil
  | EConst x -> EConst x

and convert_term_list tl sigma = 
  match tl with
  | [] -> []
  | t::rest -> (convert_term t sigma)::(convert_term_list rest sigma)

(* fact -> env -> (fact*env) *)
let convert_fact fac sigma = 
  match fac with
  | EPdSymb (f,tl) ->
    let ntl = convert_term_list tl sigma in EPdSymb (f,ntl)

let convert_fact_list fl sigma =
  (List.map (fun s -> convert_fact s sigma) fl)

let convert_rule r sigma = 
  let (f,fl) = r in ((convert_fact f sigma),(List.map (fun s -> convert_fact s sigma) fl))

let instantiate_rule r =
  let sigma = List.map (fun (x,y) -> (y,x)) (add_env (get_vars_rule r)) in
  convert_rule r sigma


(* print functions for debug *)

let rec print_term t = 
  match t with
  | EFnSymb (id,tl) -> print_name id;
                       if tl=[] then ()
                                else (print_string "(";print_term_list tl;print_string ")")
  | EVar id -> print_name id
  | ECons (x,y) -> print_list t
  | ENil -> print_string "[]"
  | EConst x -> print_name x 
and print_term_list tl = 
  match tl with
  | [] -> ()
  | t::rest -> print_term t;
               (if (rest <> []) then (print_string ",") 
                                else ());
               print_term_list rest
and print_list t =
  print_string "[";
  print_list_inner t;
  print_string "]"
and print_list_inner t =
  match t with
  | ECons (x,(ECons(y,z))) -> print_term x;print_string ", ";print_list_inner (ECons (y,z))
  | ECons (x,ENil) -> print_term x
  | ECons (x,y) -> print_term x;print_string " | ";print_term y
  | _ -> () (* Error *)

let rec print_fact fac =
  match fac with
  | EPdSymb (n,tl) -> print_name n;
                      print_string "(";
                      print_term_list tl;
                      print_string ")"

let rec print_fact_list fl =
  match fl with
  | [] -> ()
  | (f::rest) -> print_fact f;
                 (if rest <> [] then print_string "," else ());
                 print_fact_list rest

let rec print_rule r = 
  let (f,fl) = r in
  print_fact f;
  print_string ":- (";
  print_fact_list fl;
  print_string ")"

let rec print_rules rs = 
  match rs with
  | [] -> ()
  | (r::rest) -> print_rule r;
                 print_string "\n";
                 print_rules rest

let rec print_subst sigma =
  match sigma with
  | [] -> ()
  | (id,t)::rest -> print_name id;
                    print_string " -> ";
                    print_term t;
                    (if rest <> [] then print_string " , " 
                                else ());
                    print_subst rest
let print_constraint con =
  let (s,t) = con in
  print_term s;
  print_string " = ";
  print_term t

let rec print_constraints cons =
  match cons with
  | [] -> print_string "constraint end\n"
  | con::rest -> print_constraint con;
                  print_string "\n";
                  print_constraints rest

let print_state st =
  let (fl,sigma) = st in
  print_string "state:\n  Goals [";
  print_fact_list fl;
  print_string "]\n  sigma:\n";
  print_subst sigma;
  print_string "\n"

