open Syntax 

exception UnifyError 
exception NextStateError 


(* type subst = (name,term) list *)

(* subst -> term -> term *)
let rec term_subst sigma t = 
	match t with
	| EFnSymb (f,fl) -> let new_fl = List.map (fun s -> term_subst sigma s) fl in EFnSymb(f,new_fl)
	| EVar id -> (try (lookup id sigma) with Not_found -> EVar id)
	| ECons (x,y) -> ECons ((term_subst sigma x),(term_subst sigma y))
	| ENil -> ENil
	| EConst c -> EConst c

let rec fact_subst sigma t = 
	match t with 
	| EPdSymb (id,tl) -> let ntl = List.map (fun s -> term_subst sigma s) tl in
						 EPdSymb (id,ntl)

let rec constraints_subst sigma cons =
	match cons with
	| [] -> []
	| (x,y)::rest -> ((term_subst sigma x),(term_subst sigma y))::(constraints_subst sigma rest)

(* subst -> subst -> name list -> subst *)
let rec make_subst s t u =
	match u with
	| [] -> []
	| y::ys -> let z =  term_subst t (EVar y) in
			   let zz = term_subst s z in
			   	(y,zz)::(make_subst s t ys)
(* subst -> name list *)
let rec domain s =
	match s with
	| [] -> []
 	| (tv,t)::ss -> tv::(domain ss)

(* name_list -> name_list -> name_list *)
let rec domain_union s t =
	match t with
	| [] -> s
	| y::ys -> if List.mem y s then domain_union s ys
							   else domain_union (y::s) ys

(* subst -> subst -> subst *)
let rec compose s t = let u = domain_union (domain s) (domain t) in make_subst s t u

(* term -> term ->  constraints *)
let rec collect_constraints s t =
	match s with 
	| EVar x -> [(s,t)]
	| EFnSymb (f,fl) -> (match t with
						 | EVar x -> [(s,t)]
						 | EFnSymb(g,gl) -> if ((f = g) && (List.length fl) = (List.length gl))
						 						then List.concat (List.map (fun (a,b) -> collect_constraints a b) (List.combine fl gl))
						 					else (raise UnifyError)
						 | _ -> (raise UnifyError))
	| ECons (x1,y1) -> (match t with
				  		| ECons (x2,y2) -> (collect_constraints x1 x2)@(collect_constraints y1 y2)
				  		| EVar x -> [(s,t)]
				  		| _ -> (raise UnifyError))
	| ENil -> (match t with
			   | EVar x -> [(s,t)]
			   | ENil -> []
			   | _ -> (raise UnifyError))
	| EConst c -> (match t with
			       | EVar x -> [(s,t)]
			       | EConst d -> (if c = d then []
			       				 else (raise UnifyError))
			       | _ -> (raise UnifyError))

(* fact -> fact -> constraints *)
let collect_constraints_fact s t = 
	match (s,t) with
	| (EPdSymb (p,pl),EPdSymb (q,ql)) -> if (p=q && List.length(pl)=List.length(ql)) 
											 then List.concat (List.map (fun (a,b) -> collect_constraints a b) (List.combine pl ql))
											 else (raise UnifyError)
exception IncludeVarError
(* name -> term -> bool *)
let rec include_var x t =
	match t with
	| EFnSymb (f,tl) -> let _ = List.map (fun s -> include_var x s) tl in false
	| EVar y -> if x=y then (raise IncludeVarError)
				else false
	| ECons (a,b) -> let _ = include_var x a in
					 let _ = include_var x b in false
	| ENil -> false
	| EConst c -> false 
(* constraints -> subst *)
let rec unify cl =
	match cl with
	| [] -> []
	| (s,t)::rest ->
		(match s with
		 | EVar x -> (match t with
		 			  | EVar y -> if x=y then (unify rest)
		 						  else compose (unify (constraints_subst [x,EVar y] rest)) [x,EVar y]
		 			  | _ -> (try (let _ = include_var x t in compose (unify (constraints_subst [x,t] rest)) [x,t]) with
		 			  		  | IncludeVarError -> (raise UnifyError) ))
		 | EFnSymb (f,fl) -> (match t with
		 					  | EVar y -> (try (let _ = include_var y s in compose (unify (constraints_subst [y,s] rest)) [y,s]) with
		 			  		               | IncludeVarError -> (raise UnifyError))
		 					  | EFnSymb (_,_) -> unify ((collect_constraints s t)@rest)
		 			  		  | _ -> (raise UnifyError))
		 | ECons (a,b) -> (match t with
	 					   | EVar y -> (try (let _ = include_var y s in compose (unify (constraints_subst [y,s] rest)) [y,s]) with
	 			  		                | IncludeVarError -> (raise UnifyError))
	 					   | ECons (_,_) -> unify ((collect_constraints s t)@rest)
	 			  		   | _ -> (raise UnifyError))
		 | ENil -> (match t with
	 				| EVar y -> (try (let _ = include_var y s in compose (unify (constraints_subst [y,s] rest)) [y,s]) with
	 			  		         | IncludeVarError -> (raise UnifyError))
	 				| ENil -> unify ((collect_constraints s t)@rest)
	 			  	| _ -> (raise UnifyError))
		 | EConst c -> (match t with
	 				    | EVar y -> (try (let _ = include_var y s in compose (unify (constraints_subst [y,s] rest)) [y,s]) with
	 			  		             | IncludeVarError -> (raise UnifyError))
	 				    | EConst _ -> unify ((collect_constraints s t)@rest)
	 			  	    | _ -> (raise UnifyError)))

(* state -> state list *)
let rec rotate_goal acc state n = 
	let (gl,sigma) = state in
	(
		if (List.length gl = 0) then
			[state]
		else if ((List.length gl) = n) then
			(acc)
		else
			(match gl with
			 | [] -> []
			 | p::rest -> (rotate_goal (state::acc) ((rest@[p]),sigma) (n+1) )))

(*  make next state
	rule -> ((fact list) * subst) -> ((fact list) * subst)
	Goal list of q must not be empty.
*)
let rec next rule state =
	match state with
	| (gl,sigma) -> (match gl with
					 | [] -> (raise NextStateError)
					 | (p::rest) -> try(
					 					let (q,ql) = instantiate_rule rule in
					 					let cons = collect_constraints_fact p q in
					 					(* print_fact q;
					 					print_constraints cons; *)
						 				let mgu = unify cons in
						 				let new_sigma = compose mgu sigma in
						 				let nql = List.map (fun g -> fact_subst mgu g) ql in
						 				let nrest = List.map (fun g -> fact_subst mgu g) rest in
						 				(*print_string "mgu\n";
						 				print_subst sigma;
						 				print_string "\n";*)
						 				[((nql@nrest),new_sigma)]
						 			)with UnifyError -> [])

(*  rules [rule list] : Rules
	queue [((fact list) * subst) list] : State queue *)	
let rec search rules queue =
	(*print_rules rules;*)
	match queue with 
	| [] -> (false,[],rules,[],false)
	| state::rest -> (* print_state state;print_string "\n"; *)
		(match state with
		 | ([],sigma) -> (true,sigma,rules,rest,true)
		 | _ -> let nexts = List.concat (List.map (fun x -> (next x state)) rules) in
		 		let nexts_rotate = List.concat (List.map (fun s -> (rotate_goal [] s 0)) nexts) in
		 		(search rules (rest@nexts_rotate)))

exception UndefinedProcedure
let rec exist_predict f rules =
	match rules with
	| [] -> (raise UndefinedProcedure)
	| (r,_)::rest -> (match (f,r) with
				  | (EPdSymb (x,_),EPdSymb (y,_)) -> if (x=y) then true
				  									 else (exist_predict f rest))
let check_query q rules = 
	let _ = List.map (fun s -> exist_predict s rules) q in ()  

(* let rules = [(EPdSymb ("male",[EFnSymb ("koji",[])]));(EPdSymb ("parent",[EFnSymb ("kobo",[]);EFnSymb ("koji",[])]))] *)

let rec eval_command cmd rules queue table = 
	match cmd with
	| CRule r -> (true,[],r::rules,[],[],false,true)
	| CQuery q -> let _ = check_query q rules in
				  let newtable = add_env (get_vars_fact_list q) in
				  let sigma = List.map (fun (x,y) -> (y,x)) newtable in
				  let gl = convert_fact_list q sigma in
				  let intial_queue = rotate_goal [] (gl,[]) 0 in
				  let (result,sigma,newrules,nque,in_progress) = search rules intial_queue in
					(result,sigma,newrules,nque,newtable,in_progress,false)
	| CCont -> let (result,sigma,newrules,nque,in_progress) = search rules queue in
					(result,sigma,newrules,nque,table,in_progress,false)
	| CExit -> (true,[],rules,[],[],false,true)