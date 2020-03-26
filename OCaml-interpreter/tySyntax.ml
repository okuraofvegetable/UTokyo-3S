type tyvar = int

	      
type ty =
  | TyInt
  | TyBool
  | TyFun of ty * ty
  | TyVar of tyvar
  | TyPair of ty * ty
  | TyList of ty

(*
 * the type of substitution
 *)
type subst = (tyvar * ty) list
(*
 * the type of constraints
 *   a list of equations t1 = t2 for types t1 and t2
 *)
type constraints = (ty * ty) list

exception TyError
exception TyLookupError
exception TyMakeSubstError

type type_schema = tyvar list * ty
type type_env = (string * type_schema) list





let idx = ref 0 
let new_tyvar u = idx := !idx+1;!idx

(* ty -> unit *)
let rec print_type t =
	match t with
	| TyInt -> print_string " int"
	| TyBool -> print_string " bool "
	| TyFun (x,y) -> print_string " (";print_type x;print_string "-> ";print_type y;print_string ")"
	| TyVar alpha -> print_string " a";print_int alpha;print_string" "
	| TyPair (x,y) -> print_string " (";print_type x;print_string ", ";print_type y;print_string ")"
	| TyList x -> print_type x;print_string "list"
	

let rec print_constraints c = 
	match c with
	| [] -> print_string "end constraints\n"
	| (x,y)::cs -> (print_type x);print_string "=";(print_type y);print_string "\n";print_constraints cs

let rec print_subst s = 
	match s with
	| [] -> print_string "end subst\n"
	| (tv,t)::ss -> print_type (TyVar tv);print_string "=";(print_type t);print_string "\n";print_subst ss

let rec print_tyvar_list tvl =
	match tvl with
	| [] -> print_string "\n"
	| tv::tvs -> print_string "a";print_int tv;print_string " ";print_tyvar_list tvs

let rec print_tysc tysc =
	let (tvl,t) = tysc in
		print_string "for all ";
		print_tyvar_list tvl;
		print_type t

(* tyvar -> subst -> ty *)
let rec lookup_var x sigma =
  try List.assoc x sigma with Not_found -> raise TyLookupError

(* subst -> ty -> ty *)
let rec ty_subst sigma t = 
	match t with
	| TyInt -> TyInt
	| TyBool -> TyBool
	| TyFun (x,y) -> let sx = ty_subst sigma x in
					 let sy = ty_subst sigma y in TyFun(sx,sy)
	| TyVar id -> (try (lookup_var id sigma) with TyLookupError -> TyVar id)
	| TyPair (x,y) -> let sx = ty_subst sigma x in
					  let sy = ty_subst sigma y in TyPair(sx,sy)
	| TyList x -> let sx = ty_subst sigma x in TyList sx
	

(* subst -> tyvar list -> ty -> ty *)
(* this is subfunction for ty_subst_schema *)
let rec ty_subst_limited sigma tvl t =
	match t with
	| TyInt -> TyInt
	| TyBool -> TyBool
	| TyFun (x,y) -> let sx = ty_subst_limited sigma tvl x in
					 let sy = ty_subst_limited sigma tvl y in
					 	TyFun (sx,sy)
	| TyVar id -> (if (List.mem id tvl)
						then (TyVar id) (* tyvar id is bound. it should not be replaced. *)
						else ty_subst sigma (TyVar id))
	| TyPair (x,y) -> let sx = ty_subst_limited sigma tvl x in
					  let sy = ty_subst_limited sigma tvl y in
					 	TyPair (sx,sy)
	| TyList x -> let sx = ty_subst_limited sigma tvl x in TyList sx
	
(* subst -> type_schema -> type_schema *)
(* substitute type schema only free tyvar *)
let rec ty_subst_schema sigma tysc =
	let (tvl,t) = tysc in (tvl,ty_subst_limited sigma tvl t)

(* substitute free tyvars in tyenv with sigma  *)
let rec ty_subst_tyenv sigma (tyenv : type_env) = 
	match tyenv with
	| [] -> []
	| (n,tysc)::ys -> (n,(ty_subst_schema sigma tysc))::(ty_subst_tyenv sigma ys)


(* subst -> subst -> tyvar list -> subst *)
let rec make_subst s t u =
	match u with
	| [] -> []
	| y::ys -> let z =  ty_subst t (TyVar y) in
			   let zz = ty_subst s z in
			   	(y,zz)::(make_subst s t ys)
(* subst -> tyvar list *)
let rec domain s =
	match s with
	| [] -> []
 	| (tv,t)::ss -> tv::(domain ss)

(* tyvar_list -> tyvar_list -> tyvar_list *)
let rec domain_union s t =
	match t with
	| [] -> s
	| y::ys -> if List.mem y s then domain_union s ys
							   else domain_union (y::s) ys

(* subst -> subst -> subst *)
let rec compose s t = let u = domain_union (domain s) (domain t) in make_subst s t u


(* subst -> constraints -> constraints *)
let rec ty_subst_constraints sigma con =
	match con with
	| [] -> []
	| (x,y)::ys -> ((ty_subst sigma x),(ty_subst sigma y))::(ty_subst_constraints sigma ys)



let rec include_tyvar t tv =
	match t with
	| TyInt -> false
	| TyBool -> false
	| TyFun (x,y) -> (if ((include_tyvar x tv) || (include_tyvar y tv)) then true else false )
	| TyVar id -> (if (id=tv) then true else false)
	| TyPair (x,y) -> (if ((include_tyvar x tv) || (include_tyvar y tv)) then true else false )
	| TyList x -> if (include_tyvar x tv) then true else false
	

(*
 * return the most general unifier of the constraints
 * raise TyError if unification fails
 *)
 (* constraints -> subst *)



let rec unify c =
	(* print_constraints c; *)
	match c with
	| [] -> []
	| (x,y)::rem -> 
		(match x with
		 | TyVar alpha -> 
		 	(match y with
		 	 | TyVar beta -> 
		 	 	(if (alpha = beta)
		 	 		then (unify rem)
		 	 		else (if (include_tyvar y alpha)
		 	 				then (raise TyError)
							else ((compose (unify (ty_subst_constraints [(alpha,y)] rem)) [(alpha,y)])))) 
		 	 | _ -> (if (include_tyvar y alpha)
				 		then (raise TyError)
				 		else (compose (unify (ty_subst_constraints [(alpha,y)] rem)) [(alpha,y)])))
		 | TyFun (s,t) ->
		 	(match y with
		 	 | TyFun (s2,t2) -> unify ((s,s2)::((t,t2)::rem))
		 	 | TyVar alpha -> 
		 	 	(if include_tyvar x alpha 
		 	 					then (raise TyError)
		 	 					else (compose (unify (ty_subst_constraints [(alpha,x)] rem)) [(alpha,x)]))
		 	 | _ -> (raise TyError))
		 | TyPair (s,t) ->
		 	(match y with
		 	 | TyPair (s2,t2) -> unify ((s,s2)::((t,t2)::rem))
		 	 | TyVar alpha -> 
		 	 	(if include_tyvar x alpha 
		 	 					then (raise TyError)
		 	 					else (compose (unify (ty_subst_constraints [(alpha,x)] rem)) [(alpha,x)]))
		 	 | _ -> (raise TyError))
		 | TyList (s) ->
		 	(match y with
		 	 | TyList (s2) -> unify ((s,s2)::rem)
		 	 | TyVar alpha -> 
		 	 	(if include_tyvar x alpha 
		 	 					then (raise TyError)
		 	 					else (compose (unify (ty_subst_constraints [(alpha,x)] rem)) [(alpha,x)]))
		 	 | _ -> (raise TyError))
		 | TyInt ->
		 	(match y with
		 	 | TyVar alpha -> 
		 	 	(compose (unify (ty_subst_constraints [(alpha,x)] rem)) [(alpha,x)])
		 	 | TyInt -> (unify rem)
		 	 | _ -> (raise TyError))
		 | TyBool ->
		 	(match y with
		 	 | TyVar alpha -> 
		 	 	(compose (unify (ty_subst_constraints [(alpha,x)] rem)) [(alpha,x)])
		 	 | TyBool -> (unify rem)
		 	 | _ -> (raise TyError)))

(* tyvar list -> subst *)
(* this is subfunction for instantiate *)
let rec new_tyvar_subst (tvl : tyvar list) =
	match tvl with
	| [] -> []
	| y::ys -> (y,(TyVar (new_tyvar ()))) :: (new_tyvar_subst ys)

(* type_schema -> ty *)
(* replace bound tyvars with fresh tyvars *)
let instantiate (tysc : type_schema) = 
	let (tvl,t) = tysc in
		ty_subst (new_tyvar_subst tvl) t

let rec merge_tyvar_list s t =
	match t with
	| [] -> s
	| y::ys -> if List.mem y s then merge_tyvar_list s ys
							   else merge_tyvar_list (y::s) ys
let rec get_type_vars t = 
	match t with
	| TyInt -> []
	| TyBool -> []
	| TyFun(x,y) -> merge_tyvar_list (get_type_vars x) (get_type_vars y)
	| TyVar id -> [id]
	| TyPair(x,y) -> merge_tyvar_list (get_type_vars x) (get_type_vars y)
	| TyList x -> (get_type_vars x)

(* eliminate elements of t from s (S/T) *)
let rec set_diff s t = 
	match s with
	| [] -> []
	| y::ys -> (if List.mem y t then (set_diff ys t) else (y::(set_diff ys t)))

(* list of free tyvars in tysc*)
let get_free_tyvars_from_tysc tysc = 
	let (tvl,t) = tysc in set_diff (get_type_vars t) tvl


(* list of free tyvars in tyenv *)
let rec get_free_tyvars_from_tyenv (tyenv : type_env ) =
	match tyenv with
	| [] -> []
	| (n,tysc)::ys -> merge_tyvar_list (get_free_tyvars_from_tysc tysc) (get_free_tyvars_from_tyenv ys)

let generalize tyenv t = 
	let free_tyvars = set_diff (get_type_vars t) (get_free_tyvars_from_tyenv tyenv) in
		(free_tyvars,t) 