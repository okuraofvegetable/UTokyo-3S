open Syntax
open TySyntax

exception Unbound
exception ListLengthUnmatch

let extend x v env = (x, v) :: env
let rec extends xvl env =
  match xvl with
  | [] -> env
  | (x,v)::rem -> extends rem (extend x v env)

let rec lookup x env =
  try List.assoc x env with Not_found -> raise Unbound
exception InferTypeError
exception EvalErr
exception DivisionByZero
exception NotSupported

(* *)
let rec tcgamma pt tyenv = 
  match pt with
  | PInt x -> (TyInt,[],[])
  | PBool x -> (TyBool,[],[])
  | PVar id -> let alpha = TyVar(new_tyvar ()) in (alpha,[],[(id,([],alpha))])
  | PPair (p1,p2) -> (let (t1,c1,g1) = tcgamma p1 tyenv in
                      let (t2,c2,g2) = tcgamma p2 tyenv in
                         (TyPair(t1,t2),c1@c2,g1@g2))
  | PNil -> (let alpha = TyVar(new_tyvar ()) in (TyList alpha,[],[]))
  | PCons (p1,p2) -> let (t1,c1,g1) = tcgamma p1 tyenv in
                     let (t2,c2,g2) = tcgamma p2 tyenv in
                        (TyList t1,[(TyList t1,t2)]@c1@c2,g1@g2)  
let rec map_tcgamma_pel pel tyenv = 
  match pel with
  | [] -> []
  | (p,e)::rem -> (tcgamma p tyenv)::(map_tcgamma_pel rem tyenv)

let rec select1from3 tcgl =
  match tcgl with
  | [] -> []
  | (t,c,g)::rem -> t::(select1from3 rem)

let rec select2from3 tcgl =
  match tcgl with
  | [] -> []
  | (t,c,g)::rem -> c::(select2from3 rem)

let rec select3from3 tcgl =
  match tcgl with
  | [] -> []
  | (t,c,g)::rem -> g::(select3from3 rem)

let rec select1from2 tcl =
  match tcl with
  | [] -> []
  | (t,c)::rem -> t::(select1from2 rem)

let rec select2from2 tcl =
  match tcl with
  | [] -> []
  | (t,c)::rem -> c::(select2from2 rem)

(* t [t1,t2,...] => [(t,t1);(t,t2);...] *)
let rec make_cons t tl =
  match tl with
  | [] -> []
  | (t2::rem) -> (t,t2)::(make_cons t rem)

let rec make_cons_inst tysc tl =
  match tl with
  | [] -> []
  | (t2::rem) -> ((instantiate tysc),t2)::(make_cons_inst tysc rem)


let rec add_g_infer pel gl tyenv =
  match (pel,gl) with
  | ([],[]) -> []
  | (((p,e)::rem),(g::grem)) -> (infer_expr (extends g tyenv) e)::(add_g_infer rem grem tyenv)
  | _ -> (raise ListLengthUnmatch)

and infer_expr tyenv e =
  (*print_expr e;print_string "\n";*)
  match e with
  | EConstInt i -> (TyInt,[])
  | EConstBool b -> (TyBool,[])
  | EVar x ->
    (try
       (instantiate (lookup x tyenv),[])
     with
     | Unbound -> (raise InferTypeError))
  | EAdd (e1,e2) -> 
    let (t1,c1) = infer_expr tyenv e1 in
    let (t2,c2) = infer_expr tyenv e2 in
    (TyInt,[(t1,TyInt);(t2,TyInt)]@c1@c2)
  | ESub (e1,e2) -> 
    let (t1,c1) = infer_expr tyenv e1 in
    let (t2,c2) = infer_expr tyenv e2 in
    (TyInt,[(t1,TyInt);(t2,TyInt)]@c1@c2)
  | EMul (e1,e2) -> 
    let (t1,c1) = infer_expr tyenv e1 in
    let (t2,c2) = infer_expr tyenv e2 in
    (TyInt,[(t1,TyInt);(t2,TyInt)]@c1@c2)
  | EDiv (e1,e2) -> 
    let (t1,c1) = infer_expr tyenv e1 in
    let (t2,c2) = infer_expr tyenv e2 in
    (TyInt,[(t1,TyInt);(t2,TyInt)]@c1@c2)
  | EEq (e1,e2) ->
    let (t1,c1) = infer_expr tyenv e1 in
    let (t2,c2) = infer_expr tyenv e2 in
    (TyBool,[(t1,t2)]@c1@c2)
  | ELt (e1,e2) ->
    let (t1,c1) = infer_expr tyenv e1 in
    let (t2,c2) = infer_expr tyenv e2 in
    (TyBool,[(t1,t2)]@c1@c2)
  | EIf (e1,e2,e3) ->
    let (t1,c1) = infer_expr tyenv e1 in
    let (t2,c2) = infer_expr tyenv e2 in
    let (t3,c3) = infer_expr tyenv e3 in
    (t2,[(t1,TyBool);(t2,t3)]@c1@c2@c3)
  | ELet (n,e1,e2) -> 
    let (t1,c1) = infer_expr tyenv e1 in
    let sigma = unify c1 in
    let s1 = ty_subst sigma t1 in
    let delta = ty_subst_tyenv sigma tyenv in
    let (t2,c2) = infer_expr (extend n (generalize delta s1) delta) e2 in
    (t2,c1@c2)
  | EFun (x,exp) -> 
    let alpha = TyVar(new_tyvar ()) in
    let (t,c) = infer_expr (extend x ([],alpha) tyenv) exp in
    (TyFun(alpha,t),c) 
  | EPair (e1,e2) -> 
    let (t1,c1) = infer_expr tyenv e1 in
    let (t2,c2) = infer_expr tyenv e2 in
     (TyPair(t1,t2),c1@c2)
  | ENil -> let alpha = TyVar(new_tyvar ()) in (TyList alpha,[])
  | ECons (e1,e2) -> 
    let (t1,c1) = infer_expr tyenv e1 in
    let (t2,c2) = infer_expr tyenv e2 in
      (TyList t1,[(t2,TyList t1)]@c1@c2)
  | EApp (e1,e2) -> let (t1,c1) = infer_expr tyenv e1 in
                    let (t2,c2) = infer_expr tyenv e2 in
                    let alpha = TyVar(new_tyvar ()) in
                    (alpha,[(t1,TyFun(t2,alpha))]@c1@c2)
  (* | EMatch (e,pel) -> let (t,c) = infer_expr tyenv e in
                      let tcgl = map_tcgamma_pel pel tyenv in
                      let tcl = add_g_infer pel (select3from3 tcgl) tyenv in
                      let alpha = TyVar(new_tyvar ()) in
                      let finalc = (make_cons alpha (select1from2 tcl))@
                                   (List.concat (select2from2 tcl))@
                                   (make_cons t (select1from3 tcgl))@
                                   (List.concat (select2from3 tcgl))@c in
                      (*print_string "alpha\n";
                      print_type alpha;
                      print_string "\nsigma";
                      print_subst sigma;
                      print_string "\n";
                      print_constraints (make_cons alpha (select1from2 tcl));
                      print_string "\n";*)(alpha,finalc) *)

  | ELetRec (f,x,e1,e2) ->
    let alpha = TyVar(new_tyvar ()) in
    let beta = TyVar(new_tyvar ()) in
    let env' = (extend x ([],alpha) (extend f ([],TyFun(alpha,beta)) tyenv)) in
    let (t1,c1) = infer_expr env' e1 in
    let sigma = unify c1 in
    let s1 = ty_subst sigma (TyFun(alpha,beta)) in
    let delta = ty_subst_tyenv sigma tyenv in
    let (t2,c2) = infer_expr (extend f (generalize delta s1) delta) e2 in
      (t2,[(t1,beta)]@c1@c2) 
  | _ -> (raise NotSupported)

(* type_env -> expr -> type_schema *)
let decide_expr_type_schema tyenv exp = 
  match infer_expr tyenv exp with
  | (t,c) -> (*print_constraints c;
             print_string "\n";
             print_type t;
             print_string "\n";*)
             generalize tyenv (ty_subst (unify c) t)



let rec eval_match v pe =
  match pe with
  | [] -> (raise EvalErr)
  | (p,e)::rem -> try ((find_match p v),e) with
                  | PatternMatchError -> eval_match v rem
                  | _ -> (raise EvalErr)


let rec eval_expr env e =
  (*print_expr e;
  print_string "\n";*)
  match e with
  | EConstInt i ->
    VInt i
  | EConstBool b ->
    VBool b
  | EVar x ->
    (try
       let Thunk (exp,env') = (lookup x env) in eval_expr env' exp
     with
     | Unbound -> raise EvalErr)
  | EAdd (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1, VInt i2 -> VInt (i1 + i2)
     | _ -> raise EvalErr)
  | ESub (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1, VInt i2 -> VInt (i1 - i2)
     | _ -> raise EvalErr)
  | EMul (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1, VInt i2 -> VInt (i1 * i2)
     | _ -> raise EvalErr)
  | EDiv (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1, VInt i2 -> (match i2 with
                            | 0 -> (raise DivisionByZero)
                            | i2 -> VInt (i1 / i2))
     | _ -> raise EvalErr)
  | EEq (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1,  VInt i2  -> VBool (i1 = i2)
     | _ -> raise EvalErr)
  | ELt (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1,  VInt i2  -> VBool (i1 < i2)
     | _ -> raise EvalErr)
  | EIf (e1,e2,e3) ->
    let v1 = eval_expr env e1 in
    (match v1 with
     | VBool b ->
       if b then eval_expr env e2 else eval_expr env e3
     | _ -> raise EvalErr)
  | ELet (n,e1,e2) -> (eval_expr (extend n (Thunk (e1,env)) env) e2)
  | EFun (x,exp) -> VFun(x,exp,env)
  | ERecFun (f,x,exp,oenv) -> VRecFun(f,x,exp,oenv)
  | EPair (e1,e2) -> let v1 = eval_expr env e1 in
                     let v2 = eval_expr env e2 in
                        VPair(v1,v2)
  | ECons (e1,e2) -> let v1 = eval_expr env e1 in
                     let v2 = eval_expr env e2 in
                        VCons(v1,v2)
  | ENil ->  VNil                
  | EApp (e1,e2) -> let v1 = eval_expr env e1 in
                    (match v1 with
                     | VFun(x,e,oenv) -> eval_expr (extend x (Thunk (e2,env)) oenv) e
                     | VRecFun (f,x,e,oenv) ->let env' = extend x (Thunk (e2,env)) (extend f (Thunk (ERecFun(f,x,e,oenv),oenv)) oenv)
                                              in eval_expr env' e
                     | _ -> raise EvalErr)
 (* | EMatch (e,pel) -> let v = eval_expr env e in 
                     (try (let (xvl,e) = eval_match v pel in (eval_expr (extends xvl env) e)) with
                      | EvalErr -> (raise EvalErr)
                      | _ -> (raise EvalErr))  *)
  | ELetRec (f,x,e1,e2) ->
    let env' = extend f (Thunk (ERecFun(f,x,e1,env),env)) env
      in eval_expr env' e2 
  | _ -> (raise NotSupported)
and eval_command env tyenv c = 
  match c with
  | CExp e ->  let exp_tysc = decide_expr_type_schema tyenv e in
                 print_tysc exp_tysc;print_string "\n";
                 ("-", env, tyenv, eval_expr env e)
  | CDecl (n,e) -> let exp_tysc = decide_expr_type_schema tyenv e in 
                     let new_tyenv = extend n exp_tysc tyenv in
                       print_tysc exp_tysc;print_string "\n";
                       let v = eval_expr env e in 
                       ("val "^n,(extend n (Thunk (e,env)) env),new_tyenv,v)
  | CRecDecl (id,n,e) ->  let alpha = TyVar(new_tyvar ()) in
                          let beta = TyVar(new_tyvar ()) in
                          let env' = (extend n ([],alpha) (extend id ([],TyFun(alpha,beta)) tyenv)) in
                          let (t,c) = infer_expr env' e in
                          let (te,ce) = (TyFun(alpha,beta),[(t,beta)]@c) in 
                          let sigma = unify ce in
                          let delta = ty_subst_tyenv sigma tyenv in
                          let se = ty_subst sigma te in
                          let tysc = generalize delta se in
                          let new_tyenv = extend id tysc tyenv in
                             (*print_constraints ce;
                             print_subst (unify ce);
                             print_type te;
                             print_string "\n";*)
                             print_tysc tysc;
                             print_string "\n";
                             ("val "^id,(extend id (Thunk (ERecFun (id,n,e,env),env)) env),new_tyenv,VRecFun(id,n,e,env))
