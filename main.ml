type operator = Soma | Subt| Mult | Div | Ig | IgMen | Men | IgMai | Mai | Or | And 

type ident = string (* identificador, variavel x *)
  
type tipo  = TyInt | TyBool | TyIdent of ident | TyFn of tipo * tipo | TyList of tipo | TyPair of tipo * tipo | TyMaybe of tipo
                                                 (*  T1 --> T2 *)      (* T list *)       (* T1 * T2 *)        (* maybe T *)
               
  
type expr = Num of int
          | Bool of bool
          | Oper of operator * expr * expr  (* e1 o e2 *)
          | IfElse of expr * expr * expr     (* if e1 then e2 else e3 *) 
          | VarIdent of ident     (* x *)
          | App of expr * expr  (* e1 e2 *)
          | Fn of ident * tipo * expr  (* fn x: T => e *)
          | Let of ident * tipo * expr * expr (*  let x : T = e1 in e2 *)
          | LetRec of ident * tipo * tipo * ident * tipo * expr * expr  (* letrec f: T1 → T2 ... *)  
          | Pair of expr * expr (* (e1, e2) *)
          | Fst of expr (* fst e *)
          | Snd of expr (* snd e *) 
          | IsEmpty of expr (* isEmpty e *)       
          | Nil 
                (*| Nil of tipo (* nil : T *) *)
          | Cons of expr * expr (* e1 :: e2 *) 
          | Hd of expr  (* hd e *) 
          | Tl of expr  (* tl e *)
          | MatchNil of expr * expr     (* match e1 with nil ⇒ e2 *) 
          | Just of expr (* just e *)
          | Nothing of tipo  (* nothing : T *) 
          | MatchNothJust of expr * expr * ident * expr  (* match e1 with nothing ⇒ e2  |just x => e3)  *) 
                                                         
                                                         
type value = Vnum of int
           | Vbool of bool
                 (*| Vnil of value*)
           | Vnil  
           | Vcons of value * value
           | Vpair of value * value 
           | Vclos of ident * expr * env
           | Vrclos of ident * ident * expr * env       
           | RRaise             
                    

and env = (ident * value) list  (* ambiente é uma lista de pares identificador - tipo *)
  
 

(* ------------------------------ *)
(* ------------------------------ *)
(* INICIO DAS FUNÇÕES AUXILIARES TYPE INFER *)
(* ------------------------------ *)
(* ------------------------------ *)                               
        

    (* CONSTRAINTS *)                        
  
  
   
   (* um par (T1, T2) representa T1 = T2, onde T1 é considerado o tipo inferido
(actual) e T2 o tipo esperado (expected). *) 
type typeConstraint = tipo * tipo 
type typeConstraintSet = typeConstraint list (* conjunto de type constraints *)
             
                                             
       
                                             
  
   (* COLETA DE EQUACOES DE TIPO *)                                     
                                             
                                             
                                                                             
type typeEnv = (ident * tipo) list

  
exception UndefinedIdentifier of ident

(* Retorna o valor associado a uma chave em uma lista de pares (chave, valor) *)

let lookup = List.assoc
  
               
let collectTyEqs env expr = let varCount = ref (-1) in
  
  let newTypeVar () =
    incr varCount;
    TyIdent ("T" ^ string_of_int(!varCount))
  in

  let rec collect env expr = match expr with
    
    (* C-Num *)
    | Num (_) ->
        (TyInt, [])
    
    (* C-Bool *)
    | Bool (_) ->
        (TyBool, [])
  
    (* C-<Oper>, onde <Oper> é uma operação Int x Int -> Int *)
    | Oper ((Soma | Subt | Mult | Div), e1, e2) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        (TyInt, c1 @ c2 @ [(t1, TyInt); (t2, TyInt)])
    
    (* C-<Oper>, onde <Oper> é uma operação Int x Int -> Bool *)
    | Oper ((Ig | Men | Mai | IgMen | IgMai), 
            e1, e2) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        (TyBool, c1 @ c2 @ [(t1, TyInt); (t2, TyInt)])
    
    (* C-<Oper>, onde <Oper> é uma operação Bool x Bool -> Bool *)
    | Oper ((And | Or), e1, e2) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        (TyBool, c1 @ c2 @ [(t1, TyBool); (t2, TyBool)])
  
    (* C-IfElse *)

    | IfElse (e1, e2, e3) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        let (t3, c3) = collect env e3 in
        (t2, c1 @ c2 @ c3 @ [(t1, TyBool); (t2, t3)])
        
     
    (* C-VarIdent*)
    | VarIdent x ->
        (try let t = lookup x env in
           (t, [])
         with Not_found -> raise (UndefinedIdentifier x))
    
    (* C-App *)
    | App (e1, e2) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        let x = newTypeVar () in
        (x, c1 @ c2 @ [(t1, TyFn (t2, x))])
    
    (* C-Fn *)
    | Fn (x, t, e) ->
        let (t1, c) = collect ((x, t)::env) e in
        (TyFn (t, t1), c)
        
      
    (* C-Let *)
    | Let (x, t, e1, e2) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect ((x, t)::env) e2 in
        (t2, c1 @ c2 @ [(t1, t)])
        
     (* C-LetRec *)
    | LetRec (f, t', t, y, t'', e1, e2) ->
        let (t1, c1) = collect ((f, TyFn (t', t))::(y, t')::env) e1 in
        let (t2, c2) = collect ((f, TyFn (t', t))::env) e2 in
        (t2, c1 @ c2 @ [(t1, t); (t', t'')])
        
         
    (* C-Nil *)
    | Nil ->
        let x = newTypeVar () in
        (TyList x, [])
  
     (* C-Cons *)
    | Cons (e1, e2) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        (t2, c1 @ c2 @ [(TyList t1, t2)])
  
        (* C-Hd *)
    | Hd e ->
        let (t, c) = collect env e in
        let x = newTypeVar () in
        (x, c @ [(t, TyList x)])
        
    (* C-Tl *)
    | Tl e ->
        let (t, c) = collect env e in
        let x = newTypeVar () in
        (TyList x, c @ [(t, TyList x)])
    
    (* C-IsEmpty *)
    | IsEmpty e ->
        let (t, c) = collect env e in
        let x = newTypeVar () in
        (TyBool, c @ [(t, TyList x)])
    
        
  
  in
  collect env expr
    
    
    
    (* ALGORITMO DE SUBSTITUIÇÃO DE VARIAVEIS DE TIPO *)
    
type substMapping  = ident * tipo
type substituition = substMapping list

let rec applySubstMapping (x, tSub) t = match t with
  | TyIdent y when y = x -> tSub
  | TyIdent y            -> TyIdent y
  | TyInt              -> TyInt
  | TyBool             -> TyBool
  | TyFn (t1, t2)      -> TyFn (applySubstMapping (x, tSub) t1,
                                applySubstMapping (x, tSub) t2)
  | TyList t           -> TyList (applySubstMapping (x, tSub) t)

let rec applySubs subs t = match subs with
  | []              -> t
  | mapping :: tail -> applySubs tail (applySubstMapping mapping t)





    (* UNIFY *)
  
exception OccursCheckError of ident * tipo
exception UnificationError of typeConstraint

let unify eqs =
  let rec occurs x t = match t with
    | TyIdent y             -> y == x
    | (TyInt | TyBool)    -> false
    | TyFn (t1, t2)       -> occurs x t1 || occurs x t2
    | TyList t            -> occurs x t
  in
  
  let rec replaceInType x tSub t = applySubstMapping (x, tSub) t
  in
  
  let rec replace x t constraints = match constraints with
    | [] -> []
    | (t1, t2) :: c -> (replaceInType x t t1,
                        replaceInType x t t2) :: (replace x t c)
  in
  
  let rec solve subst eqs = match eqs with
    | [] ->
        subst
    
    | (TyInt, TyInt) :: c ->
        solve subst c
    | (TyBool, TyBool) :: c ->
        solve subst c
    | (TyIdent x, TyIdent y) :: c when x == y ->
        solve subst c
    
    | (TyIdent x, t) :: c ->
        if occurs x t
        then raise (OccursCheckError (x, t))
        else solve (subst @ [(x, t)]) (replace x t c)
    | (t, TyIdent x) :: c ->
        if occurs x t
        then raise (OccursCheckError (x, t))
        else solve (subst @ [(x, t)]) (replace x t c)
    
    | (TyFn (t1, t2), TyFn (t3, t4)) :: c ->
        solve subst ((t3, t1) :: (t2, t4) :: c)
    | (TyList t1, TyList t2) :: c ->
        solve subst ((t1, t2) :: c)
    
    | (actualType, expectedType) :: c ->
        raise (UnificationError (actualType, expectedType))
  in
  solve [] eqs   
  
    





(* SUBSTITUI AS VARIAVEIS DE TIPO CORRESPONDENTES *)    

type substMapping  = ident * tipo
type substituition = substMapping list

let rec applySubstMapping (x, tSub) t = match t with
  | TyIdent y when y = x -> tSub
  | TyIdent y            -> TyIdent y
  | TyInt              -> TyInt
  | TyBool             -> TyBool
  | TyFn (t1, t2)      -> TyFn (applySubstMapping (x, tSub) t1,
                                applySubstMapping (x, tSub) t2)
  | TyList t           -> TyList (applySubstMapping (x, tSub) t)

let rec applySubs subs t = match subs with
  | []              -> t
  | mapping :: tail -> applySubs tail (applySubstMapping mapping t) 
                         
  
(* ------------------------------ *)
(* ------------------------------ *)
(* FIM DAS FUNÇÕES AUXILIARES TYPE INFER *)
(* ------------------------------ *)
(* ------------------------------ *)
                         
               



(* TYPE INFER *)
                                   
let typeInfer env expr =
  let (t, c) = collectTyEqs env expr in
  let subs = unify c in
  applySubs subs t
    
    



    (*  BIG STEP *)


(* Excecao a ser ativada quando nenhuma regra se aplica. *)
exception NoRuleApplies

exception UndefinedIdentifier of ident

let remove_tuple var list =
  List.filter (fun (k,_) -> k <> var) list


let update_env var v1 env : env = match env with
    [] -> [(var,v1)]
  | hd::tl ->
      if (List.exists (fun (k,_) -> k = var) env)
      then List.append (remove_tuple var env) [(var,v1)]
      else List.append env [(var,v1)]


let lookup_environment = List.assoc

let empty_env : env = []

let rec eval (env:env) (exp : expr) : value =	match exp with
	(* Valores *)
    Num(n) -> Vnum(n)
  | Bool(b) -> Vbool(b)

	(* Operações *)

	(* Operações binárias *)
  | Oper(op,e1,e2) ->
      let n1 = eval env e1 in
    	(* O primeiro operando avalia para Raise *)
      if n1 = RRaise then RRaise else
        let n2 = eval env e2 in
	    (* O segundo operando avalia para Raise *)
        if n2 = RRaise then RRaise else
    	(* Nenhum dos operandos avalia para raise *)

          (match op,n1,n2 with
             Soma,Vnum(n1),Vnum(n2) -> Vnum(n1 + n2)
           | Subt,Vnum(n1),Vnum(n2) -> Vnum(n1 - n2)
           | Mult,Vnum(n1),Vnum(n2) -> Vnum(n1 * n2)
           | Div,Vnum(n1),Vnum(n2) ->(match n2 with
                 0 -> RRaise
               | _ -> Vnum(n1 / n2)
             )
           | Ig,Vnum(n1),Vnum(n2) -> Vbool(n1 == n2)
           | And,Vbool(n1),Vbool(n2) -> Vbool(n1 && n2)
           | Or,Vbool(n1),Vbool(n2) -> Vbool(n1 || n2) 
           | Men,Vnum(n1),Vnum(n2) -> Vbool(n1 < n2)
           | Mai,Vnum(n1),Vnum(n2) -> Vbool(n1 > n2)
           | IgMen,Vnum(n1),Vnum(n2) -> Vbool(n1 <= n2)
           | IgMai,Vnum(n1),Vnum(n2) -> Vbool(n1 >= n2)
           | _,_,_ -> raise NoRuleApplies
          )
  

	(* IfElse *)
  | IfElse(e1,e2,e3) ->
      let b = eval env e1 in
      if b = RRaise then RRaise else
      if b = Vbool(true) then
        let v1 = eval env e2 in
        if v1 = RRaise then RRaise else v1
      else
        let v2 = eval env e3 in
        if v2 = RRaise then RRaise else v2

	(* Variável *)
  | VarIdent(ident) ->
      (try lookup_environment ident env
       with Not_found -> raise (UndefinedIdentifier ident))


	(* Aplicação *)
  | App(e1,e2) ->
      let v1 = eval env e1 in
      if v1 = RRaise then RRaise else
        let v2 = eval env e2 in
        if v2 = RRaise then RRaise else

          (match v1,v2 with
             Vclos(var,e,env), v ->
               let n = eval (update_env var v env) e in
               if(n = RRaise)
               then RRaise
               else n

           | Vrclos(f,x,e,env), v ->
               let n_rec = eval (update_env f (Vrclos(f,x,e,env)) (update_env x v env)) e in
               if(n_rec = RRaise)
               then RRaise
               else n_rec
           | _ -> raise NoRuleApplies
          )


	(* Função - Fn *) 
  | Fn(ident,tipo,exp) -> Vclos(ident,exp,env)

	(* Let  *)
  | Let(var,tipo,e1,e2) ->
      let v1 = eval env e1 in
      if v1 = RRaise then RRaise else
        eval (update_env var v1 env) e2 

	(* LetRec *)
  | LetRec(varF,t1,t2,varX,tX,e1,e2) ->
      let v = eval (update_env varF (Vrclos (varF, varX, e1, env)) env) e2 in
      if v = RRaise then RRaise else v 

	(* Nil *)
  | Nil -> Vnil

    (* Cons *)
  | Cons(elemento,lista) ->
      let n = eval env elemento in
      if n = RRaise then RRaise
      else
        let n_lista = eval env lista in
        if n_lista = RRaise then RRaise
        else Vcons(n,n_lista)

    (* IsEmpty *)
  | IsEmpty(e1) ->
      let n = eval env e1 in
      if n = RRaise then RRaise
      else if n = Vnil then Vbool(true) else Vbool(false)

	(* Hd *)
  | Hd(l) ->
      let v = eval env l in
      if v = RRaise || v = Vnil then RRaise else
        (match v with Vcons(e1, e2) -> e1
                    | _ -> raise NoRuleApplies
        )

  
  (* ALGUNS TESTES DA BIG STEP *)

let environment = empty_env;;

	(* Testes - cada um corresponde à uma regra da semântica BIG-STEP *)

	(* BS-NUM *)
let numAccept = Num(7);;
let eval = eval environment numAccept;;

	(* BS-BOOL *)
let boolAccept = Bool(true);;
let eval = eval environment boolAccept;;

(* BS-OPDIV *)
let divAccept = Oper(Div,Num(4),Num(2));;
let eval = eval environment divAccept;;
  

(* BS-OP+ *)
let sumAccept = Oper(Soma,Num(1),Num(1));;
let eval = eval environment sumAccept;;


(* BS-OPMULT *)
let sumAccept = Oper(Mult,Num(2),Num(3));;
let eval = eval environment sumAccept;;






