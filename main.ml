type operator = Soma | Subt| Mult | Div | Ig | IgMen | Men | IgMai | Mai | Or | And | Nig

type ident = string (* identificador, variavel x *)
  
type tipo  = TyInt | TyBool | TyIdent of ident | TyFn of tipo * tipo | TyList of tipo | TyPair of tipo * tipo | TyMaybe of tipo
                                                 (*  T1 --> T2 *)      (* T list *)       (* T1 * T2 *)        (* maybe T *)
               
                                                              
                 (* Além das definidas na especificação do trabalho, coloquei Raise, Not e IsEmpty *)

type expr = Num of int
          | Bool of bool
          | Oper of operator * expr * expr  (* e1 op e2 *)
          | Not of expr  (* not e1 *)                                  
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
          | Raise
          | Cons of expr * expr (* e1 :: e2 *) 
          | Hd of expr  (* hd e *) 
          | Tl of expr  (* tl e *)
          | MatchNil of expr * expr     (* match e1 with nil ⇒ e2 *) 
          | Just of expr (* just e *)
          | Nothing of tipo  (* nothing : T *) 
          | MatchNothJust of expr * expr * ident * expr  (* match e1 with nothing ⇒ e2  |just x => e3)  *) 
                                                         
                            
              (* As últimas 4 expressões não foram implementadas *)                                       
                                                         
                                                         
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
    | Oper ((Ig | Nig | Men | Mai | IgMen | IgMai ), 
            e1, e2) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        (TyBool, c1 @ c2 @ [(t1, TyInt); (t2, TyInt)])
    
    (* C-<Oper>, onde <Oper> é uma operação Bool x Bool -> Bool *)
    | Oper ((And | Or), e1, e2) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        (TyBool, c1 @ c2 @ [(t1, TyBool); (t2, TyBool)])
          
   (* C-Not *)
    | Not e ->
        let (t, c) = collect env e in
        (TyBool, c @ [(t, TyBool)])
  
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
        
      (* C-Raise *)
    | Raise ->
        let x = newTypeVar () in
        (x, [])    
    
        
  
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
    
    



    (*  AVALIADOR BIG STEP *)


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
           | Nig,Vnum(n1),Vnum(n2) -> Vbool(n1 != n2)                               
           | Men,Vnum(n1),Vnum(n2) -> Vbool(n1 < n2)
           | Mai,Vnum(n1),Vnum(n2) -> Vbool(n1 > n2)
           | IgMen,Vnum(n1),Vnum(n2) -> Vbool(n1 <= n2)
           | IgMai,Vnum(n1),Vnum(n2) -> Vbool(n1 >= n2)
           | _,_,_ -> raise NoRuleApplies
          )
          
  (* Not *)
  | Not(e1) ->
      let v1 = eval env e1 in
      if v1 = RRaise then RRaise
      else if v1 = Vbool(true) then Vbool(false)
      else Vbool(true)        
  

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
        
  (* Tl *)
  | Tl(l) ->
      let v = eval env l in
      if v = RRaise || v = Vnil then RRaise else
        (match v with Vcons(e1, e2) -> e2
                    | _ -> raise NoRuleApplies
        )
        
  (* Raise *)
  | Raise -> RRaise      

  
  (* ALGUNS TESTES DA BIG STEP *)



let environment = empty_env;;



	(* Testes - cada um corresponde à uma regra da semântica BIG-STEP *)


(* BS-NUM *)
let numEx1 = Num(7);;
let evaln = eval environment numEx1;;

	(* BS-BOOL *)
let boolEx1 = Bool(true);;
let evalb = eval environment boolEx1;;

	(* BS-BOOL *)
let boolEx2 = Bool(false);;
let evalbb = eval environment boolEx2;;

(* BS-OPMULT *)
let mulEx1 = Oper(Mult,Num(2),Num(3));;
let evalm = eval environment mulEx1;;

(* BS-OPMULT *)
let multEx2 = Oper(Mult,Num(0),Num(5));;
let evalmm  = eval environment multEx2;;

(* BS-OPDIV *)
let divEx1 = Oper(Div,Num(4),Num(2));;
let evald = eval environment divEx1;;
  
(* BS-OPDIV *)
let divEx2 = Oper(Div,Num(15),Num(3));;
let evaldd = eval environment divEx2;;
  
(* BS-OP+ *)
let somEx1 = Oper(Soma,Num(1),Num(13));;
let evals = eval environment somEx1;;


(* testando update_env *)
let env = update_env "numAccept" (Vnum(7)) environment;;
lookup_environment "numAccept" env;;


(** Teste Let Rec com fatorial **)

let fat =
  LetRec ("fat", TyInt, TyInt, "n", TyInt, 
          IfElse (Oper (Ig, VarIdent "n", Num 0),
                  Num 1,
                  Oper(Mult, VarIdent "n", App (VarIdent "fat", Oper (Men, VarIdent "n", Num 1)))),
          VarIdent "fat");;

let progFat = App (fat, Num 3);; 
let evalpf = eval environment progFat;;

    
  
(** Teste Let Rec com RAISE e com fatorial **)


let lrecRaise = LetRec ("fat", TyInt, TyInt, "n", TyInt, IfElse (Oper (Ig, VarIdent "n", Num 0),
                                                                 Num 1,
                                                                 Oper (Mult, VarIdent "n", App (VarIdent "fat", Oper (Subt, VarIdent "n", Num 1)))), Raise);;
let evalLrecRaise = eval environment lrecRaise;;

  

(* BS-OP==TR *)
let eqAccept = Oper(Ig,Num(2),Num(2));;
let evalEqAccept = eval environment eqAccept;;

(* BS-OP==FLS *)
let eqReject = Oper(Ig,Num(2),Num(3));;
let evalEqReject = eval environment eqReject;;


	(* BS-OPANDTR *)
let andTrue = Oper(And,Bool(true),Bool(true));;
let evalAndTrue = eval environment andTrue;;
  
	(* BS-OPANDFLS *)

let andFalse = Oper(And,Bool(true),Bool(false));;
let evalAndFalse = eval environment andFalse;;


(* BS-IFTR *)
let ifTrue = IfElse(Oper(Ig,Num(1),Num(1)),Bool(true),Bool(false));;
let evalIfTrue = eval environment ifTrue;;
  
	(* BS-IFFLS *)
let ifFalse = IfElse(Oper(Ig,Num(1),Num(2)),Bool(true),Bool(false));;
let evalIfFalse = eval environment ifFalse;;


(* BS-FN *)
let funcAccept = Fn("x", TyInt ,Oper(Soma,VarIdent "x",Num(1)));;
let evalFuncAccept = eval environment funcAccept;;


	(* BS-LET x = x + 1*)
let letAccept = Let("x", TyInt ,Num(1), Oper(Soma,VarIdent("x"),Num(1)));;
let evalLetAccept = eval environment letAccept;;



	(* BS-APP x = x + 1 <---- x = 4 RESULTADO = X = 4 + 1*)
let appAccept = App(Fn("x", TyInt ,Oper(Soma,VarIdent "x",Num(1))),Num(4));;
let evalAppAccept = eval environment appAccept;;


let empty_env : env = [];;
	(* Nome da regra - Teste *)
	(* Teste Nil *)
	(* BS-NIL *)

let exp = Nil;;
eval empty_env exp;;

	(* Testes listas *)
	(* BS-CONS *)
let exp = Cons(Num(1), Nil);;
eval empty_env exp;;


(* BS-ISEMPTYNIL *)
let exp = IsEmpty(Nil);;
eval empty_env exp;;

	(* BS-ISEMPTYCONS *)
let exp = IsEmpty(Cons(Num(1), Nil));;
eval empty_env exp;;


	(* BS-HDNIL *)
let exp = Hd(Nil);;
eval empty_env exp;;

	(* BS-HDCONS *)
let exp = Hd(Cons(Num(2), Cons(Num(1), Nil)));;
eval empty_env exp;;


	(* BS-TLNIL *)
let exp = Tl(Nil);;
eval empty_env exp;;

	(* BS-TLCONS *)
let exp = Tl(Cons(Num(1), Nil));;
eval empty_env exp;;



(* TESTE MAP *)

let progMap =
  LetRec ("map", TyFn (TyInt, TyInt), TyFn (TyList TyInt, TyList TyInt),
          "f", TyFn (TyInt, TyInt),
          Fn("l", TyList TyInt,
             IfElse (Not (IsEmpty (VarIdent "l")),
                     Cons (App (VarIdent "f", Hd (VarIdent "l")), App (App (VarIdent "map", VarIdent "f"), Tl (VarIdent "l"))),
                     Nil)),
          Let ("inc", TyFn (TyInt, TyInt),
               Fn("n", TyInt, Oper (Soma, VarIdent "n", Num 1)),
               App (App (VarIdent "map", VarIdent "inc"), Cons (Num 0, Cons (Num 1, Nil)))));;
    
    
















    
(* TESTE DE OUTRAS EXPRESSÕES, PORÉM UTILIZANDO RAISE *)

(* BS-OP+RS1 *)
let sumRaise1 = Oper(Soma,Raise,Num(3));;
let evalSumRaise1 = eval environment sumRaise1;;

(* BS-OP+RS2 *)
let sumRaise2 = Oper(Soma,Num(2),Raise);;
let evalSumRaise2 = eval environment sumRaise2;;

(* BS-OPDIVRS1 *)
let divRaise1 = Oper(Div,Raise,Num(3));;
let evalDivRaise1 = eval environment divRaise1;;
  
	(* BS-OPDIVRS2 *)
let divRaise2 = Oper(Div,Num(2),Raise);;
let evalDivRaise2 = eval environment divRaise2;;


	(* BS-OPDIVZERO *)
let divRaise0 = Oper(Div,Num(3),Num(0));;
let evalDivRaise0 = eval environment divRaise0;;


(* BS-OP==RS1 *)
let eqRaise1 = Oper(Ig,Raise,Num(2));;
let evalEqRaise1 = eval environment eqRaise1;;
  
	(* BS-OP==RS2 *)
let eqRaise2 = Oper(Ig,Num(2),Raise);;
let evalEqRaise2 = eval environment eqRaise2;;


	(* BS-OPANDRS1 *)
let andRaise1 = Oper(And,Raise,Bool(true));;
let evalAndRaise1 = eval environment andRaise1;;
  
	(* BS-OPANDRS2 *)
let andRaise2 = Oper(And,Bool(true),Raise);;
let evalAndRaise2 = eval environment andRaise2;;


	(* BS-OPNOTRS *)
let notRaise = Not(Raise);;
let evalNotRaise = eval environment notRaise;;

(* BS-IFRS1 *)
let ifRaise1 = IfElse(Raise,Bool(true),Bool(false));;
let evalIfRaise1 = eval environment ifRaise1;;
  
	(* BS-IFRS2 *)
let ifRaise2 = IfElse(Oper(Ig,Num(1),Num(1)),Raise,Bool(false));;
let evalIfRaise2 = eval environment ifRaise2;;


(* BS-LETRS1 *)
let letRaise1 = Let("x", TyInt ,Raise, Oper(Soma,VarIdent("x"),Num(1)));;
let evalLetRaise1 = eval environment letRaise1;;
  
	(* BS-LETRS2 *)
let letRaise2 = Let("x", TyInt ,Num(1), Raise);;
let evalLetRaise2 = eval environment letRaise2;;


(* BS-APPRS1 *)
let appRaise1 = App(Raise,Num(4));;
let evalAppRaise1 = eval environment appRaise1;;
  
	(* BS-APPRS2 *)
let appRaise2 = App(Fn("x", TyInt ,Oper(Soma,VarIdent "x",Num(1))),Raise);;
let evalAppRaise2 = eval environment appRaise2;;
  

(* BS-CONSRS1 *)
let exp = Cons(Raise, Nil);;
eval empty_env exp;;

	(* BS-CONSRS2 *)
let exp = Cons(Num(1), Raise);;
eval empty_env exp;;


(* BS-ISEMPTYRS *)
let exp = IsEmpty(Raise);;
eval empty_env exp;;


(* BS-RAISE *)
let exp = Raise;;
eval empty_env exp;;


	(* BS-HDRS *)
let exp = Hd(Raise);;
eval empty_env exp;;


(* BS-TLRS *)
let exp = Tl(Raise);;
eval empty_env exp;;



