type operator = Soma | Subt| Mult | Div | Ig | Igmen | Men | IgMai | Mai | Or | And 

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
          (* | Nil *) 
          | Nil of tipo (* nil : T *) 
          | Cons of expr * expr (* e1 :: e2 *) 
          | Hd of expr  (* hd e *) 
          | Tl of expr  (* tl e *)
          | MatchNil of expr * expr     (* match e1 with nil ⇒ e2 *) 
          | Just of expr (* just e *)~ 
          | Nothing of tipo  (* nothing : T *) 
          | MatchNothJust of expr * expr * ident * expr  (* match e1 with nothing ⇒ e2  |just x => e3)  *) 
                                                         
                                                         
type value = Vnum of int
           | Vbool of bool
           | Vnil of value
                 (* | Vnil *)   
           | Vcons of value * value
           | Vpair of value * value 
                                    (* | VFn of variable * expression * env  *)
           | Vclos of ident * expr * env
           | Vrclos of ident * ident * expr * env                                         
                    

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
    TyVar ("T" ^ string_of_int(!varCount))
  in

  let rec collect env expr = match expr with
    
    (* C-Num *)
    | Num (_) ->
        (TyInt, [])
    
    (* C-Bool *)
    | Bool (_) ->
        (TyBool, [])
  

    (* C-IfThenElse *)

    | IfElse (e1, e2, e3) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        let (t3, c3) = collect env e3 in
        (t2, c1 @ c2 @ c3 @ [(t1, TyBool); (t2, t3)])
  
     (* C-Cons *)
    | Cons (e1, e2) ->
        let (t1, c1) = collect env e1 in
        let (t2, c2) = collect env e2 in
        (t2, c1 @ c2 @ [(TyList t1, t2)]) 
  
  
  in
  collect env expr
    
    






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
