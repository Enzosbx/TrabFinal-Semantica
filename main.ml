* DEFINIÇÃO DE TYPES *)

type operator = Soma | Subt| Mult | Div | Ig | Igmen | Men | IgMai | Mai | Or | And 
type ident = string
type tipo  = TyInt | TyBool | TyFn of tipo * tipo | TyList of tipo | TyPair of tipo * tipo | TyMaybe of tipo
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
           | Vcons of value * value
           | Vpair of value * value 
           | VFn of variable * expression * env and env = (ident * value) list            
                    
  
type type_env = (ident * tipo) list  (* ambiente é uma lista de pares identificador - tipo *)
  
type type_equations = (tipo * tipo) list (* equacoes de tipo 
  
    
