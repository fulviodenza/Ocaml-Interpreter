
(*
 -Dati Denotabili: Possono essere associati a un nome
 -Dati Esprimibili: se possono essere il risultato della valutazione di una espressione
  Complessa 
 -Memorizzabili: se possono essere memorizzati in una variabile)
*)
type ide = string;;
type exp = 
  Eint of int 
  | Ebool of bool 
  | Den of ide 
  | Mul of exp * exp 
  | Sum of exp * exp 
  | Diff of exp * exp 
  | Eq of exp * exp 
  | Or of exp* exp 
  | And of exp* exp 
  | Not of exp 
  | Ifthenelse of exp * exp * exp 
  | Let of ide * exp * exp 
  | Fun of ide * exp 
  | Letrec of ide * exp * exp 
  | Apply of exp * exp 
  | Estring of string
  (*Implemento la sintassi astratta del dizionario e delle operazioni associate*)
  | Edict of dict 
  | Clear of exp
  | ApplyOver of exp * exp
  | Get of ide * exp
  | Rm of ide * exp
  | Add of (ide * exp) * exp
and dict =
  Empty (*Dizionario Vuoto*)
  | Item of (ide * exp) * dict;;

(*Ambiente Polimorfo*)
(*Passo l'identificatore e mi restituisce la funzione che mi restituisce il valore*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = fun x -> v;; (*v può essere Int, Bool, Unbound, nel caso di lista vuota*)
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

type evT = 
  Int of int 
  | Bool of bool 
  | Float of float 
  | Closure of evFun 
  | String of string 
  | RecClosure of ide * evFun 
  | DictVal of evDic 
  | Unbound 
and evFun = ide * exp * evT env
and evDic = 
  EvEmpty 
  | Elem of (ide * evT) * evDic;;

(*TypeChecking, funzione che verra' usata nei descrittori*)
let typecheck (s : string) (v : evT) : bool = match s with
   "int" -> 
      (match v with
        Int(_) -> true 
        | _ -> false)|
   "bool" -> 
      (match v with
        Bool(_) -> true 
        | _ -> false)|
    "float" -> 
      (match v with
        Float(_) -> true
        | _ -> false)|
    "string" ->
      (match v with
        String(_) -> true
        | _ -> false)|
    "dict" ->
      (match v with
        DictVal(_) -> true
        | _ -> false)|
    _ -> failwith("Not a valid type");;

(*Funzioni primitive*)
(*Primitive Operazioni su interi*)
let int_sum x y = 
  match (typecheck "int" x ,typecheck "int" y ,x,y) with
    |(true,true,Int(a),Int(b)) -> Int(a+b)
    |(_,_,_,_) -> failwith ("run-time error")

let int_mul x y = if (typecheck "int" x) && (typecheck "int" y)
      then (match (x,y) with
        (Int(n),Int(u)) -> Int(n*u)
        |(_,_) -> failwith("Not a valid match"))
      else failwith("Type Error");;

let int_diff x y = if (typecheck "int" x) && (typecheck "int" y)
      then (match (x,y) with
        (Int(n),Int(u)) -> Int(n-u)
        |(_,_) -> failwith("Not a valid match"))
      else failwith("Type Error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
      then (match (x,y) with
        (Int(n),Int(u)) -> Bool(n=u)
        | (_, _) -> failwith("Not a valid match"))
      else failwith("Type error");;

  (*Primitive espressioni logiche*)
let and_bool x y = if (typecheck "bool" x) && (typecheck "bool" y)
      then (match (x,y) with
        (Bool(n),Bool(u)) -> Bool(n&&u)
        | (_,_) -> failwith("Not a valid match"))
      else failwith("Type Error");;

let or_bool x y = if (typecheck "bool" x) && (typecheck "bool" y)
      then (match (x,y) with
        |(Bool(n),Bool(u)) -> Bool(n || u)
        |(_,_) -> failwith("Not a valid match"))
      else failwith("Type Error");;

let not_bool x = if (typecheck "bool" x)
      then (match x with
        Bool(true) -> Bool(false) 
        | Bool(false) -> Bool(true)	
        | _ -> failwith("Not a valid match"))
      else failwith("Type error");;

(*Inizio interprete*)
let rec eval (e:exp) (r: evT env) : evT = match e with
  Eint(i) -> Int i
  | Ebool(i) -> Bool i
  | Estring(s) -> String s
  | Den i -> applyenv r i
  | Sum(a,b) -> int_sum (eval a r) (eval b r)
  | Mul(a,b) -> int_mul (eval a r) (eval b r)
  | Diff(i,j) -> int_diff (eval i r) (eval j r)
  | And(a, b) -> and_bool (eval a r) (eval b r) 
  | Or(a,b) -> or_bool (eval a r) (eval b r)
  | Not(a) -> not_bool (eval a r)
  | Eq(a, b) -> eq (eval a r) (eval b r)
  | Ifthenelse(a, b, c) -> 
    let g = (eval a r) in (*Vai nell'ambiente e cerca un tipo esprimibile che corrisponde alla variabile a*)
      (match (typecheck "bool" g , g) with
        (true,Bool(true)) -> eval b r
        |(true,Bool(false)) -> eval c r
        |(_,_) -> failwith("nope")
      )
  | Let(i,e1,e2) -> eval e2 (bind r i (eval e1 r))
  | Apply(rFun,actParam) -> 
    let fClosure = (eval rFun r) in 
      (match fClosure with
      Closure(par,body,envF) -> 
        (eval body (bind envF par (eval actParam r)))
      | RecClosure(f, (recArg,fBody,fDecEnv)) ->
        let aVal = (eval actParam r) in
          let rEnv = bind fDecEnv f fClosure in
            let aEnv = bind rEnv recArg aVal in
              eval fBody aEnv
      | _ -> failwith("not a function"))
  | Fun(param,body) -> Closure(param,body,r)
  | Letrec(fIde, funDef, letBody) ->
    (match funDef with
      Fun(i, fBody) -> let r1 = (bind r fIde (RecClosure(fIde, (i, fBody, r)))) in
        eval letBody r1 
      | _ -> failwith("non functional def")
    )
  (*Implementazione progetto*)
  | Edict dDict -> DictVal(eval_d dDict r)
  | Clear dDict -> DictVal(EvEmpty)
  | ApplyOver(f,expDict)->
		(match (eval expDict r) with
			DictVal(d) -> let fVal = eval f r in DictVal(apply_o fVal d)
      |_ -> failwith("Not a valid match"))
  | Get(iEl,expDict) -> (*IMPLEMENTATA*)
    (let v = (eval expDict r) in 
      match v with
      DictVal(a) -> search_d a iEl
      | _ -> failwith("not a dictionary")
    )
  | Rm(iEl,expDict) ->
    (match (eval expDict r) with
      DictVal(d) -> DictVal(remove_d d iEl r)
      | _ -> failwith("not a dictionary")
    )
  | Add((iEl,expEl),expDict) ->
    (match (eval expDict r) with
      DictVal(d) -> DictVal(add_d d iEl (eval expEl  r) r)
      | _ -> failwith("not a dictionary")
    )

and eval_d (d: dict) (r: evT env) : evDic = 
  (match d with
    Empty -> EvEmpty
    | Item((idItem,expItem),restDict) -> 
      if (check_d idItem restDict) then Elem((idItem,eval expItem r), eval_d restDict r)
      else (eval_d restDict r)
  )

and apply_o (f : evT) (d : evDic) : evDic =
  (
    match f,d with
    _,EvEmpty -> EvEmpty
    | Closure(par,body,envF),Elem((id,el),restDict) ->
      Elem((id,(eval body (bind envF par el))), apply_o f restDict)
    | RecClosure(g, (recArg,fBody,fDecEnv)),Elem((id,el),restDict) ->
        let rEnv = bind fDecEnv g f in
          let aEnv = bind rEnv recArg el in
            Elem((id, eval fBody aEnv),apply_o f restDict)
    | _ -> failwith("Not a function")
  )

and remove_d (d: evDic) (i: ide) (r: evT env) : evDic = 
  (match d with
    EvEmpty -> EvEmpty
    | Elem((id,e),restDict) -> if id=i then restDict else (remove_d restDict id r)
  )

and add_d (d: evDic) (i: ide) (eEl: evT) (r: evT env) : evDic =
  (match d with
    EvEmpty -> Elem((i,eEl),EvEmpty)
    | Elem((id,el),restDict) -> Elem((id,el),(add_d restDict i eEl r))
  )
and search_d (d: evDic) (i: ide): evT =
  (match d with
    EvEmpty -> failwith("no element")
    | Elem((id,el),restDict) -> if id=i then el else search_d restDict i
  )
and check_d (i:ide) (d:dict) : bool =
  (
    match d with
    Empty -> true
    | Item((id,_),restDict) -> if id = i then false else check_d i restDict
  )
;;