(*
 -Dati Denotabili: Possono essere associati a un nome
 -Dati Esprimibili: se possono essere il risultato della valutazione di una espressione
  Complessa 
 -Memorizzabili: se possono essere memorizzati in una variabile)
*)
type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Mul of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp* exp | And of exp* exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp | Apply of exp * exp;;

(*Ambiente Polimorfo*)
(*Passo l'identificatore e mi restituisce la funzione che mi restituisce il valore*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = fun x -> v;; (*v può essere Int, Float, Bool, Unbound, nel caso di lista vuota*)
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

type evT = Int of int | Bool of bool | Float of float | Closure of evFun | RecClosure of ide * evFun | Unbound
and evFun = ide * exp * evT env;;

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
  |Eint(i) -> Int i
  |Ebool(i) -> Bool i
  |Den i -> applyenv r i
  |Sum(a,b) -> int_sum (eval a r) (eval b r)
  |Mul(a,b) -> int_mul (eval a r) (eval b r)
  |Diff(i,j) -> int_diff (eval i r) (eval j r)
  |And(a, b) -> and_bool (eval a r) (eval b r) 
  |Or(a,b) -> or_bool (eval a r) (eval b r)
  |Not(a) -> not_bool (eval a r)
  |Eq(a, b) -> eq (eval a r) (eval b r)
  |Ifthenelse(a, b, c) -> 
    let g = (eval a r) in (*Vai nell'ambiente e cerca un tipo esprimibile che corrisponde alla variabile a*)
      (match (typecheck "bool" g , g) with
        (true,Bool(true)) -> eval b r
        |(true,Bool(false)) -> eval c r
        |(_,_) -> failwith("mi faccio di coca")
      )
  |Let(i,e1,e2) -> eval e2 (bind r i (eval e1 r))
  |Apply(actParam,rFun) -> 
    let fClosure = (eval rFun r) in 
      (match fClosure with
      |Closure(par,body,envF) -> 
        (eval body (bind envF par (eval actParam r)))
      |RecClosure(f, (recArg,fBody,fDecEnv)) ->
        let aVal = (eval actParam r) in
          let rEnv = bind fDecEnv f fClosure in
            let aEnv = bind rEnv recArg aVal in
              eval fBody aEnv
      |_ -> failwith("not a function"))
  |Apply(_,_) -> failwith("not first order function")
  |Fun(param,body) -> Closure(param,body,r)
  |Letrec(fIde, funDef, letBody) ->
    (match funDef with
    |Fun(i, fBody) -> let r1 = (bind r fIde (RecClosure(fIde, (i, fBody, r)))) in
      eval letBody r1 
    |_ -> failwith("non functional def"));;