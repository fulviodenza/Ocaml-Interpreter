(*TESTCASES*)
  
let env0 = emptyenv Unbound;;

let dict1 = Edict(Item((("Nome"),(Estring "Fulvio")),Item((("Eta"),(Eint 21)),Item((("Matricola"),(Eint 544006)),Empty))));;
let dict2 = Edict(Item((("CINQUE:"),(Eint 5)),Item((("QUATTRO:"),(Eint 4)),Item((("TRE:"),(Eint 3)),Empty))));;
let f = Fun("x",Diff(Den "x",Eint 1));;
let a = Apply(Eint 3,f);;
let test = ApplyOver(f,dict2);;
let testget = Get("CINQUE:",dict2);;
let removed = Rm("CINQUE:",dict2);;
let added = Add((("SEI:"),(Eint 6)),dict2);;



(*Applicazione di funzione ricorsiva a dizionario*)
let testRec = 
    Letrec("fact",Fun("x",Ifthenelse(Eq(Den "x",Eint 0),Eint 1,Mul(Den "x",Apply(Den "fact",Diff(Den "x",Eint 1))))),
    ApplyOver(Den "fact",dict2));;

eval testRec env0;; (*it works!*)

(* Il dizionario è davvero immutabile? *)
let testDue =
    Let(
        "d",
        Edict(
            Item(("NomeDip0",Estring "Dipartimento Giurisprudenza"),Empty)
        ),
        Let(
            "a",
            Rm("NomeDip0",Den "d"),Den "d"
        )
    );;

eval testDue env0;; (*Si*)

let testTre = 
    Let(
        "a",
        Edict(
            Item(("NomeDip0", Estring "Dipartimento Matematica"),Empty)
        ),
        Add(
            ("NomeDip1",
            Estring "Dipartimento Informatica"),
            Den "a"
        )
    )
;;

eval testTre env0;; (*ok*)

let testQuattro = 
    Let(
        "ld",
        Edict(
            Item(("NomeDip", Estring "Dipartimento Lettere"),Empty)
        ),
        Get(
            "NomeDip",
            Den "ld"
        )
    )
;;

eval testQuattro env0;; (*ok*)

let testCinque = 
  Let(
        "ls",
        Edict(
            Item(
                ("eta", Eint 20),
                Empty
            )
        ),
        ApplyOver(
            Fun(
               "x",
               Sum(
                 Eint 1,
                 Den "x"
               )
            ),
            Den "ls"
        )
      );;
      
eval testCinque env0;; (*Apposto ce l'hai fatta*)