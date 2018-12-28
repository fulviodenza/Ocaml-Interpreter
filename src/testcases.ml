(*TESTCASES*)
  
let env0 = emptyenv Unbound;;

let dict1 = Edict(Item((("Nome"),(Estring "Fulvio")),Item((("Eta"),(Eint 21)),Empty)));;
let dict2 = Edict(Item((("CINQUE:"),(Eint 5)),Item((("QUATTRO:"),(Eint 4)),Item((("TRE:"),(Eint 3)),Empty))));;
let f = Fun("x",Diff(Den "x",Eint 1));;
let a = Apply(Eint 3,f);;
let test = ApplyOver(f,dict2);;
let testget = Get("CINQUE:",dict2);;
let removed = Rm("CINQUE:",dict2);;
let added = Add((("SEI:"),(Eint 6)),dict2);;



(*Applicazione di funzione ricorsiva a dizionario*)
let testGG =
    Letrec(
        "fact",
        Fun(
            "x",
            Ifthenelse(
                Eq(
                    Den "x",
                    Eint 0
                ),
                Eint 1,
                Mul(
                    Den "x",
                    Apply(
                        Den "fact",
                        Diff(
                            Den "x",
                            Eint 1
                        )
                    )
                )
            )
        ),
        ApplyOver(
            Den "fact",
            dict2
        )
    )
;;
eval testGG env0;; (*worka fine gg*)
(* Il dizionario è davvero immutabile? *)
let testGGDue =
    Let(
        "d",
        Edict(
            Item(
                (
                    "name",
                    Estring "giua"
                ),
                Empty
            )
        ),
        Let(
            "a",
            Rm(
                "name",
                Den "d"
            ),
            Den "d"
        )
    )
;;
eval testGGDue env0;; (*YEEEEEAH RIMANE IMMUTATO, QUINDI FUNGE *)

let testGGTre = 
    Let(
        "a",
        Edict(
            Item(
                ("nome", Estring "giua"),
                Empty
            )
        ),
        Add(
            ("nome",
            Estring "luiggi"),
            Den "a"
        )
    )
;;

eval testGGTre env0;; (*Funge anche questa gggg fulvio*)

let testGGQuattro = 
    Let(
        "a",
        Edict(
            Item(
                ("nome", Estring "giua"),
                Empty
            )
        ),
        Get(
            "nome",
            Den "a"
        )
    )
;;

eval testGGQuattro env0;; (*Come vedi this funziona*)
let testGGCinque = 
  Let(
        "a",
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
            Den "a"
        )
      );;
eval testGGCinque env0;; (*Apposto ce l'hai fatta*)