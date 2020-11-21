datatype 'a expression = Not of 'a expression
                    | Or of 'a expression list
                    | And of 'a expression list
                    | Eq of 'a expression list
                    | Imp of 'a expression * 'a expression
                    | Var of 'a
                    | True | False;

fun isSimple(exp : 'a expression) : bool =
    case exp of
    True => false
    | False => false
    | Not True => false
    | Not False => false
    | Var e => true
    | Not (Var e) => true
    | Not e => false
    | And l => false
    | Or l => false
    | Eq l => false
    | Imp (e1, e2) => false

fun rmEmpty (exp: 'a expression) : 'a expression = 
    case exp of
    True => True
    | False => False
    | Var e => Var e
    | Not e => Not (rmEmpty e)
    | And [] => True
    | Or [] => False
    | Eq [] => True
    | And [e] => rmEmpty e
    | Or [e] => rmEmpty e
    | Eq [e] => True (* Zakaj? Zato ker to lahko smatramo kot e <=> e? *)
    | And l => And (map (fn x => (rmEmpty x)) l)
    | Or l => Or (map (fn x => (rmEmpty x)) l)
    | Eq l => Eq (map (fn x => (rmEmpty x)) l)
    | Imp (e1, e2) => Imp ((rmEmpty e1), (rmEmpty e2))

fun rmConstants(exp : ''a expression) : ''a expression =
    case rmEmpty exp of
    True => True
    | False => False
    | Not True => False
    | Not False => True
    | Var e => Var e
    | Not (Var e) => Not (Var e)
    | Not (Not e) => rmConstants e
    | Not e => rmConstants (Not (rmConstants e))
    | And l => if List.exists (fn x => x = False) l
               then False 
               else if List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l)
               then And l
               else rmConstants (And (map (fn x => rmConstants x) (List.filter (fn x => not (x = True)) l)))
    
val t1 = And [Var 1, Not (Var 2), Var 3];
val t4 = And [True, Not (And [False, True])];