datatype 'a expr = !! of 'a expr
                | \/ of 'a expr * 'a expr
                | /\ of 'a expr * 'a expr
                | <=> of 'a expr * 'a expr
                | ==> of 'a expr * 'a expr
                | V of 'a
                | T | F;
infix 5 <=>;
infixr 6 ==>;
infix 7 \/;
infix 8 /\;

datatype 'a expression = Not of 'a expression
                    | Or of 'a expression list
                    | And of 'a expression list
                    | Eq of 'a expression list
                    | Imp of 'a expression * 'a expression
                    | Var of 'a
                    | True | False;

datatype 'a stream = Next of 'a * (unit -> 'a stream);

fun lcg seed =
    let fun lcg seed =
        Next (seed, fn () =>
            lcg (LargeInt.mod (1103515245 * seed + 12345, 0x7FFFFFFF)))
    in lcg (LargeInt.fromInt seed) end;

fun int2bool i = LargeInt.mod (i, 2) = 1;

exception InvalidCNF;
exception NotImplemented;

Control.Print.printDepth := 100;
Control.Print.printLength := 1000;
Control.Print.stringDepth := 1000;

fun checkCombine(l1, l2) = 
    case l2 of
    [] => l1
    | h::t => 
        if (List.exists (fn x => x = h) l1) then
            checkCombine(l1, t)
        else
            checkCombine(l1 @ [h], t)

fun getVars (exp : ''a expression) : ''a list =
let
    
    fun getVarsList(exp_l : ''a expression list) : ''a list =
        case exp_l of
        [] => []
        | h::t => checkCombine(getVars h, getVarsList t)
in
    case exp of
    True => []
    | False => []
    | Var i => [i]
    | Not i => (getVars i)
    | Imp (i, j) => checkCombine(getVars i , getVars j)
    | And l => (getVarsList l)
    | Or l => (getVarsList l)
    | Eq l => (getVarsList l)
end

fun eval vars exp  =
let
    fun And'(list : bool list) : bool =
        case list of
        [] => true
        | h::t => h andalso (And' t)
    
    fun Or'(list : bool list) : bool =
        case list of
        [] => false
        | h::t => h orelse Or'(t)

    fun Eq'(list : bool list) : bool =
        case list of
        [] => true
        | h::t =>  if (List.all(fn x => x = h) list) then true else false
in 
    case exp of
    True => true
    | False => false
    | Var i => if List.exists (fn x => x = i) vars then true else false 
    | Not i => not (eval vars i)
    | Imp (i, j) => not (eval vars i) orelse (eval vars j)
    | And l => And'(map (fn x => (eval vars x)) l)
    | Or l => Or'(map (fn x => (eval vars x)) l)
    | Eq l => Eq'(map (fn x => (eval vars x)) l)
end

fun rmEmpty (exp: 'a expression) : 'a expression = 
    case exp of
    True => True
    | False => False
    | Var e => Var e
    | Not e => Not (rmEmpty e)
    | And [] => True
    | Or [] => False
    | Eq [] => True
    | And [e] => rmEmpty e (* e and e is e*)
    | Or [e] => rmEmpty e (* e or e is e*)
    | Eq [e] => True (* e <=> e is true *)
    | And l => And (map (fn x => (rmEmpty x)) l)
    | Or l => Or (map (fn x => (rmEmpty x)) l)
    | Eq l => Eq (map (fn x => (rmEmpty x)) l)
    | Imp (e1, e2) => Imp ((rmEmpty e1), (rmEmpty e2))

fun makePairs (l : 'a list) : ('a * 'a) list =
    case l of
    [] => []
    | [i] => []
    | h::t => [(h, (hd t))] @ makePairs(t)

fun beautify (exp: 'a expression) : 'a expr =
    case rmEmpty exp of
    True => T
    | False => F
    | Var e => V e
    | Not e => !!(beautify e)
    | Imp (e1, e2) => beautify e1 ==> beautify e2
    | And l => List.foldl (fn (x, y) => ( y /\ beautify(x) ) ) (beautify (hd l)) (tl l)
    | Or l => List.foldl (fn (x, y) => ( y \/ beautify(x) ) ) (beautify (hd l)) (tl l)
    | Eq l => List.foldl (fn (x, y) => y /\ ((beautify(#1 x)) <=> (beautify(#2 x))) ) (beautify(#1 (hd (makePairs l))) <=> beautify(#2 (hd (makePairs l)))) (tl (makePairs l))
    
fun pushNegations(exp : 'a expression) : 'a expression =
    case rmEmpty exp of
    True => True
    | False => False
    | Var e => Var e
    | Not True => Not True
    | Not False => Not False
    | Not (Var e) => Not (Var e)
    | Not (Not e) => e
    | Not (Imp (e1, e2)) => And [pushNegations e1, pushNegations (Not e2)]
    | Not (And l) => Or (List.map (fn x => pushNegations (Not x)) l)
    | Not (Or l) => And (List.map (fn x => pushNegations (Not x)) l)
    | Not (Eq l) => And [Or (List.map (fn x => pushNegations (Not x)) l), Or (List.map (fn x => pushNegations (x)) l)]
    | And l => And (map pushNegations l)
    | Or l => Or (map pushNegations l)
    | Eq l => Eq (map pushNegations l)

fun isSimple(exp : 'a expression) : bool =
    case exp of
    True => false
    | False => false
    | Not True => false
    | Not False => false
    | Var e => true
    | Not (Var e) => true
    | Not e => false
    | Imp (e1, e2) => false
    | And l => if List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l) then true else false
    | Or l => if List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l) then true else false
    | Eq l => if List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l) then true else false
    
fun rmConstants(exp : ''a expression) : ''a expression =
    case rmEmpty exp of
    True => True
    | False => False
    | Not True => False
    | Not False => True
    | Var e => Var e
    | Not (Var e) => Not (Var e)
    | Not (Not e) => rmConstants e
    | Not e => if isSimple(e) then Not e else rmConstants (Not (rmConstants e))
    | And l => if List.exists (fn x => x = False) l then False 
               else if List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l) then And l
               else rmConstants (And (map (fn x => rmConstants x) (List.filter (fn x => not (x = True)) l)))
    | Or l => if List.exists (fn x => x = True) l then True
              else if List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l) then Or l
              else rmConstants (Or (map (fn x => rmConstants x) (List.filter (fn x => not (x = False)) l)))
    | Imp (e, False) => rmConstants (Not e)
    | Imp (e, True) => True
    | Imp (False, e) => True
    | Imp (True, e) => rmConstants e
    | Imp (e1, e2) => Imp (rmConstants e1, rmConstants e2)
    | Eq l => if List.exists (fn x => x = True) l then rmConstants (And (List.filter (fn x => not (x = True)) l))
              else if List.exists (fn x => x = False) l then rmConstants (And (map (fn x => rmConstants (Not x)) (List.filter (fn x => not (x = False)) l)))
              else if List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l) then Eq l
              else Eq (map (fn x => rmConstants x) l)

fun eliminateDuplicates(list : ''a list, acc : ''a list) : ''a list =
    case list of
    [] => rev acc
    | h::t => if List.exists(fn x => x = h) acc
              then eliminateDuplicates(t, acc)
              else eliminateDuplicates(t, h::acc)
    
fun rmVars (exp : ''a expression) : ''a expression =
    case rmEmpty exp of
    True => True
    | False => False
    | Var e => Var e
    | Not True => False
    | Not False => True
    | Not (Var e) => Not (Var e)
    | Not e => Not (rmVars e)
    | Imp (e1, e2) => if rmVars e1 = rmVars e2 then True else Imp(rmVars e1, rmVars e2)
    | And l => rmEmpty (And (eliminateDuplicates (map rmVars l, [])))
    | Or l => rmEmpty (Or (eliminateDuplicates (map rmVars l, [])))
    | Eq l => rmEmpty (Eq (eliminateDuplicates (map rmVars l, [])))

fun simplify  (exp : ''a expression) : ''a expression =
    rmVars(pushNegations(rmConstants (rmEmpty exp)))

fun toWolframLang f exp : string=
let
    fun removeLastChar(str : string) : string =
        implode (rev (List.drop (rev (explode str), 2)))
in
    case exp of
    True => "True"
    | False => "False"
    | Not False => "True"
    | Not True => "False"
    | Var e => "Var[\"" ^ f(e) ^ "\"]"
    | Not e => "Not[" ^ (toWolframLang f e) ^ "]"
    | Imp (e1, e2) => "Implies[" ^ (toWolframLang f e1) ^ ", " ^ (toWolframLang f e2) ^ "]"
    | And [] => "And[]"
    | And l =>"And[" ^ removeLastChar (List.foldr (fn (acc, x) => acc ^ ", " ^ x) "" (List.map (fn (x) => toWolframLang f x)  l)) ^ "]"
    | Or [] => "Or[]"
    | Or l =>"Or[" ^ removeLastChar (List.foldr (fn (acc, x) => acc ^ ", " ^ x) "" (List.map (fn (x) => toWolframLang f x)  l)) ^ "]"
    | Eq [] => "Equivalent[]"
    | Eq l =>"Equivalent[" ^ removeLastChar (List.foldr (fn (acc, x) => acc ^ ", " ^ x) "" (List.map (fn (x) => toWolframLang f x)  l)) ^ "]"
end

fun prTestEq seed exp1 exp2 =
let
    fun get_bools(union, Next(n, f), acc) = 
        case union of
        [] => rev acc
        | h::t => if (int2bool n) then get_bools(t, f(), h::acc) else get_bools(t, f(), acc)

    fun rm_duplicates (list, acc) = 
        case list of
        [] => rev acc
        | h::t => if List.exists (fn x => x = h) acc then rm_duplicates(t, acc) else rm_duplicates(t, h::acc)

    val union = rm_duplicates ((getVars exp1) @ (getVars exp2), [])
    val Next(seed, f) = lcg(seed)
    val vars = get_bools(union, Next(seed, f), [])
in
    (eval vars exp1) = (eval vars exp2)
end

fun to_bin(vars, n) = 
    let 
        fun bools_to_vars(vars, bools, acc) =
            case bools of
            [] => rev acc
            | h::t => if h then bools_to_vars(tl vars, t, (hd vars)::acc) else bools_to_vars(tl vars, t, acc)

        fun to_bin'(n, acc) = 
            case n of
            0 => acc
            | num =>  if num mod 2 = 0 then to_bin'(num div 2, false :: acc) else to_bin'(num div 2, true :: acc)

        val bin = to_bin'(n, [])
    in
        bools_to_vars(vars, List.tabulate((List.length vars) - (List.length bin), fn x => false) @ bin, [])
    end

fun bruteforce exp =
let
   fun bruteforce' (vars, n) =
        if n < 0 then NONE
        else 
            if eval (to_bin(vars, n)) exp then 
                SOME (to_bin(vars, n))
            else
                bruteforce' (vars, n - 1)            
    val vars = getVars exp;
in
    bruteforce' (vars, List.length vars)
end
