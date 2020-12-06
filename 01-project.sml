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
exception NotAVar;

Control.Print.printDepth := 100;
Control.Print.printLength := 1000;
Control.Print.stringDepth := 1000;

fun bitNeg exp =
    case exp of
    True => False
    | False => True

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
    | And l => And (List.map (fn x => (rmEmpty x)) l)
    | Or l => Or (List.map (fn x => (rmEmpty x)) l)
    | Eq l => Eq (List.map (fn x => (rmEmpty x)) l)
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
    | Not (Not e) => pushNegations e
    | Not (Imp (e1, e2)) => And [pushNegations e1, pushNegations (Not e2)]
    | Not (And l) => Or (List.map (fn x => pushNegations (Not x)) l)
    | Not (Or l) => And (List.map (fn x => pushNegations (Not x)) l)
    | Not (Eq l) => And [Or (List.map (fn x => pushNegations (Not x)) l), Or (List.map (fn x => pushNegations (x)) l)]
    | Imp (e1, e2) => Imp(pushNegations(e1), pushNegations(e2))
    | And l => And (List.map (fn x => pushNegations x) l)
    | Or l => Or (List.map (fn x => pushNegations x) l)
    | Eq l => Eq (List.map (fn x => pushNegations x) l)

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
    | And l => List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l)
    | Or l => List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l)
    | Eq l => List.foldl (fn (acc, x) => acc andalso x) true (map isSimple l)
    
fun rmConstants(exp : ''a expression) : ''a expression =
    case rmEmpty exp of
    True => True
    | False => False
    | Not True => False
    | Not False => True
    | Var e => Var e
    | Not (Var e) => Not (Var e)
    | Not (Not e) => rmConstants e
    | Not e => Not (rmConstants e)
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
    | Not e => Not (rmVars e)
    | Imp (e1, e2) => if rmVars e1 = rmVars e2 then True else Imp(rmVars e1, rmVars e2)
    | And l => rmEmpty (And (eliminateDuplicates (List.map rmVars l, [])))
    | Or l => rmEmpty (Or (eliminateDuplicates (List.map rmVars l, [])))
    | Eq l => rmEmpty (Eq (eliminateDuplicates (List.map rmVars l, [])))

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

fun isCNF exp =
let 
    fun isVarList exp =
        case exp of
        And [] => true
        | Or [] => true
        | And(True::t) => true andalso isVarList (And t)
        | Or(True::t) => true andalso isVarList (Or t)
        | And(False::t) => true andalso isVarList (And t)
        | Or(False::t) => true andalso isVarList (Or t)
        | And(Var e::t) => true andalso isVarList (And t)
        | Or(Var e::t) => true andalso isVarList (Or t)
        | And(Not(Var e)::t) => true andalso isVarList (And t)
        | Or(Not(Var e)::t) => true andalso isVarList (Or t)
        | And((Or l)::t) => true andalso isVarList(Or l) andalso isVarList(And t)
        | _ => false
in
    case exp of 
    True => true
    | False => true
    | Var e => true
    | Not (Var e) => true
    | And l => isVarList(And l)
    | Or l => isVarList(Or l)
    | _ => false
end

fun getIsolatedVars exp =
let
    fun getIsolatedVarsList exp_l =
        case exp_l of
        [] => []
        | h::t => checkCombine(getIsolatedVars h, getIsolatedVarsList t)
in
    case exp of
    Var i => [Var i]
    | Not (Var i) => [Not (Var i)]
    | Or [Var i] => [Or [Var i]]
    | Or [Not (Var i)] => [Or [Not (Var i)]]
    | And l => (getIsolatedVarsList l)
    | _ => []
end

fun replaceWith (exp, e, r) = 
let
    fun replaceWithList (l, e, r) =
        case l of
        [] => []
        | h::t => replaceWith (h, e, r) :: replaceWithList (t, e, r)
in
    case exp of
    True => True
    | False => False
    | Var i => if (Var i) = e orelse Or [Var i] = e then r else if Not (Var i) = e orelse Or [Not (Var i)] = e then (bitNeg r) else Var i
    | Not (Var i) => if Not (Var i) = e then r else if (Var i) = e then (bitNeg r) else Not (Var i)
    | Not i => Not (replaceWith(i, e, r))
    | Imp (e1, e2) => Imp (replaceWith (e1, e, r), replaceWith (e2, e, r))
    | Or [Var i] => if Or [Var i] = e then r else Or [Var i]
    | Or [Not (Var i)] => if Or [Not (Var i)] = e then r else Or [Not (Var i)]
    | Or l => Or (replaceWithList(l, e, r))
    | And l => And (replaceWithList(l, e, r))
    | Eq l => Eq (replaceWithList(l, e, r))
end

fun replaceAllWith (exp, l, r) =
    case l of
    [] => exp
    | h::t => replaceAllWith(replaceWith (exp, h, r), t, r)

fun removeVars (exp, vars, removed) =
    case vars of
    [] => rev removed
    | Or[Var i]::t => removeVars(replaceWith (exp, Or[Var i], True), t, i::removed)
    | (Var i)::t => removeVars(replaceWith (exp, (Var i), True), t, i::removed)
    | Or[Not (Var i)]::t => removeVars(replaceWith (exp, Or[Not (Var i)], True), t, removed)
    | Not (Var i)::t => removeVars(replaceWith (exp, Not (Var i), True), t, removed)

fun step1 (exp, acc) =
let
    val vars = getIsolatedVars exp
    val removedVars = removeVars (exp, vars, [])
    val exp' = replaceAllWith (exp, vars, True)
in
    case vars of
    [] => (exp', acc @ removedVars)
    | l => step1(rmConstants exp', acc @ removedVars)
end

fun step3 (exp, vars, trues) =
let
    val withTrue = rmConstants (replaceWith(exp, Var (hd vars), True))
    val withFalse = rmConstants (replaceWith(exp, Var (hd vars), False))
in
    if withTrue = True
    then SOME (trues @ [(hd vars)])
    else if withFalse = True
    then SOME trues
    else
        if null (tl vars) 
        then NONE
        else
        let
            val withTrueRec = step3(withTrue, tl vars, trues @ [(hd vars)])
            val withFalseRec = step3(withFalse, tl vars, trues)
        in
            
            if not (withTrueRec = NONE)
            then withTrueRec
            else 
                withFalseRec
        end
end

fun dpll exp=
let
    val (exp', vars) = step1(exp, [])
in
    if exp' = True then (* Step 2 *)
        SOME vars
    else if exp' = False then (* Step 2 *)
        NONE
    else
        step3(exp', getVars exp', vars)
end 

fun satSolver exp =
let
    fun containsEmpty (And l) =
        case l of
        [] => false
        | h::t => if h = (Or[]) then true else containsEmpty(And t)
in
    if isCNF exp then

        if exp = True orelse (exp = And[]) then
            SOME []
        else if exp = False orelse (containsEmpty exp) then
            NONE
        else 
            dpll exp
    else
        raise InvalidCNF
end

fun toBin(vars, n) = 
    let 
        fun boolsToVars(vars, bools, acc) =
            case bools of
            [] => rev acc
            | h::t => if h then boolsToVars(tl vars, t, (hd vars)::acc) else boolsToVars(tl vars, t, acc)

        fun toBin'(n, acc) = 
            case n of
            0 => acc
            | num =>  if num mod 2 = 0 then toBin'(num div 2, false :: acc) else toBin'(num div 2, true :: acc)

        val bin = toBin'(n, [])
    in
        boolsToVars(vars, List.tabulate((List.length vars) - (List.length bin), fn x => false) @ bin, [])
    end

fun bruteforce exp =
let
   fun bruteforce' (vars, n) =
        if n < 0 then NONE
        else 
            if eval (toBin(vars, n)) exp then 
                SOME (toBin(vars, n))
            else
                bruteforce' (vars, n - 1)            
    val vars = getVars exp;
in
    bruteforce' (vars, List.length vars)
end

type timetable = {day : string, time: int, course: string} list
type student = {studentID : int, curriculum : string list}

fun problemReduction _ _ _ = raise NotImplemented;

fun solutionRepresentation _ = raise NotImplemented;