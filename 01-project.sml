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