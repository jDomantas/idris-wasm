module TSExp

import Data.List
import Data.Vect
import Data.Fin

%default total
%access public export

data TSConst 
    = I Integer
    | WorldVal
    | IntegerType
    | WorldType

data PrimFn : Nat -> Type where
    Add : PrimFn 2
    Sub : PrimFn 2
    Mul : PrimFn 2
    Div : PrimFn 2
    Mod : PrimFn 2
    Neg : PrimFn 1
    LT : PrimFn 2
    LTE : PrimFn 2
    EQ : PrimFn 2
    GTE : PrimFn 2
    GT : PrimFn 2

mutual
    data TSExp : (vars : Nat) -> Type where
        Local : Fin vars -> TSExp vars
        Global : Nat -> TSExp vars
        Lam : TSExp (S vars) -> TSExp vars
        Let : TSExp vars -> TSExp (S vars) -> TSExp vars
        Apply : TSExp vars -> List (TSExp vars) -> TSExp vars
        Construct : (tag : Int) -> List (TSExp vars) -> TSExp vars
        Op : PrimFn arity -> Vect arity (TSExp vars) -> TSExp vars
        Force : TSExp vars -> TSExp vars
        Delay : TSExp vars -> TSExp vars
        Case : (sc : TSExp vars) -> List (Branch vars) -> Maybe (TSExp vars) -> TSExp vars
        ConstCase : (sc : TSExp vars) -> List (ConstBranch vars) -> Maybe (TSExp vars) -> TSExp vars
        Const : TSConst -> TSExp vars
        Erased : TSExp vars
        Crash : String -> TSExp vars

    record Branch (vars : Nat) where
        constructor MkBranch
        tag : Int
        args : Nat
        value : TSExp (args + vars)

    record ConstBranch (vars : Nat) where
        constructor MkConstBranch
        tag : Int
        value : TSExp vars

data TSDef : Type where
    Function : (args : Nat) -> TSExp args -> TSDef
    Constructor : (tag : Int) -> (arity : Nat) -> TSDef

record Module where
    constructor MkModule
    defs : List TSDef
    main : Fin (length defs)

Show TSConst where
    show (I x) = show x
    show WorldVal = "%world"
    show IntegerType = "%intTy"
    show WorldType = "%worldTy"

Show (PrimFn arity) where
    show Add = "add"
    show Sub = "sub"
    show Mul = "mul"
    show Div = "div"
    show Mod = "mod"
    show Neg = "neg"
    show LT = "lt"
    show LTE = "lte"
    show EQ = "eq"
    show GTE = "gte"
    show GT = "gt"

mutual
    partial
    showArgs : List (TSExp vars) -> String
    showArgs [] = ")"
    showArgs (x :: xs) = " " ++ show x ++ showArgs xs

    partial
    showArgsv : Vect x (TSExp vars) -> String
    showArgsv [] = ")"
    showArgsv (x :: xs) = " " ++ show x ++ showArgsv xs

    partial
    showList : Show a => List a -> String
    showList [] = ""
    showList (x :: xs) = " " ++ show x ++ showList xs

    partial
    Show (TSExp vars) where
        show (Local idx) = "local_" ++ show (finToNat idx)
        show (Global idx) = "global_" ++ show idx
        show (Lam body) = "(lambda " ++ show body ++ ")"
        show (Let val rest) = "(let " ++ show val ++ " " ++ show rest ++ ")"
        show (Apply f args) = "(call " ++ show f ++ showArgs args
        show (Construct tag args) = "(construct " ++ show tag ++ showArgs args
        show (Op op args) = "(op " ++ show op ++ showArgsv args
        show (Force exp) = "(force " ++ show exp ++ ")"
        show (Delay exp) = "(delay " ++ show exp ++ ")"
        show (Case sc alt Nothing) = "(match " ++ show sc ++ showList alt ++ ")"
        show (Case sc alt (Just def)) = "(match " ++ show sc ++ showList alt ++ " (default " ++ show def ++ "))"
        show (ConstCase sc alt Nothing) = "(cmatch " ++ show sc ++ showList alt ++ ")"
        show (ConstCase sc alt (Just def)) = "(cmatch " ++ show sc ++ showList alt ++ " (default " ++ show def ++ "))"
        show (Const c) = show c
        show Erased = "%erased"
        show (Crash msg) = "(crash \"" ++ msg ++ "\")"

    partial
    Show (Branch vars) where
        show (MkBranch tag args val) = "(case " ++ show tag ++ " (fields " ++ show args ++ ") " ++ show val ++ ")"

    partial
    Show (ConstBranch vars) where
        show (MkConstBranch tag val) = "(case " ++ show tag ++ " " ++ show val ++ ")"

partial
Show TSDef where
    show (Function args body) = "(function (args " ++ show args ++ ") " ++ show body ++ ")"
    show (Constructor tag arity) = "(constructor (tag " ++ show tag ++ ") (arity " ++ show arity ++ "))"

partial
showDefs : Nat -> List TSDef -> String
showDefs idx [] = ""
showDefs idx (d :: ds) = "global_" ++ show idx ++ " = " ++ show d ++ "\n" ++ showDefs (S idx) ds

partial
Show Module where
    show (MkModule defs main) = showDefs Z defs ++ "main = global_" ++ show (finToNat main)
