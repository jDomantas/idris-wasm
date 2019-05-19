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
