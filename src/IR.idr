module IR

import Data.List
import Data.Vect
import Common

%default total
%access public export

LocalName : Type
LocalName = Nat

FuncName : Type
FuncName = Nat

GlobalName : Type
GlobalName = Nat

mutual
    data IExp : List LocalName -> Type where
        ILocal : Elem x vars -> IExp vars
        IGlobal : GlobalName -> IExp vars
        ICall : FuncName -> List (IExp vars) -> IExp vars
        ICallClosure : IExp vars -> IExp vars -> IExp vars
        ILet : (x : LocalName) -> IExp vars -> IExp (x :: vars) -> IExp vars
        ILambda : (f : FuncName) -> IExp vars -> IExp vars
        ICon : (tag : Int) -> List (IExp vars) -> IExp vars
        IOp : PrimFn arity -> Vect arity (IExp vars) -> IExp vars
        IConCase : (sc : IExp vars) -> List (IConAlt vars) -> Maybe (IExp vars) -> IExp vars
        IConstCase : (sc : IExp vars) -> List (IConstAlt vars) -> Maybe (IExp vars) -> IExp vars
        IConst : Constant -> IExp vars
        ICrash : String -> IExp vars

    data IConAlt : List LocalName -> Type where
        MkConAlt : (tag : Int) -> (args : List LocalName) -> IExp (args ++ vars) -> IConAlt vars

    data IConstAlt : List LocalName -> Type where
        MkConstAlt : Constant -> IExp vars -> IConstAlt vars

record IDef where
    constructor MkDef
    exported : Bool
    name : String
    args : List LocalName
    body : IExp args
