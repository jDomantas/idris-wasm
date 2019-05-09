module BExp

import Data.List
import Data.Vect
import Common

%default total
%access public export

Name : Type
Name = Unit

mutual
    data BExp : List Name -> Type where
        BLocal : Elem x vars -> BExp vars
        BGlobal : Nat -> BExp vars
        -- Lambda expression
        BLam : (x : Name) -> BExp (x :: vars) -> BExp vars
        -- Let bindings
        BLet : (x : Name) -> BExp vars -> BExp (x :: vars) -> BExp vars
        -- Application of a defined function. The length of the argument list is
        -- exactly the same length as expected by its definition (so saturate with
        -- lambdas if necessary, or overapply with additional BApps)
        BApp : BExp vars -> List (BExp vars) -> BExp vars
        -- A saturated constructor application
        BCon : (tag : Int) -> List (BExp vars) -> BExp vars
        -- Internally defined primitive operations
        BOp : PrimFn arity -> Vect arity (BExp vars) -> BExp vars
        -- A forced (evaluated) value (TODO: is this right?)
        BForce : BExp vars -> BExp vars
        -- A delayed value (lazy? TODO: check)
        BDelay : BExp vars -> BExp vars
        -- A case match statement
        BConCase : (sc : BExp vars) -> List (BConAlt vars) -> Maybe (BExp vars) -> BExp vars
        BConstCase : (sc : BExp vars) -> List (BConstAlt vars) -> Maybe (BExp vars) -> BExp vars
        -- A primitive value
        BPrimVal : Constant -> BExp vars
        -- An erased value
        BErased : BExp vars
        -- Some sort of crash?
        BCrash : String -> BExp vars

    record BConAlt (vars : List Name) where
        constructor MkConAlt
        tag : Int
        args : List Name
        body : BExp (args ++ vars)

    record BConstAlt (vars : List Name) where
        constructor MkConstAlt
        tag : Constant
        body : BExp vars

record BDef where
    constructor MkDef
    exported : Bool
    name : String
    args : List Name
    body : BExp args
