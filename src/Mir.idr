module Mir

import Data.Fin
import Data.List

%default total
%access public export

data ValueType = Obj | Num

data Op = Add | Sub | Mul | Div | Rem | Eq | Ne | Lt | Le | Gt | Ge

data MExp : ValueType -> Nat -> Type where
    Const : Integer -> MExp Num locals
    Local : Fin locals -> MExp Obj locals
    Let : MExp Obj locals -> MExp ty (S locals) -> MExp ty locals
    Create : MExp Num locals -> List (MExp Obj locals) -> MExp Obj locals
    Field : MExp Obj locals -> MExp Num locals -> MExp Obj locals
    Tag : MExp Obj locals -> MExp Num locals
    If : MExp Num locals -> MExp ty locals -> MExp ty locals -> MExp ty locals
    Call : Nat -> List (MExp Obj locals) -> MExp Obj locals
    CallVirt : MExp Num locals -> MExp Obj locals -> MExp Obj locals -> MExp Obj locals
    Binop : Op -> MExp Num locals -> MExp Num locals -> MExp Num locals

record MDef where
    constructor MkMDef
    args : Nat
    body : MExp Obj args

record Module where
    constructor MkModule
    defs : List MDef
    main : Fin (length defs)
