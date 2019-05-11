module MIR

import Data.Fin

%default total
%access public export

data Value = ValueInt Integer | ValueStr String | ValueChar Char

data ExpType = Object | Number

data MExp : ExpType -> Nat -> MExp where
    Const : Int -> ExpType Number locals
    Local : Fin locals -> MExp Object locals
    Let : MExp Object locals -> MExp Object (S locals)
    Create : MExp Number locals -> List Object (MExp locals) -> MExp Object locals
    Field : MExp Object locals -> MExp Number locals -> MExp Object locals
    Tag : MExp Object locals -> MExp Number locals
    If : MExp Number locals -> MExp ty locals -> MExp ty locals -> MExp ty locals
    Call : MExp Number locals -> List (MExp Object locals) -> MExp Object locals

record MDef where
    constructor MkMDef
    args : Nat
    body : MExp args


