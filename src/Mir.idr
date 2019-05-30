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
    Crash : MExp ty locals

record MDef where
    constructor MkMDef
    args : Nat
    body : MExp Obj args

record Module where
    constructor MkModule
    defs : List MDef
    main : Fin (length defs)

Show Op where
    show Add = "+"
    show Sub = "-"
    show Mul = "*"
    show Div = "/"
    show Rem = "%"
    show Eq = "=="
    show Ne = "!="
    show Lt = "<"
    show Le = "<="
    show Gt = ">"
    show Ge = ">="

mutual
    partial
    showList : Show a => List a -> String
    showList [] = ""
    showList (x :: xs) = " " ++ show x ++ showList xs

    partial
    Show (MExp ty vars) where
        show (Const x) = show x
        show (Local idx) = "local_" ++ show (finToNat idx)
        show (Let ex rest) = "(let " ++ show ex ++ " " ++ show rest ++ ")"
        show (Create tag args) = "(create " ++ show tag ++ showList args ++ ")"
        show (Field obj idx) = "(field " ++ show idx ++ " " ++ show obj ++ ")"
        show (Tag obj) = "(tag " ++ show obj ++ ")"
        show (If c t e) = "(if " ++ show c ++ " " ++ show t ++ " " ++ show e ++ ")"
        show (Call idx args) = "(call global_" ++ show idx ++ showList args ++ ")"
        show (CallVirt idx a b) = "(callvirt " ++ show idx ++ " " ++ show a ++ " " ++ show b ++ ")"
        show (Binop op a b) = "(" ++ show a ++ " " ++ show op ++ " " ++ show b ++ ")"
        show Crash = "crash"

partial
Show MDef where
    show (MkMDef args body) = "(function (args " ++ show args ++ ") " ++ show body ++ ")"

partial
showDefs : Nat -> List MDef -> String
showDefs idx [] = ""
showDefs idx (d :: ds) = "global_" ++ show idx ++ " = " ++ show d ++ "\n" ++ showDefs (S idx) ds

partial
Show Module where
    show (MkModule defs main) = showDefs Z defs ++ "main = global_" ++ show (finToNat main)
