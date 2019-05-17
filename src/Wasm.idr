module Wasm

import Data.List
import Data.Fin

%default total
%access public export

-- we currently don't use any other types than i32
data ValueType = I32

data ResultType = None | Some ValueType

record FuncType where
    constructor MkFuncType
    args : List ValueType
    result : ResultType

data Sign = Signed | Unsigned

data Value : ValueType -> Type where
    ValueI32 : Integer -> Value I32

data IntBinaryOp
    = AddInt
    | SubInt
    | MulInt
    | DivInt Sign
    | RemInt Sign

data IntTestOp = Eqz

data IntRelOp = EqInt | NeInt | LtInt Sign | GtInt Sign | LeInt Sign | GeInt Sign

record CodeCtx where
    constructor MkCodeCtx
    functions : List FuncType
    locals : List ValueType

record FunctionCtx where
    constructor MkFunctionCtx
    functions : List FuncType

FuncIdx : Type
FuncIdx = Nat

LocalIdx : Type
LocalIdx = Nat

data HasFunc : CodeCtx -> FuncIdx -> FuncType -> Type where
    HasFuncHere : HasFunc (MkCodeCtx (f :: _) ls) 0 f
    HasFuncThere :
        HasFunc (MkCodeCtx fs ls) idx f
        -> HasFunc (MkCodeCtx (_ :: fs) ls) (S idx) f

data HasLocal : CodeCtx -> LocalIdx -> ValueType -> Type where
    HasLocalHere : HasLocal (MkCodeCtx fs (l :: _)) 0 l
    HasLocalThere :
        HasLocal (MkCodeCtx fs ls) idx l
        -> HasLocal (MkCodeCtx fs (_ :: ls)) (S idx) l

mutual
    data CallParams : CodeCtx -> List ValueType -> Type where
        ParamsNil : CallParams ctx []
        ParamsCons : Instr ctx (Some t) -> CallParams ctx ts -> CallParams ctx (t :: ts)

    data Instr : CodeCtx -> ResultType -> Type where
        Drop : Instr ctx (Some ty) -> Instr ctx None
        Const : Value ty -> Instr ctx (Some ty)
        Binop : IntBinaryOp -> Instr ctx (Some ty) -> Instr ctx (Some ty) -> Instr ctx (Some ty)
        Testop : IntTestOp -> Instr ctx (Some ty) -> Instr ctx (Some I32)
        Relop : IntRelOp -> Instr ctx (Some ty) -> Instr ctx (Some ty) -> Instr ctx (Some I32)
        LocalGet : (idx : LocalIdx) -> {prf : HasLocal ctx idx ty} -> Instr ctx (Some ty)
        LocalSet : (idx : LocalIdx) -> {prf : HasLocal ctx idx ty} -> Instr ctx (Some ty) -> Instr ctx None
        -- module always has one mutable i32 global
        GlobalGet : Instr ctx (Some I32)
        GlobalSet : Instr ctx (Some I32) -> Instr ctx None
        -- only stores and loads for i32, and memarg is always {offset: 0, align: 4}
        Load : Instr ctx (Some I32) -> Instr ctx (Some I32)
        Store : (val : Instr ctx (Some I32)) -> (addr : Instr ctx (Some I32)) -> Instr ctx None
        MemorySize : Instr ctx (Some I32)
        MemoryGrow : Instr ctx (Some I32) -> Instr ctx (Some I32)
        Unreachable : Instr ctx ty
        If : (ty : ResultType) -> Instr ctx (Some I32) -> Instr ctx ty -> Instr ctx ty -> Instr ctx ty
        Call : (idx : FuncIdx) -> {v : HasFunc ctx idx f} -> (CallParams ctx (args f)) -> Instr ctx (result f)
        -- all virtual calls must have type [i32, i32] -> [i32]
        CallIndirect : (fn : Instr ctx (Some I32)) -> Instr ctx (Some I32) -> Instr ctx (Some I32) -> Instr ctx (Some I32)
        Chain : Instr ctx None -> Instr ctx ty -> Instr ctx ty
        -- represents a sequence of zero instructions
        Empty : Instr ctx None

codeCtx : FunctionCtx -> List ValueType -> CodeCtx
codeCtx fnCtx locals = MkCodeCtx (functions fnCtx) locals

record Function (ctx : FunctionCtx) (ty : FuncType) where
    constructor MkFunction
    locals : List ValueType
    body : Instr (codeCtx ctx (args ty ++ locals)) (result ty)

data Functions : FunctionCtx -> List FuncType -> Type where
    FunctionsNil : Functions ctx []
    FunctionsCons : Function ctx t -> Functions ctx ts -> Functions ctx (t :: ts)

-- module implicitly contains:
-- * type at index 0 for virtual calls: [i32, i32] -> [i32]
-- * single memory with initial size of 0 and unlimited maximum
-- * single mutable i32 global
-- * exports the last function and names it main

record Module where
    constructor MkModule
    decls : List FuncType
    functions : Functions (MkFunctionCtx decls) decls
    table : List (Fin (length decls))
    main : Fin (length decls)
