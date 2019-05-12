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
    -- `types` only list types available for call_indirect. When we emit, we
    -- append function types to the end, and emit function declarations that
    -- refer to those appended types.
    functions : List FuncType
    types : List FuncType
    locals : List ValueType
    return : ResultType

record FunctionCtx where
    constructor MkFunctionCtx
    functions : List FuncType
    types : List FuncType

FuncIdx : Type
FuncIdx = Nat

TypeIdx : Type
TypeIdx = Nat

LocalIdx : Type
LocalIdx = Nat

data HasFunc : CodeCtx -> FuncIdx -> FuncType -> Type where
    HasFuncHere : HasFunc (MkCodeCtx (f :: _) ts ls ret) 0 f
    HasFuncThere :
        HasFunc (MkCodeCtx fs ts ls ret) idx f
        -> HasFunc (MkCodeCtx (_ :: fs) ts ls ret) (S idx) f

data HasType : CodeCtx -> TypeIdx -> FuncType -> Type where
    HasTypeHere : HasType (MkCodeCtx fs (t :: _) ls ret) 0 t
    HasTypeThere :
        HasType (MkCodeCtx fs ts ls ret) idx t
        -> HasType (MkCodeCtx fs (_ :: ts) ls ret) (S idx) t

data HasLocal : CodeCtx -> LocalIdx -> ValueType -> Type where
    HasLocalHere : HasLocal (MkCodeCtx fs ts (l :: _) ret) 0 l
    HasLocalThere :
        HasLocal (MkCodeCtx fs ts ls ret) idx l
        -> HasLocal (MkCodeCtx fs ts (_ :: ls) ret) (S idx) l

data HasReturn : CodeCtx -> ResultType -> Type where
    HasReturnCtx : HasReturn (MkCodeCtx fs ts ls ret) ret        

mutual
    data CallParams : CodeCtx -> List ValueType -> Type where
        ParamsNil : CallParams ctx []
        ParamsCons : Instr ctx (Some t) -> CallParams ctx ts -> CallParams ctx (t :: ts)

    data Instr : CodeCtx -> ResultType -> Type where
        Const : Value ty -> Instr ctx (Some ty)
        Binop : IntBinaryOp -> Instr ctx (Some ty) -> Instr ctx (Some ty) -> Instr ctx (Some ty)
        Testop : IntTestOp -> Instr ctx (Some ty) -> Instr ctx (Some I32)
        Relop : IntRelOp -> Instr ctx (Some ty) -> Instr ctx (Some ty) -> Instr ctx (Some I32)
        LocalGet : (idx : LocalIdx) -> {v : HasLocal ctx idx ty} -> Instr ctx (Some ty)
        LocalSet : (idx : LocalIdx) -> {v : HasLocal ctx idx ty} -> Instr ctx (Some ty) -> Instr ctx None
        LocalTee : (idx : LocalIdx) -> {v : HasLocal ctx idx ty} -> Instr ctx (Some ty) -> Instr ctx (Some ty)
        -- module always has one mutable i32 global
        GlobalGet : Instr ctx (Some I32)
        GlobalSet : Instr ctx (Some I32) -> Instr ctx None
        -- only stores and loads for i32, and memarg is always {offset: 0, align: 4}
        Load : Instr ctx (Some I32) -> Instr ctx (Some I32)
        Store : Instr ctx (Some I32) -> Instr ctx (Some I32) -> Instr ctx None
        MemorySize : Instr ctx (Some I32)
        MemoryGrow : Instr ctx (Some I32) -> Instr ctx (Some I32)
        Unreachable : Instr ctx ty
        If : (ty : ResultType) -> Expr ctx ty -> Expr ctx ty -> Instr ctx ty
        Return : {v : HasReturn ctx ty} -> Instr ctx ty -> Instr ctx anyTy
        Call : (idx : FuncIdx) -> {v : HasFunc ctx idx f} -> (CallParams ctx (args f)) -> Instr ctx (result f)
        CallIndirect : (idx : TypeIdx) -> {v : HasType ctx idx f} -> (CallParams ctx (args f)) -> Instr ctx (Some I32) -> Instr ctx (result f)
        Chain : Instr ctx None -> Instr ctx ty -> Instr ctx ty

    data Expr : CodeCtx -> ResultType -> Type where
        ExprEmpty : Expr ctx None
        ExprReturn : Instr ctx ty -> Expr ctx ty
        ExprChain : Instr ctx None -> Expr ctx ty -> Expr ctx ty

codeCtx : FunctionCtx -> ResultType -> List ValueType -> CodeCtx
codeCtx fnCtx returnTy locals = MkCodeCtx (functions fnCtx) (types fnCtx) locals returnTy

record Function (ctx : FunctionCtx) (ty : FuncType) where
    constructor MkFunction
    locals : List ValueType
    body : Expr (codeCtx ctx (result ty) (args ty ++ locals)) (result ty)

data Functions : FunctionCtx -> List FuncType -> Type where
    FunctionsNil : Functions ctx []
    FunctionsCons : Function ctx t -> Functions ctx ts -> Functions ctx (t :: ts)

-- module implicitly contains:
-- * single memory with initial size of 0 and unlimited maximum
-- * single mutable i32 global
-- * exports the last function and names it main

record Module where
    constructor MkModule
    decls : List FuncType
    types : List FuncType
    functions : Functions (MkFunctionCtx decls types) decls
    table : List (Fin (length decls))
