module Wasm

import Data.List

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
    ValueI32 : Nat -> Value I32

data IntBinaryOp
    = AddInt
    | SubInt
    | MulInt
    | DivInt Sign
    | RemInt Sign

data IntTestOp = Eqz

data IntRelOp = EqInt | NeInt | LtInt Sign | GtInt Sign | LeInt Sign | GeInt Sign

data Mutability = Immutable | Mutable

record Global where
    constructor MkGlobal
    mutability : Mutability
    type : ValueType

record CodeCtx where
    constructor MkCodeCtx
    globals : List Global
    -- `types` only list types available for call_indirect. When we emit, we
    -- append function types to the end, and emit function declarations that
    -- refer to those appended types.
    functions : List FuncType
    types : List FuncType
    locals : List ValueType
    labels : List ResultType
    return : ResultType

record FunctionCtx where
    constructor MkFunctionCtx
    globals : List Global
    functions : List FuncType
    types : List FuncType

withLabel : ResultType -> CodeCtx -> CodeCtx
withLabel ty (MkCodeCtx gs fs ts ls lbs ret) = MkCodeCtx gs fs ts ls (ty :: lbs) ret

GlobalIdx : Type
GlobalIdx = Nat

FuncIdx : Type
FuncIdx = Nat

TypeIdx : Type
TypeIdx = Nat

LocalIdx : Type
LocalIdx = Nat

LabelIdx : Type
LabelIdx = Nat

data HasGlobal : CodeCtx -> GlobalIdx -> Global -> Type where
    HasGlobalHere : HasGlobal (MkCodeCtx (g :: _) ts fs ls lbs ret) 0 g
    HasGlobalThere :
        HasGlobal (MkCodeCtx gs fs ts ls lbs ret) idx g
        -> HasGlobal (MkCodeCtx (_ :: gs) fs ts ls lbs ret) (S idx) g

data HasFunc : CodeCtx -> FuncIdx -> FuncType -> Type where
    HasFuncHere : HasFunc (MkCodeCtx gs (f :: _) ts ls lbs ret) 0 f
    HasFuncThere :
        HasFunc (MkCodeCtx gs fs ts ls lbs ret) idx f
        -> HasFunc (MkCodeCtx gs (_ :: fs) ts ls lbs ret) (S idx) f

data HasType : CodeCtx -> TypeIdx -> FuncType -> Type where
    HasTypeHere : HasType (MkCodeCtx gs fs (t :: _) ls lbs ret) 0 t
    HasTypeThere :
        HasType (MkCodeCtx gs fs ts ls lbs ret) idx t
        -> HasType (MkCodeCtx gs fs (_ :: ts) ls lbs ret) (S idx) t

data HasLocal : CodeCtx -> LocalIdx -> ValueType -> Type where
    HasLocalHere : HasLocal (MkCodeCtx gs fs ts (l :: _) lbs ret) 0 l
    HasLocalThere :
        HasLocal (MkCodeCtx gs fs ts ls lbs ret) idx l
        -> HasLocal (MkCodeCtx gs fs ts (_ :: ls) lbs ret) (S idx) l

data HasLabel : CodeCtx -> LabelIdx -> ResultType -> Type where
    HasLabelHere : HasLabel (MkCodeCtx gs fs ts ls (l :: _) ret) 0 l
    HasLabelThere :
        HasLabel (MkCodeCtx gs fs ts ls lbs ret) idx l
        -> HasLabel (MkCodeCtx gs fs ts ls (_ :: lbs) ret) (S idx) l

data HasReturn : CodeCtx -> ResultType -> Type where
    HasReturnCtx : HasReturn (MkCodeCtx gs fs ts ls lbs ret) ret        

    
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
        GlobalGet : (idx : GlobalIdx) -> {v : HasGlobal ctx idx (MkGlobal mut ty)} -> Instr ctx (Some ty)
        GlobalSet : (idx : GlobalIdx) -> {v : HasGlobal ctx idx (MkGlobal Mutable ty)} -> Instr ctx (Some ty) -> Instr ctx None
        -- only stores and loads for i32, and memarg is always {offset: 0, align: 4}
        Load : Instr ctx (Some I32) -> Instr ctx (Some I32)
        Store : Instr ctx (Some I32) -> Instr ctx (Some I32) -> Instr ctx None
        MemorySize : Instr ctx (Some I32)
        MemoryGrow : Instr ctx (Some I32) -> Instr ctx (Some I32)
        Unreachable : Instr ctx ty
        Block : (ty : ResultType) -> Expr ctx ty -> Instr (withLabel ty ctx) ty
        Loop : (ty : ResultType) -> Expr ctx ty -> Instr (withLabel ty ctx) ty
        If : (ty : ResultType) -> Expr (withLabel ty ctx) ty -> Expr (withLabel ty ctx) ty -> Instr ctx ty
        Return : {v : HasReturn ctx ty} -> Instr ctx ty -> Instr ctx anyTy
        Call : (idx : FuncIdx) -> {v : HasFunc ctx idx f} -> (CallParams ctx (args f)) -> Instr ctx (result f)
        CallIndirect : (idx : TypeIdx) -> {v : HasType ctx idx f} -> (CallParams ctx (args f)) -> Instr ctx (Some I32) -> Instr ctx (result f)

    data Expr : CodeCtx -> ResultType -> Type where
        ExprEmpty : Expr ctx None
        ExprReturn : Instr ctx ty -> Expr ctx ty
        ExprChain : Instr ctx None -> Expr ctx ty -> Expr ctx ty

codeCtx : FunctionCtx -> ResultType -> List ValueType -> CodeCtx
codeCtx fnCtx returnTy locals = MkCodeCtx
    (globals fnCtx)
    (functions fnCtx)
    (types fnCtx)
    locals
    []
    returnTy

record Function (ctx : FunctionCtx) (ty : FuncType) where
    constructor MkFunction
    locals : List ValueType
    body : Expr (codeCtx ctx (result ty) locals) (result ty)

moduleFunctions : FunctionCtx -> List FuncType -> Type
moduleFunctions ctx [] = ()
moduleFunctions ctx (f :: fs) = (Function ctx f, moduleFunctions ctx fs)

-- FIXME: tables are missing

record Module where
    constructor MkModule
    globals : List Global
    decls : List FuncType
    types : List FuncType
    functions : moduleFunctions (MkFunctionCtx globals decls types) decls
