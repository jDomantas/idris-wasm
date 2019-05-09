module Wasm

import Data.List

%default total
%access public export

data ValueType = I32 | I64 | F32 | F64

data Size = B32 | B64

data ResultType = None | Some ValueType

record FuncType where
    constructor MkFuncType
    args : List ValueType
    result : ResultType

typeSize : ValueType -> Size
typeSize I32 = B32
typeSize I64 = B64
typeSize F32 = B32
typeSize F64 = B64

intTy : Size -> ValueType
intTy B32 = I32
intTy B64 = I64

floatTy : Size -> ValueType
floatTy B32 = F32
floatTy B64 = F64

data Sign = Signed | Unsigned

data IntType : ValueType -> Type where
    Int32 : IntType I32
    Int64 : IntType I64

data FloatType : ValueType -> Type where
    Float32 : FloatType F32
    Float64 : FloatType F64

data Value : ValueType -> Type where
    ValueI32 : Nat -> Value I32
    ValueI64 : Nat -> Value I64
    ValueF32 : Double -> Value F32
    ValueF64 : Double -> Value F64

data IntUnaryOp = Clz | Ctz | Popcnt

data FloatUnaryOp = Abs | Neg | Sqrt | Ceil | Floor | Trunc | Nearest

data IntBinaryOp
    = AddInt
    | SubInt
    | MulInt
    | DivInt Sign
    | RemInt Sign
    | And
    | Or
    | Xor
    | Shl
    | Shr Sign
    | Rotl
    | Rotr

data FloatBinaryOp
    = AddFloat
    | SubFloat
    | MulFloat
    | DivFloat
    | Min
    | Max
    | CopySign

data IntTestOp = Eqz

data IntRelOp = EqInt | NeInt | LtInt Sign | GtInt Sign | LeInt Sign | GeInt Sign

data FloatRelOp = EqFloat | NeFloat | LtFloat | GtFloat | LeFloat | GeFloat

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

data MemArg : Nat -> Type where
    MemAlign1 : Nat -> MemArg 1
    MemAlign2 : Nat -> MemArg 2
    MemAlign4 : Nat -> MemArg 4
    MemAlign8 : Nat -> MemArg 8

memOffset : MemArg align -> Nat
memOffset (MemAlign1 offset) = offset
memOffset (MemAlign2 offset) = offset
memOffset (MemAlign4 offset) = offset
memOffset (MemAlign8 offset) = offset

data LabelTable : CodeCtx -> ResultType -> Type where
    TableEmpty : LabelTable ctx None
    TableSingle : (idx : LabelIdx) -> {v : HasLabel ctx idx ty} -> LabelTable ctx ty
    TableCons : (idx : LabelIdx) -> {v : HasLabel ctx idx ty} -> LabelTable ctx ty -> LabelTable ctx ty

mutual
    callParams : (ctx : CodeCtx) -> List ValueType -> Type
    callParams _ [] = Unit
    callParams ctx (p :: ps) = (Instr ctx (Some p), callParams ctx ps)

    data Instr : CodeCtx -> ResultType -> Type where
        Const : Value ty -> Instr ctx (Some ty)
        IUnop : {t : IntType ty} -> IntUnaryOp -> Instr ctx (Some ty) -> Instr ctx (Some ty)
        FUnop : {t : FloatType ty} -> FloatUnaryOp -> Instr ctx (Some ty) -> Instr ctx (Some ty)
        IBinop : {t : IntType ty} -> IntBinaryOp -> Instr ctx (Some ty) -> Instr ctx (Some ty) -> Instr ctx (Some ty)
        FBinop : {t : FloatType ty} -> FloatBinaryOp -> Instr ctx (Some ty) -> Instr ctx (Some ty) -> Instr ctx (Some ty)
        ITestop : {t : IntType ty} -> IntTestOp -> Instr ctx (Some ty) -> Instr ctx (Some I32)
        IRelop : {t : IntType ty} -> IntRelOp -> Instr ctx (Some ty) -> Instr ctx (Some ty) -> Instr ctx (Some I32)
        FRelop : {t : FloatType ty} -> FloatRelOp -> Instr ctx (Some ty) -> Instr ctx (Some ty) -> Instr ctx (Some I32)
        Drop : Instr ctx (Some ty) -> Instr ctx None
        SelectType : Instr ctx (Some ty) -> Instr ctx (Some ty) -> Instr ctx (Some I32) -> Instr ctx (Some ty)
        LocalGet : (idx : LocalIdx) -> {v : HasLocal ctx idx ty} -> Instr ctx (Some ty)
        LocalSet : (idx : LocalIdx) -> {v : HasLocal ctx idx ty} -> Instr ctx (Some ty) -> Instr ctx None
        LocalTee : (idx : LocalIdx) -> {v : HasLocal ctx idx ty} -> Instr ctx (Some ty) -> Instr ctx (Some ty)
        GlobalGet : (idx : GlobalIdx) -> {v : HasGlobal ctx idx (MkGlobal mut ty)} -> Instr ctx (Some ty)
        GlobalSet : (idx : GlobalIdx) -> {v : HasGlobal ctx idx (MkGlobal Mutable ty)} -> Instr ctx (Some ty) -> Instr ctx None
        -- alignment must not be larger than size of accessed memory fragment, but if
        -- we have overaligned accesses we just decrease alignment when emitting
        ILoad : (size : Size) -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some (intTy size))
        FLoad : (size : Size) -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some (floatTy size))
        IStore : (size : Size) -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some (intTy size)) -> Instr ctx None
        FStore : (size : Size) -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some (floatTy size)) -> Instr ctx None
        ILoad8 : (size : Size) -> Sign -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some (intTy size))
        ILoad16 : (size : Size) -> Sign -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some (intTy size))
        ILoad32 : Sign -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some I64)
        IStore8 : (size : Size) -> Sign -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some (intTy size)) -> Instr ctx None
        IStore16 : (size : Size) -> Sign -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some (intTy size)) -> Instr ctx None
        IStore32 : Sign -> MemArg align -> Instr ctx (Some I32) -> Instr ctx (Some I64) -> Instr ctx None
        MemorySize : Instr ctx (Some I32)
        MemoryGrow : Instr ctx (Some I32) -> Instr ctx (Some I32)
        Unreachable : Instr ctx ty
        Block : (ty : ResultType) -> Expr ctx ty -> Instr (withLabel ty ctx) ty
        Loop : (ty : ResultType) -> Expr ctx ty -> Instr (withLabel ty ctx) ty
        If : (ty : ResultType) -> Expr (withLabel ty ctx) ty -> Expr (withLabel ty ctx) ty -> Instr ctx ty
        -- Br : (idx : LabelIdx) -> {v : HasLabel ctx idx ty} -> Instr ctx ty -> Instr ctx anyTy
        -- BrIf : (idx : LabelIdx) -> {v : HasLabel ctx idx ty} -> Instr ctx ty -> Instr ctx (Some I32) -> Instr ctx ty
        -- BrTable : (default : LabelIdx) -> {v : HasLabel ctx idx ty} -> LabelTable ctx ty -> Instr ctx ty -> Instr ctx anyTy
        Return : {v : HasReturn ctx ty} -> Instr ctx ty -> Instr ctx anyTy
        Call : (idx : FuncIdx) -> {v : HasFunc ctx idx f} -> (params : callParams ctx (args f)) -> Instr ctx (result f)
        CallIndirect : (idx : TypeIdx) -> {v : HasType ctx idx f} -> (params : callParams ctx (args f)) -> Instr ctx (Some I32) -> Instr ctx (result f)

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
