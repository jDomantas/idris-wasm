module Main

%default total

data ValType = I32 | I64 | F32 | F64
data ResultType = Some ValType | None
data FuncType = MkFuncType (List ValType) ResultType

-- fixme: shpuld be 32 bit integer
U32 : Type
U32 = Int

record Limits where
    constructor MkLimits
    min : U32
    max : Maybe U32

data MemType = MkMemType Limits

data ElemType = FuncRef

record TableType where
    constructor MkTableType
    limits : Limits
    elemType : ElemType

data Mut = Const | Var

record GlobalType where
    constructor MkGlobalType
    mut : Mut
    type : ValType

data ExternType : Type where
    ExternFunc : FuncType -> ExternType
    ExternTable : TableType -> ExternType
    ExternMem : MemType -> ExternType
    ExternGlobal : GlobalType -> ExternType

filterMap : (a -> Maybe b) -> List a -> List b
filterMap _ [] = []
filterMap f (x :: xs) = case f x of
    Just x' => x' :: filterMap f xs
    Nothing => filterMap f xs

funcs : List ExternType -> List FuncType
funcs = filterMap (\x => case x of { ExternFunc x => Just x; _ => Nothing })

tables : List ExternType -> List TableType
tables = filterMap (\x => case x of { ExternTable x => Just x; _ => Nothing })

mems : List ExternType -> List MemType
mems = filterMap (\x => case x of { ExternMem x => Just x; _ => Nothing })

globals : List ExternType -> List GlobalType
globals = filterMap (\x => case x of { ExternGlobal x => Just x; _ => Nothing })

data Size = B32 | B64
data Sign = Unsigned | Signed

data IntVal : Size -> Type where
    Int32 : U32 -> IntVal B32
    -- FIXME: Int should be some 64 bit integer
    Int64 : Int -> IntVal B64

data FloatVal : Size -> Type where
    -- FIXME: appropriate types
    Float32 : Double -> FloatVal B32
    Float64 : Double -> FloatVal B64

-- FIXME: where are they defined in the spec?
-- answer: 2.5.1, all of these are supposed to be u32
LocalIdx : Type
LocalIdx = Nat

GlobalIdx : Type
GlobalIdx = Nat

LabelIdx : Type
LabelIdx = Nat

FuncIdx : Type
FuncIdx = Nat

TypeIdx : Type
TypeIdx = Nat

MemIdx : Type
MemIdx = Nat

TableIdx : Type
TableIdx = Nat

-- FIXME: where is name defined?
Name : Type
Name = String

record MemArg where
    constructor MkMemArg
    offset : U32
    align : U32

data IUnop = Clz | Ctz | Popcnt
data FUnop = Abs | Neg | Sqrt | Ceil | Floor | Trunc | Nearest
data IBinop = IAdd | ISub | IMul | IDiv Sign | IRem Sign | And | Or | Xor | Shl | Shr Sign | Rotl | Rotr
data FBinop = Add | Sub | Mul | Div | Min | Max | CopySign
data IRelop = IEq | INe | ILt Sign | IGt Sign | ILe Sign | IGe Sign
data FRelop = FEq | FNe | FLt | FGt | FLe | FGe

-- FIXME: split by instruction group?
data Instr : Type where
    -- 2.4.1 numeric instructions
    IConst : (s : Size) -> IntVal s -> Instr
    FConst : (s : Size) -> FloatVal s -> Instr
    -- inn.iunop
    IntUnop : Size -> IUnop -> Instr
    -- fnn.funcop
    FloatUnop : Size -> FUnop -> Instr
    -- inn.ibinop
    IntBinop : Size -> IBinop -> Instr
    -- fnn.fbinop
    FloatBinop : Size -> FBinop -> Instr
    -- inn.itestop
    Eqz : Size -> Instr
    -- inn.irelop
    IntRelop : Size -> IRelop -> Instr
    -- fnn.frelop
    FloatRelop : Size -> FRelop -> Instr
    -- conversions
    I32WrapI64 : Instr
    I64ExtendI32 : Sign -> Instr
    TruncToInt : Size -> Size -> Sign -> Instr
    F32DemoteF64 : Instr
    F64PromoteF32 : Instr
    Convert : Size -> Size -> Sign -> Instr
    ReinterpretAsInt : Size -> Instr
    ReinterpretAsFloat : Size -> Instr
    -- 2.4.2 parametric instructions
    Drop : Instr
    Select : Instr
    -- 2.4.3 variable instructions
    LocalGet : LocalIdx -> Instr
    LocalSet : LocalIdx -> Instr
    LocalTee : LocalIdx -> Instr
    GlobalGet : GlobalIdx -> Instr
    GlobalSet : GlobalIdx -> Instr
    -- 2.4.4 memory instructions
    ILoad : Size -> MemArg -> Instr
    FLoad : Size -> MemArg -> Instr
    IStore : Size -> MemArg -> Instr
    FStore : Size -> MemArg -> Instr
    ILoad8 : Size -> Sign -> MemArg -> Instr
    ILoad16 : Size -> Sign -> MemArg -> Instr
    I64Load32 : Sign -> MemArg -> Instr
    IStore8 : Size -> MemArg -> Instr
    IStore16 : Size -> MemArg -> Instr
    I64Store32 : MemArg -> Instr
    MemorySize : Instr
    MemoryGrow : Instr
    -- 2.4.5 control instructions
    Nop : Instr
    Unreachable : Instr
    Block : ResultType -> List Instr -> Instr
    Loop : ResultType -> List Instr -> Instr
    If : ResultType -> List Instr -> List Instr -> Instr
    Br : LabelIdx -> Instr
    BrIf : LabelIdx -> Instr
    BrTable : List LabelIdx -> LabelIdx -> Instr
    Return : Instr
    Call : FuncIdx -> Instr
    CallIndirect : TypeIdx -> Instr

-- 2.4.6 expressions
data Expr = MkExpr (List Instr)

-- 2.5.2 types
data Types = MkTypes (List FuncType)

-- 2.5.3 functions
record Function where
    constructor MkFunction
    type : TypeIdx
    locals : List ValType
    body : Expr

-- 2.5.6 global
record Global where
    constructor MkGlobal
    type : GlobalType
    -- FIXME: init expr must be constant
    init : Expr

-- 2.5.7 element segments
record Element where
    constructor MkElement
    table : TableIdx
    -- FIXME: must be constant
    offset : Expr
    init : List FuncIdx

-- 2.5.8 data segments
record Data where
    constructor MkData
    -- data : MemIdx -- can only be 0, we have not defined MemIdx
    -- FIXME: must be constant
    offset : Expr
    -- FIXME: List Byte
    init : List Int

-- 2.5.10 exports
data ExportDesc : Type where
    ExportFunc : FuncIdx -> ExportDesc
    ExportTable : TableIdx -> ExportDesc
    ExportMem : MemIdx -> ExportDesc
    ExportGlobal : GlobalIdx -> ExportDesc

record Export where
    constructor MkExport
    name : Name
    desc : ExportDesc

-- 2.5.11 imports
data ImportDesc : Type where
    ImportFunc : TypeIdx -> ImportDesc
    ImportTable : TableType -> ImportDesc
    ImportMem : MemType -> ImportDesc
    ImportGlobal : GlobalType -> ImportDesc

record Import where
    constructor MkImport
    -- FIXME: module : Name
    module_ : Name
    name : Name
    desc : ImportDesc

-- 3.1.1 validation context

record Context where
    constructor MkContext
    types : List FuncType
    funcs : List FuncType
    tables : List TableType
    mems : List MemType
    globals : List GlobalType
    locals : List ValType
    labels : List ResultType
    return : Maybe ResultType

withLabel : ResultType -> Context -> Context
withLabel ty (MkContext ts fs tbs mems gs ls lbs r) = MkContext ts fs tbs mems gs ls (ty :: lbs) r

intTy : Size -> ValType
intTy B32 = I32
intTy B64 = I64

floatTy : Size -> ValType
floatTy B32 = F32
floatTy B64 = F64

data LocalHasType : Context -> Nat -> ValType -> Type where
    ThisLocal : LocalHasType (MkContext ts fs tbs mems gs (local :: ls) lbs r) 0 local
    ThatLocal :
        LocalHasType (MkContext ts fs tbs mems gs ls lbs r) x loc
        -> LocalHasType (MkContext ts fs tbs mems gs (l :: ls) lbs r) (S x) loc

data GlobalHasType : Context -> Nat -> Mut -> ValType -> Type where
    ThisGlobal : GlobalHasType (MkContext _ _ _ _ ((MkGlobalType mut ty) :: _) _ _ _) 0 mut ty
    ThatGlobal :
        GlobalHasType (MkContext ts fs tbs mems gs ls lbs r) x mut ty
        -> GlobalHasType (MkContext ts fs tbs mems (g :: gs) ls lbs r) (S x) mut ty

data HasMemory : Context -> Nat -> Type where
    HasMemoryHere : HasMemory (MkContext _ _ _ (_ :: _) _ _ _ _) 0
    HasMemoryThere :
        HasMemory (MkContext ts fs tbs mems gs ls lbs r) x
        -> HasMemory (MkContext ts fs tbs (_ :: mems) gs ls lbs r) (S x)

-- attempting to formalize instruction typing rules
data HasType : Context -> Instr -> List ValType -> List ValType -> Type where
    IConstType : HasType ctx (IConst size val) [] [intTy size]
    FConstType : HasType ctx (FConst size val) [] [floatTy size]
    IUnopType : HasType ctx (IntUnop size op) [intTy size] [intTy size]
    FUnopType : HasType ctx (FloatUnop size op) [floatTy size] [floatTy size]
    IBinopType : HasType ctx (IntBinop size op) [intTy size, intTy size] [intTy size]
    FBinopType : HasType ctx (FloatBinop size op) [floatTy size, floatTy size] [floatTy size]
    EqzType : HasType ctx (Eqz size) [intTy size] [I32]
    IRelopType : HasType ctx (IntRelop size op) [intTy size, intTy size] [I32]
    FRelopType : HasType ctx (FloatRelop size op) [floatTy size, floatTy size] [I32]
    WrapType : HasType ctx I32WrapI64 [I64] [I32]
    ExtendType : HasType ctx (I64ExtendI32 sign) [I32] [I64]
    TruncateType : HasType ctx (TruncToInt dest src sign) [floatTy src] [intTy dest]
    DemoteType : HasType ctx F32DemoteF64 [F64] [F32]
    PromoteType : HasType ctx F64PromoteF32 [F32] [F64]
    ConvertType : HasType ctx (Convert dest src sign) [intTy src] [floatTy dest]
    ReinterpretAsIntType : HasType ctx (ReinterpretAsInt size) [floatTy size] [intTy size]
    ReinterpretAsFloatType : HasType ctx (ReinterpretAsFloat size) [intTy size] [floatTy size]
    DropType : HasType ctx Drop [t] []
    SelectType : HasType ctx Select [t, t, I32] [t]
    LocalGetType : LocalHasType ctx idx ty -> HasType ctx (LocalGet idx) [] [ty]
    LocalSetType : LocalHasType ctx idx ty -> HasType ctx (LocalSet idx) [ty] []
    LocalTeeType : LocalHasType ctx idx ty -> HasType ctx (LocalSet idx) [ty] [ty]
    GlobalGetType : GlobalHasType ctx idx mut ty -> HasType ctx (GlobalGet idx) [] [ty]
    GlobalSetType : GlobalHasType ctx idx Var ty -> HasType ctx (GlobalSet idx) [ty] []
    -- FiXME: validate memory align
    ILoadType : HasMemory ctx 0 -> HasType (ILoad size _) [I32] [intTy size]
    ILoad8Type : HasMemory ctx 0 -> HasType (ILoad8 size _ _) [I32] [intTy size]
    ILoad16Type : HasMemory ctx 0 -> HasType (ILoad16 size _ _) [I32] [intTy size]
    I64Load32Type : HasMemory ctx 0 -> HasType (I64Load32 _ _) [I32] [I64]
    FLoadType : HasMemory ctx 0 -> HasType (FLoad size _) [I32] [floatTy size]
    IStoreType : HasMemory ctx 0 -> HasType (IStore size _) [I32, intTy size] []
    IStore8Type : HasMemory ctx 0 -> HasType (IStore8 size _) [I32, intTy size] []
    IStore16Type : HasMemory ctx 0 -> HasType (IStore16 size _) [I32, intTy size] []
    I64Store32Type : HasMemory ctx 0 -> HasType (I64Store32 _) [I32, I32] []
    MemorySizeType : HasMemory ctx 0 -> HasType MemorySize [] [I32]
    MemoryGrowType : HasMemory ctx 0 -> HasType MemoryGrow [I32] [I32]
    -- control flow
    NopType : HasType ctx Nop [] []
    UnreachableType : HasType ctx Unreachable a b
    BlockType : 


main : IO ()
main = putStrLn "Hello, world"
