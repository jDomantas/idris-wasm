module Common


public export
data Constant 
    = I Int
    | BI Integer
    | Str String
    | Ch Char
    | Db Double
    | WorldVal
    | IntType
    | IntegerType
    | StringType
    | CharType
    | DoubleType
    | WorldType

public export
data PrimFn : Nat -> Type where
    Add : (ty : Constant) -> PrimFn 2
    Sub : (ty : Constant) -> PrimFn 2
    Mul : (ty : Constant) -> PrimFn 2
    Div : (ty : Constant) -> PrimFn 2
    Mod : (ty : Constant) -> PrimFn 2
    Neg : (ty : Constant) -> PrimFn 1

    LT  : (ty : Constant) -> PrimFn 2
    LTE : (ty : Constant) -> PrimFn 2
    EQ  : (ty : Constant) -> PrimFn 2
    GTE : (ty : Constant) -> PrimFn 2
    GT  : (ty : Constant) -> PrimFn 2

    StrLength : PrimFn 1
    StrHead : PrimFn 1
    StrTail : PrimFn 1
    StrIndex : PrimFn 2
    StrCons : PrimFn 2
    StrAppend : PrimFn 2
    StrReverse : PrimFn 1
    StrSubstr : PrimFn 3
