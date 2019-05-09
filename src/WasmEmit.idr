module WasmEmit

import Wasm

-- Defines mapping from Wasm.Module to wasm binary format

-- Idris doesn't have bytes :(
-- So we'll use Int instead of that
interface Emit a where
    emit : a -> List Int

Emit Int where
    emit b = [b]

Emit Nat where
    emit x =
        if x < 128 then
            [toIntNat x]
        else
            (128 + toIntNat (mod x 128)) :: emit (div x 128)

Emit Integer where
    emit x =
        if x < 64 && x >= 0 then
            [fromInteger x]
        else if x < 0 && x >= -64 then
            [fromInteger (x + 128)]
        else
            (128 + fromInteger low) :: emit high
            where
                sign : Integer
                sign = if x < 0 then -1 else 1
                low : Integer
                low = sign * mod (abs x) 128
                high : Integer
                high = sign * div (abs x) 128

Emit a => Emit (List a) where
    emit l = emit (length l) ++ go l
        where
            go [] = []
            go (x :: xs) = emit x ++ go xs

Emit ValueType where
    emit I32 = [0x7F]

Emit ResultType where
    emit None = [0x40]
    emit (Some ty) = emit ty

Emit FuncType where
    emit (MkFuncType args result) = 0x60 :: emit args ++ emit result

-- missing: Emit Limits
-- missing: Emit MemoryType
-- missing: Emit TableType

Emit Global where
    emit (MkGlobal Immutable type) = emit type ++ [0x00]
    emit (MkGlobal Mutable type) = emit type ++ [0x01]

mutual
    Emit (CallParams ctx ty) where
        emit ParamsNil = []
        emit (ParamsCons p ps) = emit p ++ emit ps

    Emit (Instr ctx ty) where
        emit (Const (ValueI32 val)) = 0x41 :: emit val
        emit (Binop AddInt a b) = emit a ++ emit b ++ [0x6A]
        emit (Binop SubInt a b) = emit a ++ emit b ++ [0x6B]
        emit (Binop MulInt a b) = emit a ++ emit b ++ [0x6C]
        emit (Binop (DivInt Signed) a b) = emit a ++ emit b ++ [0x6D]
        emit (Binop (DivInt Unsigned) a b) = emit a ++ emit b ++ [0x6E]
        emit (Binop (RemInt Signed) a b) = emit a ++ emit b ++ [0x6F]
        emit (Binop (RemInt Unsigned) a b) = emit a ++ emit b ++ [0x70]
        emit (Testop Eqz a) = emit a ++ [0x45]
        emit (Relop EqInt a b) = [0x46]
        emit (Relop NeInt a b) = [0x47]
        emit (Relop (LtInt Signed) a b) = [0x48]
        emit (Relop (LtInt Unsigned) a b) = [0x49]
        emit (Relop (GtInt Signed) a b) = [0x4A]
        emit (Relop (GtInt Unsigned) a b) = [0x4B]
        emit (Relop (LeInt Signed) a b) = [0x4C]
        emit (Relop (LeInt Unsigned) a b) = [0x4D]
        emit (Relop (GeInt Signed) a b) = [0x4E]
        emit (Relop (GeInt Unsigned) a b) = [0x4F]
        emit (LocalGet idx) = [0x20] ++ emit idx
        emit (LocalSet idx val) = emit val ++ [0x21] ++ emit idx
        emit (LocalTee idx val) = emit val ++ [0x22] ++ emit idx
        emit (GlobalGet idx) = [0x23] ++ emit idx
        emit (GlobalSet idx val) = emit val ++ [0x24] ++ emit idx
        emit (Load addr) = emit addr ++ [0x28, 0x02, 0x00]
        emit (Store addr val) = emit val ++ emit addr ++ [0x36, 0x02, 0x00]
        emit MemorySize = [0x3F, 0x00]
        emit (MemoryGrow pages) = emit pages ++ [0x40, 0x00]
        emit Unreachable = [0x00]
        emit (Block ty body) = [0x02] ++ emit ty ++ emit body ++ [0x0B]
        emit (Loop ty body) = [0x03] ++ emit ty ++ emit body ++ [0x0B]
        emit (If ty t e) = [0x04] ++ emit ty ++ emit t ++ [0x05] ++ emit e ++ [0x0B]
        emit (Return val) = emit val ++ [0x0F]
        emit (Call idx params) = emit params ++ [0x10] ++ emit idx
        emit (CallIndirect ty params idx) = emit params ++ emit idx ++ [0x11] ++ emit ty ++ [0x00]

    Emit (Expr ctx ty) where
        emit ExprEmpty = []
        emit (ExprReturn instr) = emit instr
        emit (ExprChain i e) = emit i ++ emit e


