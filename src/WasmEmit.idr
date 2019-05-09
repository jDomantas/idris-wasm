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
    emit I64 = [0x7E]
    emit F32 = [0x7D]
    emit F64 = [0x7C]

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
    Emit (Instr ctx ty) where
        emit Unreachable = [0x00]
        emit (Block ty body) = [0x02] ++ emit ty ++ emit body ++ [0x0B]
        emit (Loop ty body) = [0x03] ++ emit ty ++ emit body ++ [0x0B]
        emit (If ty t e) = [0x04] ++ emit ty ++ emit t ++ [0x05] ++ emit e ++ [0x0B]
        emit (Return val) = emit val ++ [0x0F]
        emit (Call idx params) = [] -- FIXME: somehow figure out what params
        emit (CallIndirect ty params idx) = [] -- FIXME: same
        
        emit _ = []

    Emit (Expr ctx ty) where
        emit _ = []
