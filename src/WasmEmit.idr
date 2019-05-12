module WasmEmit

import Data.Fin
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
    emit None = [0x00]
    emit (Some ty) = emit [ty]

Emit FuncType where
    emit (MkFuncType args result) = 0x60 :: emit args ++ emit result

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
        emit (Relop EqInt a b) = emit a ++ emit b ++ [0x46]
        emit (Relop NeInt a b) = emit a ++ emit b ++ [0x47]
        emit (Relop (LtInt Signed) a b) = emit a ++ emit b ++ [0x48]
        emit (Relop (LtInt Unsigned) a b) = emit a ++ emit b ++ [0x49]
        emit (Relop (GtInt Signed) a b) = emit a ++ emit b ++ [0x4A]
        emit (Relop (GtInt Unsigned) a b) = emit a ++ emit b ++ [0x4B]
        emit (Relop (LeInt Signed) a b) = emit a ++ emit b ++ [0x4C]
        emit (Relop (LeInt Unsigned) a b) = emit a ++ emit b ++ [0x4D]
        emit (Relop (GeInt Signed) a b) = emit a ++ emit b ++ [0x4E]
        emit (Relop (GeInt Unsigned) a b) = emit a ++ emit b ++ [0x4F]
        emit (LocalGet idx) = [0x20] ++ emit idx
        emit (LocalSet idx val) = emit val ++ [0x21] ++ emit idx
        emit GlobalGet = [0x23, 0x00]
        emit (GlobalSet val) = emit val ++ [0x24, 0x00]
        emit (Load addr) = emit addr ++ [0x28, 0x02, 0x00]
        emit (Store val addr) = emit val ++ emit addr ++ [0x36, 0x02, 0x00]
        emit MemorySize = [0x3F, 0x00]
        emit (MemoryGrow pages) = emit pages ++ [0x40, 0x00]
        emit Unreachable = [0x00]
        emit (If ty c t e) = emit c ++ [0x04] ++ emit ty ++ emit t ++ [0x05] ++ emit e ++ [0x0B]
        emit (Call idx params) = emit params ++ [0x10] ++ emit idx
        emit (CallIndirect fn a b) = emit a ++ emit b ++ emit fn ++ [0x11, 0x00, 0x00]
        emit (Chain a b) = emit a ++ emit b
        emit Empty = []

emitSection : Int -> List Int -> List Int
emitSection _ [0] = []
emitSection id section = [id] ++ emit (length section) ++ section

Emit Unit where
    emit () = []

range : Nat -> Nat -> List Nat
range from to = if from >= to then [] else from :: range (from + 1) to

emitLimits : Nat -> Maybe Nat -> List Int
emitLimits min Nothing = [0x00] ++ emit min
emitLimits min (Just max) = [0x01] ++ emit min ++ emit max

emitTable : Nat -> List Int
emitTable size = [0x01, 0x70] ++ emitLimits size (Just size)

emitMemory : List Int
emitMemory = [0x01] ++ emitLimits 0 Nothing

emitGlobal : ValueType -> List Int
emitGlobal ty = [0x01] ++ emit ty ++ [0x01, 0x41, 0x00, 0x0B]

emitTableElems : List (Fin x) -> List Int
emitTableElems elems = [0x01, 0x00, 0x41, 0x00, 0x0B] ++ emit (map finToNat elems)

Emit (Function ctx ty) where
    emit (MkFunction locals body) = emit (length el + length eb) ++ el ++ eb
        where
            el : List Int
            el = emit locals
            eb : List Int
            eb = emit body ++ [0x0B]

Emit (Functions ctx types) where
    emit fns = emit (count fns) ++ emf fns
        where
            count : Functions ctx ty -> Nat
            count FunctionsNil = 0
            count (FunctionsCons _ fs) = 1 + count fs
            emf : Functions ctx types -> List Int
            emf FunctionsNil = []
            emf (FunctionsCons f fs) = emit f ++ emf fs

header : List Int
header =
    [ 0x00, 0x61, 0x73, 0x6D
    , 0x01, 0x00, 0x00, 0x00
    ]

Emit Module where
    emit (MkModule decls functions table) =
        header ++
        emitSection 1 (emit (types ++ decls)) ++
        emitSection 3 (emit properDecls) ++
        emitSection 4 (emitTable (length table)) ++
        emitSection 5 emitMemory ++
        emitSection 6 (emitGlobal I32) ++
        emitSection 9 (emitTableElems table) ++
        emitSection 10 (emit functions)
            where
                types : List FuncType
                types = [MkFuncType [I32, I32] (Some I32)]
                properDecls : List Nat
                properDecls = range (length types) (length types + length decls)

export
emitModule : Module -> List Int
emitModule m = emit m
