module WasmEmitText

import Data.Fin
import Wasm

%default covering

-- Defines mapping from Wasm.Module to wasm text format

record EmitCtx where
    constructor MkEmitCtx
    indent : Nat

indented : EmitCtx -> EmitCtx
indented ctx = record { indent $= S } ctx

interface Emit a where
    emit : EmitCtx -> a -> String

Emit Nat where
    emit ctx x = cast x

Emit Integer where
    emit ctx x = cast x

Emit ValueType where
    emit ctx I32 = "i32"

Emit FuncType where
    emit ctx (MkFuncType [] None) = "(func)"
    emit ctx (MkFuncType [] (Some ty)) = "(func (result " ++ emit ctx ty ++ "))"
    emit ctx (MkFuncType args out) = "(func (param" ++ emitArgs args ++ ")" ++ emitOut out ++ ")"
        where
            emitArgs : List ValueType -> String
            emitArgs [] = ""
            emitArgs (t :: ts) = " " ++ emit ctx t ++ emitArgs ts
            emitOut : ResultType -> String
            emitOut None = ""
            emitOut (Some ty) = " (result " ++ emit ctx ty ++ ")"

mkIndent : EmitCtx -> String
mkIndent (MkEmitCtx indent) = mk indent
    where
        mk Z = ""
        mk (S x) = "  " ++ mk x

mutual
    emitOp : EmitCtx -> String -> Instr ctx ty -> Instr ctx ty -> String
    emitOp ctx name a b = emit ctx a ++ "\n" ++ emit ctx b ++ "\n" ++ mkIndent ctx ++ name

    Emit (CallParams ctx ty) where
        emit ctx ParamsNil = ""
        emit ctx (ParamsCons p ParamsNil) = emit ctx p
        emit ctx (ParamsCons p ps) = emit ctx p ++ "\n" ++ emit ctx ps

    Emit (Instr ctx ty) where
        emit ctx (Drop val) = emit ctx val ++ "\n" ++ mkIndent ctx ++ "drop"
        emit ctx (Const (ValueI32 val)) = mkIndent ctx ++ "i32.const " ++ emit ctx val
        emit ctx (Binop AddInt a b) = emitOp ctx "i32.add" a b
        emit ctx (Binop SubInt a b) = emitOp ctx "i32.sub" a b
        emit ctx (Binop MulInt a b) = emitOp ctx "i32.mul" a b
        emit ctx (Binop (DivInt Signed) a b) = emitOp ctx "i32.div_s" a b
        emit ctx (Binop (DivInt Unsigned) a b) = emitOp ctx "i32.div_u" a b
        emit ctx (Binop (RemInt Signed) a b) = emitOp ctx "i32.mod_s" a b
        emit ctx (Binop (RemInt Unsigned) a b) = emitOp ctx "i32.mod_u" a b
        emit ctx (Relop EqInt a b) = emitOp ctx "i32.eq" a b
        emit ctx (Relop NeInt a b) = emitOp ctx "i32.ne" a b
        emit ctx (Relop (LtInt Signed) a b) = emitOp ctx "i32.lt_s" a b
        emit ctx (Relop (LtInt Unsigned) a b) = emitOp ctx "i32.lt_u" a b
        emit ctx (Relop (GtInt Signed) a b) = emitOp ctx "i32.gt_s" a b
        emit ctx (Relop (GtInt Unsigned) a b) = emitOp ctx "i32.gt_u" a b
        emit ctx (Relop (LeInt Signed) a b) = emitOp ctx "i32.le_s" a b
        emit ctx (Relop (LeInt Unsigned) a b) = emitOp ctx "i32.le_u" a b
        emit ctx (Relop (GeInt Signed) a b) = emitOp ctx "i32.ge_s" a b
        emit ctx (Relop (GeInt Unsigned) a b) = emitOp ctx "i32.ge_u" a b
        emit ctx (LocalGet idx) = mkIndent ctx ++ "get_local $p" ++ emit ctx idx
        emit ctx (LocalSet idx val) = emit ctx val ++ "\n" ++ mkIndent ctx ++ "set_local $p" ++ emit ctx idx
        emit ctx GlobalGet = mkIndent ctx ++ "get_global $g0"
        emit ctx (GlobalSet val) = emit ctx val ++ "\n" ++ mkIndent ctx ++ "set_global $g0"
        emit ctx (Load addr) = emit ctx addr ++ "\n" ++ mkIndent ctx ++ "i32.load"
        emit ctx (Store val addr) = emitOp ctx "i32.store" val addr
        emit ctx MemorySize = mkIndent ctx ++ "current_memory"
        emit ctx (MemoryGrow pages) = emit ctx pages ++ "\n" ++ mkIndent ctx ++ "grow_memory"
        emit ctx Unreachable = mkIndent ctx ++ "unreachable"
        emit ctx (If None c t Empty) =
            emit ctx c ++ "\n" ++
            mkIndent ctx ++ "if\n" ++
            emit (indented ctx) t ++ "\n" ++
            mkIndent ctx ++ "end"
        emit ctx (If None c t e) =
            emit ctx c ++ "\n" ++
            mkIndent ctx ++ "if\n" ++
            emit (indented ctx) t ++ "\n" ++
            mkIndent ctx ++ "else\n" ++
            emit (indented ctx) e ++ "\n" ++
            mkIndent ctx ++ "end"
        emit ctx (If (Some ty) c t e) =
            emit ctx c ++ "\n" ++
            mkIndent ctx ++ "if (result " ++ emit ctx ty ++ ")\n" ++
            emit (indented ctx) t ++ "\n" ++
            mkIndent ctx ++ "else\n" ++
            emit (indented ctx) e ++ "\n" ++
            mkIndent ctx ++ "end"
        emit ctx (Call idx params) = emit ctx params ++ "\n" ++ mkIndent ctx ++ "call $f" ++ emit ctx idx
        emit ctx (CallIndirect fn a b) = emit ctx a ++ "\n" ++ emitOp ctx "call_indirect (type $t0)" b fn
        emit ctx (Chain Empty a) = emit ctx a
        emit ctx (Chain a Empty) = emit ctx a
        emit ctx (Chain a b) = emit ctx a ++ "\n" ++ emit ctx b
        emit ctx Empty = ""

-- emitMain : Fin defs -> List Int
-- emitMain main = [0x01] ++ emit "main" ++ [0x00] ++ emit (finToNat main)

-- emitTableElems : List (Fin x) -> List Int
-- emitTableElems elems = [0x01, 0x00, 0x41, 0x00, 0x0B] ++ emit (map finToNat elems)

emitLocalDecls : EmitCtx -> FuncType -> List ValueType -> Nat -> String
emitLocalDecls ctx (MkFuncType [] None) [] idx = ""
emitLocalDecls ctx (MkFuncType [] None) (l :: ls) idx =
    "\n" ++
    mkIndent ctx ++ "(local $p" ++ emit ctx idx ++ " " ++ emit ctx l ++ ")" ++
    emitLocalDecls ctx (MkFuncType [] None) ls (S idx)
emitLocalDecls ctx (MkFuncType [] (Some ty)) ls idx =
    " (result " ++ emit ctx ty ++ ")" ++
    emitLocalDecls ctx (MkFuncType [] None) ls idx
emitLocalDecls ctx (MkFuncType (p :: ps) res) ls idx =
    " (param $p" ++ emit ctx idx ++ " " ++ emit ctx p ++ ")" ++
    emitLocalDecls ctx (MkFuncType ps res) ls (S idx)

Emit (Functions ctx types) where
    emit {types} ctx fns = go ctx types fns 0
        where
            emitFn : EmitCtx -> (ty : FuncType) -> Function fnCtx ty -> Nat -> String
            emitFn ctx ty (MkFunction locals body) idx =
                mkIndent ctx ++ "(func $f" ++ emit ctx idx ++
                    " (type $t" ++ emit ctx (S idx) ++ ")" ++
                    emitLocalDecls (indented ctx) ty locals 0 ++ "\n" ++
                    emit (indented ctx) body ++ ")"
            go : EmitCtx -> (types : List FuncType) -> Functions fnCtx types -> Nat -> String
            go ctx [] FunctionsNil idx = ""
            go ctx [t] (FunctionsCons f FunctionsNil) idx =
                emitFn ctx t f idx
            go ctx (t :: ts) (FunctionsCons f fs) idx =
                emitFn ctx t f idx ++ "\n" ++ go ctx ts fs (S idx)
            go ctx [] (FunctionsCons _ _) idx impossible
            go ctx (_ :: _) FunctionsNil idx impossible

emitTypes : EmitCtx -> List FuncType -> Nat -> String
emitTypes ctx [] idx = ""
emitTypes ctx (t :: ts) idx =
    mkIndent ctx ++ "(type $t" ++ emit ctx idx ++ " " ++ emit ctx t ++ ")\n" ++
    emitTypes ctx ts (S idx)

emitTable : EmitCtx -> List (Fin x) -> String
emitTable ctx items = mkIndent ctx ++ "(elem (i32.const 0)" ++ go items 0 ++ ")"
    where
        go : List (Fin x) -> Nat -> String
        go [] idx = ""
        go (x :: xs) idx = " $f" ++ emit ctx idx ++ go xs (S idx)

Emit Module where
    emit ctx (MkModule decls functions table main) =
        let
            ctx' = indented ctx
            types = emitTypes ctx' (MkFuncType [I32, I32] (Some I32) :: decls) 0
            fns = emit ctx' functions
        in
            mkIndent ctx ++ "(module\n" ++
            types ++
            fns ++ "\n" ++
            mkIndent ctx' ++ "(table $T0 " ++ emit ctx (length table) ++ " " ++ emit ctx (length table) ++ " anyfunc)\n" ++
            mkIndent ctx' ++ "(memory $M0 0)\n" ++
            mkIndent ctx' ++ "(global $g0 (mut i32) (i32.const 0))\n" ++
            mkIndent ctx' ++ "(export \"main\" (func $f" ++ emit ctx (finToNat main) ++ "))\n" ++
            emitTable ctx' table ++ ")"


export
emitModule : Module -> String
emitModule m = emit (MkEmitCtx 0) m ++ "\n"
