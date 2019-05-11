module
MirToWasm

import Data.Fin
import Mir
import Wasm

%default total

virtCallSig : FuncType
virtCallSig = MkFuncType [I32, I32] (Some I32)

mkArgs : Nat -> List Wasm.ValueType
mkArgs Z = []
mkArgs (S x) = I32 :: mkArgs x

translateDecl : MDef -> FuncType
translateDecl def = MkFuncType (mkArgs (args def)) (Some I32)

translateDecls : List MDef -> List FuncType
translateDecls [] = []
translateDecls (d :: ds) = translateDecl d :: translateDecls ds

makeTable : (defs : Nat) -> List (Fin defs)
makeTable defs = reverse (go defs)
    where
        go : (x : Nat) -> List (Fin x)
        go Z = []
        go (S x) = last {n = x} :: map weaken (go x)

translateDef :
    (ctx : FunctionCtx) ->
    (def : MDef) ->
    Function ctx (MkFuncType (mkArgs (args def)) (Some I32))
translateDef ctx def = MkFunction [] (ExprReturn (Const (ValueI32 0)))

translateDefsGo :
    (ctx : FunctionCtx) ->
    (defs : List MDef) ->
    Functions ctx (translateDecls defs)
translateDefsGo ctx [] = FunctionsNil
translateDefsGo ctx (d :: ds) = FunctionsCons (translateDef ctx d) (translateDefsGo ctx ds)

translateDefs : (defs : List MDef) -> Functions (MkFunctionCtx (translateDecls defs) [MirToWasm.virtCallSig]) (translateDecls defs)
translateDefs defs =
    let
        ctx = MkFunctionCtx (translateDecls defs) [virtCallSig]
    in
        translateDefsGo ctx defs

export
translateModule : Mir.Module -> Wasm.Module
translateModule mod =
    let
        mdefs = defs mod
        wasmDecls = translateDecls mdefs
    in
        MkModule
            wasmDecls
            [virtCallSig]
            (translateDefs mdefs)
            (makeTable (length wasmDecls))
