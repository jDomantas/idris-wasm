module TSExpToMir

import Data.Fin
import Trans
import TSExp
import Mir

%default total

record Emit a where
    constructor MkEmit
    runEmit : List MDef -> (List MDef, a)

Functor Emit where
    map f em = MkEmit (\defs => let (defs', res) = runEmit em defs in (defs', f res))

Applicative Emit where
    pure a = MkEmit (\defs => (defs, a))
    f <*> x = MkEmit (\defs =>
        let (defs', f') = runEmit f defs in
        let (defs'', x') = runEmit x defs' in
            (defs'', f' x'))

Monad Emit where
    x >>= f = MkEmit (\defs =>
        let (defs', x') = runEmit x defs in
            runEmit (f x') defs')

emitDef : MDef -> Emit Nat
emitDef def = MkEmit (\defs => (defs ++ [def], length defs))

emit : Emit a -> (List MDef, a)
emit e = runEmit e []

data AnyExp : (locals : Nat) -> Type where
    ObjExp : MExp Obj locals -> AnyExp locals
    NumExp : MExp Num locals -> AnyExp locals

coerce : {ty : ValueType} -> AnyExp locals -> MExp ty locals
coerce {ty = Obj} (ObjExp exp) = exp
coerce {ty = Num} (NumExp exp) = exp
coerce {ty = Obj} (NumExp exp) = Create exp []
coerce {ty = Num} (ObjExp exp) = Tag exp

translateExpr : TSExp args -> Emit (AnyExp locals)

translateFunction : (args : Nat) -> (body : TSExp args) -> Emit Nat
translateFunction args body = do
    mbody <- translateExpr body
    emitDef (MkMDef args (coerce mbody))

makeLocalIndex : (locals : Nat) -> (idx : Nat) -> (prf : LTE (S idx) locals) -> Fin locals
makeLocalIndex (S right) Z (LTESucc LTEZero) = FZ
makeLocalIndex (S right) (S idx) (LTESucc x) = FS (makeLocalIndex right idx x)

translateConstructor : (tag : Int) -> (arity : Nat) -> MDef
translateConstructor tag arity =
    MkMDef
        arity
        (Create (Const (cast tag)) (makeFields arity lteRefl))
    where
        makeFields : (fields : Nat) -> (prf : LTE fields arity) -> List (MExp Obj arity)
        makeFields Z prf = []
        makeFields (S x) prf = Local (makeLocalIndex arity x prf) :: makeFields x (lteSuccLeft prf)

translateDef : TSDef -> Emit Nat
translateDef (Function args body) = translateFunction args body
translateDef (Constructor tag arity) = emitDef (translateConstructor tag arity)
translateDef (Error body) = emitDef (MkMDef 0 Crash)

data MainState : Nat -> Type where
    Searching : Fin defs -> MainState defs
    Found : Nat -> MainState defs

translateDefs : (defs : List TSDef) -> MainState (length defs) -> Emit Nat
translateDefs [] (Searching FZ) impossible
translateDefs [] (Searching (FS _)) impossible
translateDefs [] (Found idx) = pure idx
translateDefs (d :: ds) (Searching FZ) = do
    idx <- translateDef d
    translateDefs ds (Found idx)
translateDefs (d :: ds) (Searching (FS x)) = do
    translateDef d
    translateDefs ds (Searching x)
translateDefs (d :: ds) (Found idx) = do
    translateDef d
    translateDefs ds (Found idx)

export
translateModule : TSExp.Module -> Trans Mir.Module
translateModule (MkModule defs main) =
    let (mdefs, mainIdx) = emit (translateDefs defs (Searching main)) in
        case natToFin mainIdx (length mdefs) of
            Just idx => pure (MkModule mdefs idx)
            Nothing => abort "bug: main oob"
