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

-- number boxing and unboxing
coerce : {from : ValueType} -> {to : ValueType} -> MExp from locals -> MExp to locals

-- coerce {ty = Obj} (ObjExp exp) = exp
-- coerce {ty = Num} (NumExp exp) = exp
-- coerce {ty = Obj} (NumExp exp) = Create exp []
-- coerce {ty = Num} (ObjExp exp) = Tag exp
-- coerce {ty} (EitherExp make) = make ty

dummyObject : MExp Obj locals
dummyObject = Create (Const 0) []

makeLocalIndex : (locals : Nat) -> (idx : Nat) -> (prf : LTE (S idx) locals) -> Fin locals
makeLocalIndex (S right) Z (LTESucc LTEZero) = FZ
makeLocalIndex (S right) (S idx) (LTESucc x) = FS (makeLocalIndex right idx x)

capture : {locals : Nat} -> (tag : Integer) -> MExp Obj locals
capture {locals} tag = Create (Const tag) (makeFields locals lteRefl)
    where
        makeFields : (x : Nat) -> (prf : LTE x locals) -> List (MExp Obj locals)
        makeFields Z prf = []
        makeFields (S x) prf = Local (makeLocalIndex locals x prf) :: makeFields x (lteSuccLeft prf)

insertLocalIdx : {locals : Nat} -> (pos : Nat) -> {auto prf : LTE pos locals} -> Fin locals -> Fin (S locals)
insertLocalIdx {locals} pos idx =
    if finToNat idx < locals - pos then
        weaken idx
    else
        FS idx

mutual
    insertLocalList : {locals : Nat} -> (pos : Nat) -> {auto prf : LTE pos locals} -> List (MExp ty locals) -> List (MExp ty (S locals))
    insertLocal : {locals : Nat} -> (pos : Nat) -> {auto prf : LTE pos locals} -> MExp ty locals -> MExp ty (S locals)

    insertLocalList pos [] = []
    insertLocalList pos (x :: xs) = insertLocal pos x :: insertLocalList pos xs

    insertLocal pos (Const x) = Const x
    insertLocal pos (Local x) = Local (insertLocalIdx pos x)
    insertLocal pos {prf} (Let x y) = Let (insertLocal pos x) (insertLocal pos {prf = lteSuccRight prf} y)
    insertLocal pos (Create x xs) = Create (insertLocal pos x) (insertLocalList pos xs)
    insertLocal pos (Field x y) = Field (insertLocal pos x) (insertLocal pos y)
    insertLocal pos (Tag x) = Tag (insertLocal pos x)
    insertLocal pos (If x y z) = If (insertLocal pos x) (insertLocal pos y) (insertLocal pos z)
    insertLocal pos (Call k xs) = Call k (insertLocalList pos xs)
    insertLocal pos (CallVirt x y z) = CallVirt (insertLocal pos x) (insertLocal pos y) (insertLocal pos z)
    insertLocal pos (Binop x y z) = Binop x (insertLocal pos y) (insertLocal pos z)
    insertLocal pos Crash = Crash

insertHere : MExp ty locals -> MExp ty (S locals)
insertHere {locals} expr = insertLocal locals {prf = lteRefl} expr

weaken : MExp ty locals -> MExp ty (S locals)
weaken exp = insertLocal 0 exp

goRebind : (idx : Nat) -> (expr : MExp Obj (S (S idx))) -> MExp Obj 2
goRebind Z expr = expr
goRebind (S x) expr = goRebind x (Let (Field (Local (last {n = (S x)})) (Const (cast x))) expr)

rebindUpvalues : (count : Nat) -> (expr : MExp Obj (S count)) -> MExp Obj 2
rebindUpvalues count expr =
    let
        inner = Mir.Let (Local (weaken (last {n = count}))) (weaken (weaken expr))
    in
        goRebind count inner

applyArgs : (fn : MExp Obj locals) -> (args : List (MExp Obj locals)) -> MExp Obj locals
applyArgs fn [] = fn
applyArgs fn (x :: xs) = applyArgs (CallVirt (Tag fn) fn x) xs

mutual
    translateList : {locals : Nat} -> List (TSExp locals) -> Emit (List (MExp ty locals))
    translateExpr : TSExp locals -> Emit (MExp ty locals)
    translateConstCase : List (ConstBranch locals) -> Maybe (TSExp locals) -> Emit (MExp ty (S locals))

    translateList [] = pure []
    translateList (x :: xs) = pure (!(translateExpr x) :: !(translateList xs))

    translateConstCase [] Nothing = pure Crash
    translateConstCase [] (Just defaultCase) = do
        value <- translateExpr defaultCase
        pure (insertHere value)
    translateConstCase {locals} (b :: bs) df = ?wahsadsda

    translateExpr (Local idx) = pure (coerce (Local idx))
    translateExpr (Global k) = ?translateExpr_rhs_2
    translateExpr {locals} (Lam x) = do
        body <- translateExpr x
        let def = MkMDef 2 (rebindUpvalues locals body)
        defId <- emitDef def
        pure (coerce (capture (cast defId)))
    translateExpr (Let x y) = do
        val <- translateExpr x
        rest <- translateExpr y
        pure (Let val rest)
    -- global functions can be called in mir directly
    translateExpr (Apply (Global f) xs) = do
        args <- translateList xs
        pure (coerce (Call f args))
    -- if we are calling non-global, then it must be lambda function
    translateExpr (Apply f xs) = do
        fn <- translateExpr f
        args <- translateList xs
        pure (coerce (applyArgs fn args))
    translateExpr (Construct tag xs) = do
        fields <- translateList xs
        let tag = Const (cast tag)
        pure (coerce (Create tag fields))
    translateExpr (Force x) = do
        delayed <- translateExpr x
        pure (coerce (CallVirt (Tag delayed) delayed dummyObject))
    translateExpr {locals} (Delay x) = do
        body <- translateExpr x
        let withParam = insertHere body
        let def = MkMDef 2 (rebindUpvalues locals withParam)
        defId <- emitDef def
        pure (coerce (capture (cast defId)))
    translateExpr (Case sc xs x) = ?translateExpr_rhs_9
    translateExpr (ConstCase sc xs x) = do
        matched <- translateExpr sc
        branches <- translateConstCase xs x
        pure (Let matched branches)
    translateExpr (Const (I x)) = pure (coerce (Const x))
    translateExpr (Const WorldVal) = pure (coerce dummyObject)
    translateExpr (Const IntegerType) = pure (coerce dummyObject)
    translateExpr (Const WorldType) = pure (coerce dummyObject)
    translateExpr {ty} Erased = pure (case ty of
        Obj => Create (Const 0) []
        Num => Const 0)
    translateExpr (Crash msg) = pure Crash

translateFunction : (args : Nat) -> (body : TSExp args) -> Emit Nat
translateFunction args body = do
    mbody <- translateExpr body
    emitDef (MkMDef args mbody)

translateConstructor : (tag : Int) -> (arity : Nat) -> MDef
translateConstructor tag arity = MkMDef arity (capture (cast tag))

translateDef : TSDef -> Emit Nat
translateDef (Function args body) = translateFunction args body
translateDef (Constructor tag arity) = emitDef (translateConstructor tag arity)

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
