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
    EitherExp : ((ty : ValueType) -> MExp ty locals) -> AnyExp locals

-- number boxing and unboxing
coerce : {ty : ValueType} -> AnyExp locals -> MExp ty locals
coerce {ty = Obj} (ObjExp exp) = exp
coerce {ty = Num} (NumExp exp) = exp
coerce {ty = Obj} (NumExp exp) = Create exp []
coerce {ty = Num} (ObjExp exp) = Tag exp
coerce {ty} (EitherExp make) = make ty

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

mutual
    translateList : {locals : Nat} -> List (TSExp locals) -> Emit (List (AnyExp locals))
    translateExpr : TSExp locals -> Emit (AnyExp locals)

    translateList [] = pure []
    translateList (x :: xs) = pure (!(translateExpr x) :: !(translateList xs))

    translateExpr (Local idx) = pure (ObjExp (Local idx))
    translateExpr (Global k) = ?translateExpr_rhs_2
    translateExpr {locals} (Lam x) = do
        body <- translateExpr x
        let def = MkMDef 2 (rebindUpvalues locals (coerce body))
        defId <- emitDef def
        pure (ObjExp (capture (cast defId)))
    translateExpr (Let x y) = do
        val <- translateExpr x
        rest <- translateExpr y
        pure (EitherExp (\ty => Let (coerce val) (coerce rest)))
    translateExpr (Apply x xs) = ?translateExpr_rhs_5
    translateExpr (Construct tag xs) = do
        fields <- translateList xs
        let tag = Const (cast tag)
        let fields = map (coerce {ty = Obj}) fields
        pure (ObjExp (Create tag fields))
    translateExpr (Force x) = do
        x' <- translateExpr x
        let delayed = coerce {ty = Obj} x'
        pure (ObjExp (CallVirt (Tag delayed) delayed dummyObject))
    translateExpr {locals} (Delay x) = do
        body <- translateExpr x
        let withParam = insertLocal locals {prf = lteRefl} (coerce body)
        let def = MkMDef 2 (rebindUpvalues locals withParam)
        defId <- emitDef def
        pure (ObjExp (capture (cast defId)))
    translateExpr (Case sc xs x) = ?translateExpr_rhs_9
    translateExpr (ConstCase sc xs x) = ?translateExpr_rhs_10
    translateExpr (Const (I x)) = pure (NumExp (Const x))
    translateExpr (Const WorldVal) = pure (ObjExp dummyObject)
    translateExpr (Const IntegerType) = pure (ObjExp dummyObject)
    translateExpr (Const WorldType) = pure (ObjExp dummyObject)
    translateExpr Erased = pure (EitherExp (\ty => case ty of
        Obj => Create (Const 0) []
        Num => Const 0))
    translateExpr (Crash msg) = pure (EitherExp (\ty => Crash))

translateFunction : (args : Nat) -> (body : TSExp args) -> Emit Nat
translateFunction args body = do
    mbody <- translateExpr body
    emitDef (MkMDef args (coerce mbody))

translateConstructor : (tag : Int) -> (arity : Nat) -> MDef
translateConstructor tag arity = MkMDef arity (capture (cast tag))

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
