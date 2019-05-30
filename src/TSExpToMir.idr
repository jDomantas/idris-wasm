module TSExpToMir

import Data.Fin
import Data.List
import Data.Vect
import Trans
import TSExp
import Mir

%default covering

record Emit a where
    constructor MkEmit
    runEmit : List Nat -> List MDef -> Either String (List MDef, a)

Functor Emit where
    map f em = MkEmit (\arities, defs => case runEmit em arities defs of
        Right (defs', res) => Right (defs', f res)
        Left err => Left err)

Applicative Emit where
    pure a = MkEmit (\arities, defs => pure (defs, a))
    f <*> x = MkEmit (\arities, defs => case runEmit f arities defs of
        Left err => Left err
        Right (defs', f') => case runEmit x arities defs' of
            Left err => Left err
            Right (defs'', x') => Right (defs'', f' x'))

Monad Emit where
    x >>= f = MkEmit (\arities, defs => case runEmit x arities defs of
        Left err => Left err
        Right (defs', x') => runEmit (f x') arities defs')

emitDef : MDef -> Emit Nat
emitDef def = MkEmit (\arities, defs => Right (defs ++ [def], length defs))

getArity : (global : Nat) -> Emit Nat
getArity global = MkEmit (\arities, defs => case index' global arities of
    Just arity => Right (defs, arity)
    Nothing => Left "tsexp global ref out of bounds")

emit : List Nat -> Emit a -> Trans (List MDef, a)
emit arities e = case runEmit e arities [] of
    Left err => abort err
    Right ok => pure ok

-- number boxing and unboxing
coerce : {from : ValueType} -> {to : ValueType} -> MExp from locals -> MExp to locals

coerce {from = Obj} {to = Obj} exp = exp
coerce {from = Num} {to = Num} exp = exp
coerce {from = Num} {to = Obj} exp = Create exp []
coerce {from = Obj} {to = Num} exp = Tag exp

dummy : {ty : ValueType} -> MExp ty locals
dummy = coerce (Const 0)

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
applyArgs fn (x :: xs) = applyArgs (Let fn (CallVirt (Tag (Local FZ)) (Local FZ) (insertHere x))) xs

wrappingArithmetic : (x : Nat) -> {amount : Nat} -> (prf : LTE (S x) amount) -> (S (minus amount (S x)) = minus amount x)
wrappingArithmetic _ {amount = Z} LTEZero impossible
wrappingArithmetic _ {amount = Z} (LTESucc _) impossible
wrappingArithmetic Z {amount = (S k)} prf = rewrite minusZeroRight k in Refl
wrappingArithmetic (S k) {amount = S j} prf = wrappingArithmetic k (fromLteSucc prf)

wrapLambdas : {locals : Nat} -> (idx : Nat) -> (amount : Nat) -> TSExp locals
wrapLambdas {locals} idx amount = replace (sym (minusZeroN amount)) {P = \x => TSExp (plus x locals)} (go amount {prf = lteRefl})
    where
        makeParamList : (to : Nat) -> {prf : LTE to amount} -> List (TSExp (amount + locals))
        makeParamList Z {prf} = []
        makeParamList (S x) {prf} = Local (weakenN locals (makeLocalIndex amount x prf)) :: makeParamList x {prf = lteSuccLeft prf}
        go : (layers : Nat) -> {prf : LTE layers amount} -> TSExp (amount - layers + locals)
        go Z = rewrite minusZeroRight amount in Apply (Global idx) (makeParamList amount {prf = lteRefl})
        go (S x) {prf} = Lam (replace (sym (wrappingArithmetic x prf)) {P = \t => TSExp (plus t locals)} (go x {prf = lteSuccLeft prf}))

unpackObject : {locals : Nat} -> (idx : Nat) -> (expr : MExp ty (S idx + locals)) -> MExp ty (S locals)
unpackObject Z expr = expr
unpackObject {locals} (S x) expr = unpackObject x (Let (Field (Local (weakenN locals (last {n = x}))) (Const (cast x))) expr)

mutual
    translateList : {locals : Nat} -> List (TSExp locals) -> Emit (List (MExp ty locals))
    translateExpr : TSExp locals -> Emit (MExp ty locals)
    translateConstCase : List (ConstBranch locals) -> Maybe (TSExp locals) -> Emit (MExp ty (S locals))
    translateCase : List (Branch locals) -> Maybe (TSExp locals) -> Emit (MExp ty (S locals))

    translateList [] = pure []
    translateList (x :: xs) = pure (!(translateExpr x) :: !(translateList xs))

    translateConstCase [] Nothing = pure Crash
    translateConstCase [] (Just defaultCase) = pure (insertHere !(translateExpr defaultCase))
    translateConstCase {locals} (MkConstBranch tag value :: bs) df = do
        body <- translateExpr value
        rest <- translateConstCase bs df
        let code = If (Binop Eq (Const (cast tag)) (coerce (Local FZ)))
            (insertHere body)
            rest
        pure code

    translateCase [] Nothing = pure Crash
    translateCase [] (Just defaultCase) = pure (insertHere !(translateExpr defaultCase))
    translateCase {locals} (MkBranch tag args value :: bs) df = do
        body <- translateExpr value
        rest <- translateCase bs df
        let unpacked = unpackObject args (insertHere body)
        let code = If (Binop Eq (Const (cast tag)) (Tag (Local FZ)))
            unpacked
            rest
        pure code

    translateExpr (Local idx) = pure (coerce (Local idx))
    translateExpr (Global k) = do
        arity <- getArity k
        -- we give up totality here for convenience: its easier to add lambdas
        -- in tsexp form, but then the compiler sees this as possibly increasing
        -- the size of `expr` parameter
        translateExpr (wrapLambdas k arity)
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
    -- if we are calling non-global, then it must be lambda function - use callvirt
    translateExpr (Apply f xs) = do
        fn <- translateExpr f
        args <- translateList xs
        pure (coerce (applyArgs fn args))
    translateExpr (Construct tag xs) = do
        fields <- translateList xs
        let tag = Const (cast tag)
        pure (coerce (Create tag fields))
    translateExpr (Op Add [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Add a b))
    translateExpr (Op Sub [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Sub a b))
    translateExpr (Op Mul [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Mul a b))
    translateExpr (Op Div [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Div a b))
    translateExpr (Op Mod [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Rem a b))
    translateExpr (Op Neg [a]) = do
        a <- translateExpr a
        pure (coerce (Binop Sub (Const 0) a))
    translateExpr (Op LT [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Lt a b))
    translateExpr (Op LTE [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Le a b))
    translateExpr (Op EQ [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Eq a b))
    translateExpr (Op GT [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Gt a b))
    translateExpr (Op GTE [a, b]) = do
        a <- translateExpr a
        b <- translateExpr b
        pure (coerce (Binop Ge a b))
    translateExpr (Force x) = do
        delayed <- translateExpr x
        pure (coerce (CallVirt (Tag delayed) delayed dummy))
    translateExpr {locals} (Delay x) = do
        body <- translateExpr x
        let withParam = insertHere body
        let def = MkMDef 2 (rebindUpvalues locals withParam)
        defId <- emitDef def
        pure (coerce (capture (cast defId)))
    translateExpr (Case sc xs x) = do
        matched <- translateExpr sc
        branches <- translateCase xs x
        pure (Let matched branches)
    translateExpr (ConstCase sc xs x) = do
        matched <- translateExpr sc
        branches <- translateConstCase xs x
        pure (Let matched branches)
    translateExpr (Const (I x)) = pure (coerce (Const x))
    translateExpr (Const WorldVal) = pure dummy
    translateExpr (Const IntegerType) = pure dummy
    translateExpr (Const WorldType) = pure dummy
    translateExpr {ty} Erased = pure dummy
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

translateDefs : (defs : List TSDef) -> MainState (length defs) -> Emit (List Nat, Nat)
translateDefs [] (Searching FZ) impossible
translateDefs [] (Searching (FS _)) impossible
translateDefs [] (Found idx) = pure ([], idx)
translateDefs (d :: ds) (Searching FZ) = do
    idx <- translateDef d
    (indices, main) <- translateDefs ds (Found idx)
    pure (idx :: indices, main)
translateDefs (d :: ds) (Searching (FS x)) = do
    idx <- translateDef d
    (indices, main) <- translateDefs ds (Searching x)
    pure (idx :: indices, main)
translateDefs (d :: ds) (Found mainIdx) = do
    idx <- translateDef d
    (indices, main) <- translateDefs ds (Found mainIdx)
    pure (idx :: indices, main)

arity : TSDef -> Nat
arity (Function args _) = args
arity (Constructor _ arity) = arity

fixIndex : List Nat -> Nat -> Nat
fixIndex [] _ = 0
fixIndex (i :: _) Z = i
fixIndex (_ :: is) (S x) = fixIndex is x

parameters (actualIndices : List Nat)
    fixGlobalsInExpr : MExp ty vars -> MExp ty vars
    fixGlobalsInExpr (Const x) = Const x
    fixGlobalsInExpr (Local x) = Local x
    fixGlobalsInExpr (Let x y) = Let (fixGlobalsInExpr x) (fixGlobalsInExpr y)
    fixGlobalsInExpr (Create x xs) = Create (fixGlobalsInExpr x) (map fixGlobalsInExpr xs)
    fixGlobalsInExpr (Field x y) = Field (fixGlobalsInExpr x) (fixGlobalsInExpr y)
    fixGlobalsInExpr (Tag x) = Tag (fixGlobalsInExpr x)
    fixGlobalsInExpr (If x y z) = If (fixGlobalsInExpr x) (fixGlobalsInExpr y) (fixGlobalsInExpr z)
    fixGlobalsInExpr (Call k xs) = Call (fixIndex actualIndices k) (map fixGlobalsInExpr xs)
    fixGlobalsInExpr (CallVirt x y z) = CallVirt (fixGlobalsInExpr x) (fixGlobalsInExpr y) (fixGlobalsInExpr z)
    fixGlobalsInExpr (Binop x y z) = Binop x (fixGlobalsInExpr y) (fixGlobalsInExpr z)
    fixGlobalsInExpr Crash = Crash

    fixGlobalsInDef : MDef -> MDef
    fixGlobalsInDef (MkMDef args body) = MkMDef args (fixGlobalsInExpr body)

mapDoesNotChangeLength : (list : List a) -> (f : a -> b) -> (length list = length (map f list))
mapDoesNotChangeLength [] f = Refl
mapDoesNotChangeLength (x :: xs) f = rewrite mapDoesNotChangeLength xs f in Refl

export
translateModule : TSExp.Module -> Trans Mir.Module
translateModule (MkModule defs main) = do
    (mdefs, (indices, mainIdx)) <- emit (map arity defs) (translateDefs defs (Searching main))
    case natToFin mainIdx (length mdefs) of
        Just idx => pure (MkModule (map (fixGlobalsInDef indices) mdefs) (rewrite sym (mapDoesNotChangeLength mdefs (fixGlobalsInDef indices)) in idx))
        Nothing => abort "bug: main oob"
