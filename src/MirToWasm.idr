module MirToWasm

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

mutual
    data AllocExp : MExp ty locals -> (slots : Nat) -> Type where
        AllocConst : AllocExp (Const val) slots
        AllocLocal : AllocExp (Local idx) slots
        AllocLet : AllocExp v (S slots) -> AllocExp e slots -> AllocExp (Let v e) (S slots)
        AllocCreate : AllocExp t slots -> AllocList fields slots -> AllocExp (Create t fields) slots
        AllocField : AllocExp o slots -> AllocExp f slots -> AllocExp (Field o f) slots
        AllocTag : AllocExp o slots -> AllocExp (Tag o) slots
        AllocIf : AllocExp c slots -> AllocExp t slots -> AllocExp e slots -> AllocExp (If c t e) slots
        AllocCall : AllocList args slots -> AllocExp (Call f args) slots
        AllocCallVirt : AllocExp f slots -> AllocExp a slots -> AllocExp b slots -> AllocExp (CallVirt f a b) slots
        AllocBinop : AllocExp a slots -> AllocExp b slots -> AllocExp (Binop op a b) slots

    data AllocList : List (MExp ty locals) -> (slots : Nat) -> Type where
        AllocNil : AllocList [] slots
        AllocCons : AllocExp e slots -> AllocList es slots -> AllocList (e :: es) slots

sBeforePlus : (x : Nat) -> (y : Nat) -> plus x (S y) = S (plus x y)
sBeforePlus Z y = Refl
sBeforePlus (S k) y = rewrite sBeforePlus k y in Refl

sAfterPlus : (x : Nat) -> (y : Nat) -> S (plus x y) = plus x (S y)
sAfterPlus x y = sym (sBeforePlus x y)

mutual
    allocMoreList : (exps : List (MExp ty locals)) -> AllocList exps slots -> AllocList exps (x + slots)
    allocMore : {x : Nat} -> {slots : Nat} -> (exp : MExp ty locals) -> AllocExp exp slots -> AllocExp exp (x + slots)

    allocMoreList [] AllocNil = AllocNil
    allocMoreList (x :: xs) (AllocCons a as) = AllocCons (allocMore x a) (allocMoreList xs as)

    allocMore (Const val) AllocConst = AllocConst
    allocMore (Local idx) AllocLocal = AllocLocal
    allocMore {x = x} {slots = S s} (Let v e) (AllocLet a b) =
        rewrite sBeforePlus x s in
        AllocLet (rewrite sAfterPlus x s in allocMore v a) (allocMore e b)
    allocMore (Create t fields) (AllocCreate x y) = AllocCreate (allocMore t x) (allocMoreList fields y)
    allocMore (Field o f) (AllocField x y) = AllocField (allocMore o x) (allocMore f y)
    allocMore (Tag o) (AllocTag x) = AllocTag (allocMore o x)
    allocMore (If c t e) (AllocIf x y z) = AllocIf (allocMore c x) (allocMore t y) (allocMore e z)
    allocMore (Call f args) (AllocCall x) = AllocCall (allocMoreList args x)
    allocMore (CallVirt f a b) (AllocCallVirt x y z) = AllocCallVirt (allocMore f x) (allocMore a y) (allocMore b z)
    allocMore (Binop op a b) (AllocBinop x y) = AllocBinop (allocMore a x) (allocMore b y)

diff : (x : Nat) -> (y : Nat) -> Either (a ** a + x = y) (a ** x = a + y)
diff Z y = Left (y ** rewrite plusZeroRightNeutral y in Refl)
diff x Z = Right (x ** rewrite plusZeroRightNeutral x in Refl)
diff (S x) (S y) = case diff x y of
    Left (a ** prf) => Left (a ** rewrite sBeforePlus a x in eqSucc (plus a x) y prf)
    Right (a ** prf) => Right (a ** rewrite sBeforePlus a y in eqSucc x (plus a y) prf)

diff3 : (x : Nat) -> (y : Nat) -> (z : Nat) -> Either ((a ** a + y = x), (b ** b + z = x)) (Either ((a ** a + x = y), (b ** b + z = y)) ((a ** a + x = z), (b ** b + y = z)))
diff3 Z y z = case diff y z of
    Left (d ** prf) => Right (Right ((z ** rewrite plusZeroRightNeutral z in Refl), (d ** prf)))
    Right (d ** prf) => Right (Left ((y ** rewrite plusZeroRightNeutral y in Refl), (d ** sym prf)))
diff3 x Z z = case diff x z of
    Left (d ** prf) => Right (Right ((d ** prf), (z ** rewrite plusZeroRightNeutral z in Refl)))
    Right (d ** prf) => Left ((x ** rewrite plusZeroRightNeutral x in Refl), (d ** sym prf))
diff3 x y Z = case diff x y of
    Left (d ** prf) => Right (Left ((d ** prf), (y ** rewrite plusZeroRightNeutral y in Refl)))
    Right (d ** prf) => Left ((d ** sym prf), (x ** rewrite plusZeroRightNeutral x in Refl))
diff3 (S x) (S y) (S z) = case diff3 x y z of
    Left ((a ** p1), (b ** p2)) => Left ((a ** rewrite sBeforePlus a y in eqSucc (plus a y) x p1), (b ** rewrite sBeforePlus b z in eqSucc (plus b z) x p2))
    Right (Left ((a ** p1), (b ** p2))) => Right (Left ((a ** rewrite sBeforePlus a x in eqSucc (plus a x) y p1), (b ** rewrite sBeforePlus b z in eqSucc (plus b z) y p2)))
    Right (Right ((a ** p1), (b ** p2))) => Right (Right ((a ** rewrite sBeforePlus a x in eqSucc (plus a x) z p1), (b ** rewrite sBeforePlus b y in eqSucc (plus b y) z p2)))

mutual
    allocExp : (exp : MExp ty locals) -> (slots : Nat ** AllocExp exp slots)
    allocList : (exps : List (MExp ty locals)) -> (slots : Nat ** AllocList exps slots)

    allocExp (Const x) = (0 ** AllocConst)
    allocExp (Local x) = (0 ** AllocLocal)
    allocExp (Let a b) =
        let
            (sa ** aa) = allocExp a
            (sb ** ab) = allocExp b
        in
            case diff sa sb of
                Left (d ** prf) => (S sb ** AllocLet (rewrite sym prf in allocMore {x = S d} a aa) ab)
                Right (Z ** prf) => (S sb ** AllocLet (rewrite sym prf in allocMore {x = 1} a aa) ab)
                Right (S d ** prf) => (sa ** rewrite prf in (AllocLet (rewrite sym prf in aa) (allocMore {x = d} b ab))) --(sa ** AllocLet aa (rewrite prf in allocMore {x = d} b ab))
    allocExp (Create x xs) =
        let
            (sx ** ax) = allocExp x
            (sxs ** axs) = allocList xs
        in
            case diff sx sxs of
                Left (d ** prf) => (sxs ** AllocCreate (rewrite sym prf in allocMore {x = d} x ax) axs)
                Right (d ** prf) => (sx ** AllocCreate ax (rewrite prf in allocMoreList {x = d} xs axs))
    allocExp (Field a b) =
        let
            (sa ** aa) = allocExp a
            (sb ** ab) = allocExp b
        in
            case diff sa sb of
                Left (d ** prf) => (sb ** AllocField (rewrite sym prf in allocMore {x = d} a aa) ab)
                Right (d ** prf) => (sa ** AllocField aa (rewrite prf in allocMore {x = d} b ab))
    allocExp (Tag x) = let (slots ** prf) = allocExp x in (slots ** (AllocTag prf))
    allocExp (If a b c) =
        let
            (sa ** aa) = allocExp a
            (sb ** ab) = allocExp b
            (sc ** ac) = allocExp c
        in
            case diff3 sa sb sc of
                Left ((da ** prf1), (db ** prf2)) => (sa ** AllocIf aa (rewrite sym prf1 in allocMore {x = da} b ab) (rewrite sym prf2 in allocMore {x = db} c ac))
                Right (Left ((da ** prf1), (db ** prf2))) => (sb ** AllocIf (rewrite sym prf1 in allocMore {x = da} a aa) ab (rewrite sym prf2 in allocMore {x = db} c ac))
                Right (Right ((da ** prf1), (db ** prf2))) => (sc ** AllocIf (rewrite sym prf1 in allocMore {x = da} a aa) (rewrite sym prf2 in allocMore {x = db} b ab) ac)
    allocExp (Call k xs) = let (slots ** prf) = allocList xs in (slots ** AllocCall prf)
    allocExp (CallVirt a b c) =
        let
            (sa ** aa) = allocExp a
            (sb ** ab) = allocExp b
            (sc ** ac) = allocExp c
        in
            case diff3 sa sb sc of
                Left ((da ** prf1), (db ** prf2)) => (sa ** AllocCallVirt aa (rewrite sym prf1 in allocMore {x = da} b ab) (rewrite sym prf2 in allocMore {x = db} c ac))
                Right (Left ((da ** prf1), (db ** prf2))) => (sb ** AllocCallVirt (rewrite sym prf1 in allocMore {x = da} a aa) ab (rewrite sym prf2 in allocMore {x = db} c ac))
                Right (Right ((da ** prf1), (db ** prf2))) => (sc ** AllocCallVirt (rewrite sym prf1 in allocMore {x = da} a aa) (rewrite sym prf2 in allocMore {x = db} b ab) ac)
    allocExp (Binop op a b) =
        let
            (sa ** aa) = allocExp a
            (sb ** ab) = allocExp b
        in
            case diff sa sb of
                Left (d ** prf) => (sb ** AllocBinop (rewrite sym prf in allocMore {x = d} a aa) ab)
                Right (d ** prf) => (sa ** AllocBinop aa (rewrite prf in allocMore {x = d} b ab))

    allocList [] = (0 ** AllocNil)
    allocList (e :: es) =
        let
            (se ** ae) = allocExp e
            (ses ** aes) = allocList es
        in
            case diff se ses of
                Left (d ** prf) => (ses ** AllocCons (rewrite sym prf in allocMore {x = d} e ae) aes)
                Right (d ** prf) => (se ** AllocCons ae (rewrite prf in allocMoreList {x = d} es aes))


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
