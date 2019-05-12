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
        AllocLocal : Fin slots -> AllocExp (Local idx) slots
        AllocLet : Fin slots -> AllocExp v slots -> AllocExp e slots -> AllocExp (Let v e) slots
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
    allocMore {x = x} {slots = slots} (Local idx) (AllocLocal place) =
        AllocLocal
            (rewrite plusCommutative x slots in weakenN x place)
    allocMore {x = x} {slots = slots} (Let v e) (AllocLet place a b) =
        AllocLet
            (rewrite plusCommutative x slots in weakenN x place)
            (allocMore v a)
            (allocMore e b)
    allocMore (Create t fields) (AllocCreate x y) = AllocCreate (allocMore t x) (allocMoreList fields y)
    allocMore (Field o f) (AllocField x y) = AllocField (allocMore o x) (allocMore f y)
    allocMore (Tag o) (AllocTag x) = AllocTag (allocMore o x)
    allocMore (If c t e) (AllocIf x y z) = AllocIf (allocMore c x) (allocMore t y) (allocMore e z)
    allocMore (Call f args) (AllocCall x) = AllocCall (allocMoreList args x)
    allocMore (CallVirt f a b) (AllocCallVirt x y z) = AllocCallVirt (allocMore f x) (allocMore a y) (allocMore b z)
    allocMore (Binop op a b) (AllocBinop x y) = AllocBinop (allocMore a x) (allocMore b y)

-- Returns which value is bigger and the difference between them.
-- In retrospect, it would have been better to just return ((a, b) ** a + x = b + y),
-- so that you wouldn't need to match and do different rewrites in the two cases.
diff : (x : Nat) -> (y : Nat) -> Either (a ** a + x = y) (a ** x = a + y)
diff Z y = Left (y ** rewrite plusZeroRightNeutral y in Refl)
diff x Z = Right (x ** rewrite plusZeroRightNeutral x in Refl)
diff (S x) (S y) = case diff x y of
    Left (a ** prf) => Left (a ** rewrite sBeforePlus a x in eqSucc (plus a x) y prf)
    Right (a ** prf) => Right (a ** rewrite sBeforePlus a y in eqSucc x (plus a y) prf)

-- And especially here, a return of ((a, b, c, max) ** (a + x = max, b + y = max, c + z = max))
-- would have been so much better.
-- But this works, so there's no reason to waste time simplifying it.
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

flip : {lim : Nat} -> (x : Fin lim) -> Fin lim
flip {lim = Z} FZ impossible
flip {lim = Z} (FS _) impossible
flip {lim = (S k)} FZ = last
flip {lim = (S k)} (FS x) = shift 1 (flip {lim = k} x)

insertSlotFin : (idx : Nat) -> Fin slots -> Fin (S slots)
insertSlotFin Z x = FS x
insertSlotFin (S k) FZ = FZ
insertSlotFin (S k) (FS x) = FS (insertSlotFin k x)

mutual
    insertSlot : (idx : Nat) -> AllocExp exp slots -> AllocExp exp (S slots)
    insertSlotList : (idx : Nat) -> AllocList exps slots -> AllocList exps (S slots)
    
    insertSlotList idx AllocNil = AllocNil
    insertSlotList idx (AllocCons x y) = AllocCons (insertSlot idx x) (insertSlotList idx y)

    insertSlot idx AllocConst = AllocConst
    insertSlot idx (AllocLocal y) = AllocLocal (insertSlotFin idx y)
    insertSlot idx (AllocLet x y z) = AllocLet (insertSlotFin idx x) (insertSlot idx y) (insertSlot idx z)
    insertSlot idx (AllocCreate x y) = AllocCreate (insertSlot idx x) (insertSlotList idx y)
    insertSlot idx (AllocField x y) = AllocField (insertSlot idx x) (insertSlot idx y)
    insertSlot idx (AllocTag x) = AllocTag (insertSlot idx x)
    insertSlot idx (AllocIf x y z) = AllocIf (insertSlot idx x) (insertSlot idx y) (insertSlot idx z)
    insertSlot idx (AllocCall x) = AllocCall (insertSlotList idx x)
    insertSlot idx (AllocCallVirt x y z) = AllocCallVirt (insertSlot idx x) (insertSlot idx y) (insertSlot idx z)
    insertSlot idx (AllocBinop x y) = AllocBinop (insertSlot idx x) (insertSlot idx y)

mutual
    allocExp : {locals : Nat} -> (exp : MExp ty locals) -> (slots : Nat ** AllocExp exp slots)
    allocList : {locals : Nat} -> (exps : List (MExp ty locals)) -> (slots : Nat ** AllocList exps slots)

    allocExp (Const x) = (0 ** AllocConst)
    allocExp {locals = locals} (Local x) = (locals ** AllocLocal (flip x))
    allocExp {locals = locals} (Let a b) =
        let
            (sa ** aaf) = allocExp a
            (sb ** ab) = allocExp b
            aa = insertSlot locals aaf
            place = last {n = locals}
        in
            case diff3 (S locals) (S sa) sb of
                Left ((da ** prf1), (db ** prf2)) => (S locals ** AllocLet place (rewrite sym prf1 in allocMore {x = da} a aa) (rewrite sym prf2 in allocMore {x = db} b ab))
                Right (Left ((da ** prf1), (db ** prf2))) => (S sa **
                    AllocLet
                        (rewrite sym prf1 in rewrite plusCommutative da (S locals) in weakenN da place)
                        aa
                        (rewrite sym prf2 in allocMore {x = db} b ab))
                Right (Right ((da ** prf1), (db ** prf2))) => (sb **
                    AllocLet
                        (rewrite sym prf1 in rewrite plusCommutative da (S locals) in weakenN da place)
                        (rewrite sym prf2 in allocMore {x = db} a aa)
                        ab)
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

data HasSlots : (slots : Nat) -> (ctx : CodeCtx) -> Type where
    HasSlotsZ : HasSlots Z (MkCodeCtx functions types locals return)
    HasSlotsS :
        HasSlots s (MkCodeCtx functions types locals return) ->
        HasSlots (S x) (MkCodeCtx functions types (I32 :: locals) return)

hasLocal :
    {slots : Nat} ->
    {ctx : CodeCtx} ->
    (prf : HasSlots slots ctx) ->
    (idx : Fin slots) ->
    HasLocal ctx (finToNat idx) I32
hasLocal prf idx = ?hasLocal_rhs

translateWithAlloc :
    {slots : Nat} ->
    {ctx : CodeCtx} ->
    (hasSlots : HasSlots slots ctx) ->
    (exp : MExp ty locals) ->
    (alloc : AllocExp exp slots) ->
    Instr ctx (Some I32)
translateWithAlloc hasSlots (Const x) AllocConst = Const (ValueI32 x)
translateWithAlloc hasSlots (Local x) (AllocLocal a) = LocalGet (finToNat a) {v = hasLocal hasSlots a}
translateWithAlloc hasSlots (Let x y) (AllocLet a b c) =
    let
        init = translateWithAlloc hasSlots x b
        body = translateWithAlloc hasSlots y c
    in
        Chain
            (LocalSet (finToNat a) {v = hasLocal hasSlots a} init)
            body
translateWithAlloc hasSlots (Create x xs) alloc = ?translate_create
translateWithAlloc hasSlots (Field x y) (AllocField a b) =
    let
        obj = translateWithAlloc hasSlots x a
        idx = translateWithAlloc hasSlots y b
        offset = Wasm.Binop MulInt (Const (ValueI32 4)) idx
        addr = Wasm.Binop AddInt obj offset
    in
        Load addr
translateWithAlloc hasSlots (Tag x) (AllocTag y) =
    let
        objAddr = translateWithAlloc hasSlots x y
    in
        Load objAddr
translateWithAlloc hasSlots (If x y z) (AllocIf a b c) =
    let
        cond = translateWithAlloc hasSlots x a
        t = translateWithAlloc hasSlots y b
        e = translateWithAlloc hasSlots z c
    in
        If (Some I32) cond t e
translateWithAlloc hasSlots (Call k xs) alloc = ?translate_call
translateWithAlloc hasSlots (CallVirt x y z) (AllocCallVirt a b c) =
    let
        fn = translateWithAlloc hasSlots x a
        arg1 = translateWithAlloc hasSlots y b
        arg2 = translateWithAlloc hasSlots z c
    in
        ?callvirt_impl
translateWithAlloc hasSlots (Binop Add y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        Binop AddInt lhs rhs
translateWithAlloc hasSlots (Binop Sub y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        Binop SubInt lhs rhs
translateWithAlloc hasSlots (Binop Mul y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        Binop MulInt lhs rhs
translateWithAlloc hasSlots (Binop Div y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        -- we actually don't know if this is supposed to be signed or unsigned
        -- division, so just assume signed because we just keep assuming that
        -- stuff won't overflow
        Binop (DivInt Signed) lhs rhs
translateWithAlloc hasSlots (Binop Rem y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        -- same as above
        Binop (RemInt Signed) lhs rhs
translateWithAlloc hasSlots (Binop Eq y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        Relop EqInt lhs rhs
translateWithAlloc hasSlots (Binop Ne y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        Relop NeInt lhs rhs
translateWithAlloc hasSlots (Binop Lt y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        -- save as above
        Relop (LtInt Signed) lhs rhs
translateWithAlloc hasSlots (Binop Le y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        -- save as above
        Relop (LeInt Signed) lhs rhs
translateWithAlloc hasSlots (Binop Gt y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        -- save as above
        Relop (GtInt Signed) lhs rhs
translateWithAlloc hasSlots (Binop Ge y z) (AllocBinop a b) =
    let
        lhs = translateWithAlloc hasSlots y a
        rhs = translateWithAlloc hasSlots z b
    in
        -- save as above
        Relop (GeInt Signed) lhs rhs

translateDef :
    (ctx : FunctionCtx) ->
    (def : MDef) ->
    Function ctx (MkFuncType (mkArgs (args def)) (Some I32))
translateDef ctx def = MkFunction [] (Const (ValueI32 0))

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
