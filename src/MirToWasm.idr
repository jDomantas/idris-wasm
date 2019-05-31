module MirToWasm

import Data.Fin
import Data.List
import Trans
import Mir
import Wasm

%default total

localList : (count : Nat) -> List Wasm.ValueType
localList Z = []
localList (S x) = I32 :: localList x

localListSize : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + b = c) -> (localList a ++ localList b = localList c)
localListSize Z b c prf = rewrite prf in Refl
localListSize (S _) _ Z Refl impossible
localListSize (S a) b (S c) prf = rewrite localListSize a b c (succInjective (a + b) c prf) in Refl

translateDecl : MDef -> FuncType
translateDecl def = MkFuncType (localList (args def)) (Some I32)

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
        -- we need to remember where the object that we are currently
        -- initializing is, because fields might want to create new objects too
        AllocCreate : Fin slots -> AllocExp t slots -> AllocList fields slots -> AllocExp (Create t fields) slots
        AllocField : AllocExp o slots -> AllocExp f slots -> AllocExp (Field o f) slots
        AllocTag : AllocExp o slots -> AllocExp (Tag o) slots
        AllocIf : AllocExp c slots -> AllocExp t slots -> AllocExp e slots -> AllocExp (If c t e) slots
        AllocCall : AllocList args slots -> AllocExp (Call f args) slots
        AllocCallVirt : AllocExp f slots -> AllocExp a slots -> AllocExp b slots -> AllocExp (CallVirt f a b) slots
        AllocBinop : AllocExp a slots -> AllocExp b slots -> AllocExp (Binop op a b) slots
        AllocCrash : AllocExp Crash slots

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
    allocMore {x} {slots} (Local idx) (AllocLocal place) =
        AllocLocal
            (rewrite plusCommutative x slots in weakenN x place)
    allocMore {x} {slots} (Let v e) (AllocLet place a b) =
        AllocLet
            (rewrite plusCommutative x slots in weakenN x place)
            (allocMore v a)
            (allocMore e b)
    allocMore {x} {slots} (Create t fields) (AllocCreate place y z) =
        AllocCreate
            (rewrite plusCommutative x slots in weakenN x place)
            (allocMore t y)
            (allocMoreList fields z)
    allocMore (Field o f) (AllocField x y) = AllocField (allocMore o x) (allocMore f y)
    allocMore (Tag o) (AllocTag x) = AllocTag (allocMore o x)
    allocMore (If c t e) (AllocIf x y z) = AllocIf (allocMore c x) (allocMore t y) (allocMore e z)
    allocMore (Call f args) (AllocCall x) = AllocCall (allocMoreList args x)
    allocMore (CallVirt f a b) (AllocCallVirt x y z) = AllocCallVirt (allocMore f x) (allocMore a y) (allocMore b z)
    allocMore (Binop op a b) (AllocBinop x y) = AllocBinop (allocMore a x) (allocMore b y)
    allocMore Crash AllocCrash = AllocCrash

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
flip {lim = (S k)} FZ = last {n = k}
flip {lim = (S k)} (FS x) = weaken (flip {lim = k} x)

finToNatLast : (k : Nat) -> (finToNat (last {n = k})) = k
finToNatLast Z = Refl
finToNatLast (S k) = rewrite finToNatLast k in Refl

finToNatWeaken : (x : Fin lim) -> (finToNat (weaken x) = finToNat x)
finToNatWeaken FZ = Refl
finToNatWeaken (FS x) = rewrite finToNatWeaken x in Refl

-- flip should change number x in range [0; n - 1] to number n - 1 - x
flipTotal : {lim : Nat} -> (x : Fin lim) -> (1 + finToNat x + finToNat (flip x) = lim)
flipTotal {lim = Z} FZ impossible
flipTotal {lim = Z} (FS _) impossible
flipTotal {lim = (S k)} FZ = rewrite finToNatLast k in Refl
flipTotal {lim = (S k)} (FS x) =
    rewrite finToNatWeaken (flip x) in
    rewrite flipTotal {lim = k} x in
        Refl

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
    insertSlot idx (AllocCreate x y z) = AllocCreate (insertSlotFin idx x) (insertSlot idx y) (insertSlotList idx z)
    insertSlot idx (AllocField x y) = AllocField (insertSlot idx x) (insertSlot idx y)
    insertSlot idx (AllocTag x) = AllocTag (insertSlot idx x)
    insertSlot idx (AllocIf x y z) = AllocIf (insertSlot idx x) (insertSlot idx y) (insertSlot idx z)
    insertSlot idx (AllocCall x) = AllocCall (insertSlotList idx x)
    insertSlot idx (AllocCallVirt x y z) = AllocCallVirt (insertSlot idx x) (insertSlot idx y) (insertSlot idx z)
    insertSlot idx (AllocBinop x y) = AllocBinop (insertSlot idx x) (insertSlot idx y)
    insertSlot idx AllocCrash = AllocCrash

mutual
    allocExp : {locals : Nat} -> (exp : MExp ty locals) -> (slots : Nat ** AllocExp exp slots)
    allocList : {locals : Nat} -> (exps : List (MExp ty locals)) -> (slots : Nat ** AllocList exps slots)

    allocExp (Const x) = (0 ** AllocConst)
    allocExp {locals} (Local x) = (locals ** AllocLocal (flip x))
    allocExp {locals} (Let a b) =
        let
            (sa ** aa) = allocExp a
            (sb ** ab) = allocExp b
            place = last {n = locals}
        in
            case diff3 (S locals) sa sb of
                Left ((da ** prf1), (db ** prf2)) => (S locals **
                    AllocLet
                        place
                        (rewrite sym prf1 in allocMore {x = da} a aa)
                        (rewrite sym prf2 in allocMore {x = db} b ab))
                Right (Left ((da ** prf1), (db ** prf2))) => (sa **
                    AllocLet
                        (rewrite sym prf1 in rewrite plusCommutative da (S locals) in weakenN da place)
                        aa
                        (rewrite sym prf2 in allocMore {x = db} b ab))
                Right (Right ((da ** prf1), (db ** prf2))) => (sb **
                    AllocLet
                        (rewrite sym prf1 in rewrite plusCommutative da (S locals) in weakenN da place)
                        (rewrite sym prf2 in allocMore {x = db} a aa)
                        ab)
    allocExp {locals} (Create x xs) =
        let
            (sx ** axf) = allocExp x
            (sxs ** axsf) = allocList xs
            ax = insertSlot locals axf
            axs = insertSlotList locals axsf
            place = last {n = locals}
        in
            case diff3 (S locals) (S sx) (S sxs) of
                Left ((da ** prf1), (db ** prf2)) => (S locals **
                    AllocCreate
                        place
                        (rewrite sym prf1 in allocMore {x = da} x ax)
                        (rewrite sym prf2 in allocMoreList {x = db} xs axs))
                Right (Left ((da ** prf1), (db ** prf2))) => (S sx **
                    AllocCreate
                        (rewrite sym prf1 in rewrite plusCommutative da (S locals) in weakenN da place)
                        ax
                        (rewrite sym prf2 in allocMoreList {x = db} xs axs))
                Right (Right ((da ** prf1), (db ** prf2))) => (S sxs **
                    AllocCreate
                        (rewrite sym prf1 in rewrite plusCommutative da (S locals) in weakenN da place)
                        (rewrite sym prf2 in allocMore {x = db} x ax)
                        axs)
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
    allocExp Crash = (0 ** AllocCrash)

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
    HasSlotsZ : HasSlots Z (MkCodeCtx functions locals)
    HasSlotsS :
        HasSlots s (MkCodeCtx functions locals) ->
        HasSlots (S s) (MkCodeCtx functions (I32 :: locals))

hasLocal :
    {slots : Nat} ->
    {ctx : CodeCtx} ->
    (prf : HasSlots slots ctx) ->
    (idx : Fin slots) ->
    HasLocal ctx (finToNat idx) I32
hasLocal {slots = Z} {ctx = (MkCodeCtx _ _)} HasSlotsZ FZ impossible
hasLocal {slots = Z} {ctx = (MkCodeCtx _ _)} HasSlotsZ (FS _) impossible
hasLocal {slots = (S s)} {ctx = (MkCodeCtx functions (I32 :: xs))} (HasSlotsS x) FZ = HasLocalHere
hasLocal {slots = (S s)} {ctx = (MkCodeCtx functions (I32 :: xs))} (HasSlotsS x) (FS y) = HasLocalThere (hasLocal x y)

callType : List (MExp Obj locals) -> FuncType
callType [] = MkFuncType [] (Some I32)
callType (a :: as) =
    let
        (MkFuncType args ret) = callType as
    in
        MkFuncType (I32 :: args) ret

findFunction : (ctx : CodeCtx) -> (idx : Nat) -> Trans (ty : FuncType ** HasFunc ctx idx ty)
findFunction (MkCodeCtx [] locals) _ = abort "call index is out of bounds"
findFunction (MkCodeCtx (f :: fs) locals) Z = pure (f ** HasFuncHere)
findFunction (MkCodeCtx (f :: fs) locals) (S x) = do
    (ty ** prf) <- findFunction (MkCodeCtx fs locals) x
    pure (ty ** HasFuncThere prf)

mutual
    translateObjectCreation :
        {slots : Nat} ->
        {ctx : CodeCtx} ->
        (hasSlots : HasSlots slots ctx) ->
        (fields : List (MExp Obj locals)) ->
        (alloc : AllocList fields slots) ->
        (setField : Instr ctx (Some I32) -> Instr ctx None) ->
        (finish : Instr ctx ty) ->
        Trans (Instr ctx ty)
    translateWithAlloc :
        {slots : Nat} ->
        {ctx : CodeCtx} ->
        (hasSlots : HasSlots slots ctx) ->
        (exp : MExp ty locals) ->
        (alloc : AllocExp exp slots) ->
        Trans (Instr ctx (Some I32))
    translateCall :
        {ctx : CodeCtx} ->
        (fn : Nat) ->
        (args : List (MExp Obj locals)) ->
        (alloc : AllocList args slots) ->
        (hasSlots : HasSlots slots ctx) ->
        Trans (Instr ctx (Some I32))

    translateObjectCreation hasSlots [] AllocNil setField finish = pure finish
    translateObjectCreation hasSlots (x :: xs) (AllocCons ax axs) setField finish = do
        field <- translateWithAlloc hasSlots x ax
        rest <- translateObjectCreation hasSlots xs axs setField finish
        pure (Chain (setField field) rest)

    translateWithAlloc hasSlots (Const x) AllocConst = pure (Const (ValueI32 x))
    translateWithAlloc hasSlots (Local x) (AllocLocal a) = pure (LocalGet (finToNat a) {prf = hasLocal hasSlots a})
    translateWithAlloc hasSlots (Let x y) (AllocLet a b c) = do
        init <- translateWithAlloc hasSlots x b
        body <- translateWithAlloc hasSlots y c
        pure (Chain
            (LocalSet (finToNat a) {prf = hasLocal hasSlots a} init)
            body)
    translateWithAlloc {ctx} hasSlots (Create x xs) (AllocCreate a b c) = do
        tag <- translateWithAlloc hasSlots x b
        let size = length xs * 4 + 4
        -- size in pages rounded up
        -- proper way to do this is (divNatNZ (size + 65535) 65536 SIsNotZ),
        -- but that takes forever to typecheck
        let sizeInPages = assert_total (div (size + 65535) 65536)
        -- check how much memory we have left
        let getSize = Wasm.Binop {ctx = ctx} MulInt MemorySize (Const (ValueI32 65536))
        let getRemaining = Binop SubInt getSize GlobalGet
        -- grow by sizeInPages if not enough
        let needToGrow = Relop (LtInt Unsigned) getRemaining (Const (ValueI32 (toIntegerNat size)))
        let grow = Wasm.If None needToGrow (Drop (MemoryGrow (Const (ValueI32 (toIntegerNat sizeInPages))))) Empty
        -- allocate: set local and increase global by size
        let allocate = Chain
            (LocalSet (finToNat a) {prf = hasLocal hasSlots a} GlobalGet)
            (GlobalSet (Binop AddInt GlobalGet (Const (ValueI32 (toIntegerNat size)))))
        let advanceMarker = LocalSet (finToNat a) {prf = hasLocal hasSlots a}
            (Binop AddInt
                (Const (ValueI32 4))
                (LocalGet (finToNat a) {prf = hasLocal hasSlots a}))
        let initTag = Chain
            (Store tag (LocalGet (finToNat a) {prf = hasLocal hasSlots a}))
            advanceMarker
        let setField = \val => Chain
            (Store val (LocalGet (finToNat a) {prf = hasLocal hasSlots a}))
            advanceMarker
        let prep = Chain grow (Chain allocate initTag)
        let finish = Binop SubInt
            (LocalGet (finToNat a) {prf = hasLocal hasSlots a})
            (Const (ValueI32 (toIntegerNat size)))
        creation <- translateObjectCreation hasSlots xs c setField finish
        pure (Chain prep creation)
    translateWithAlloc hasSlots (Field x y) (AllocField a b) = do
        obj <- translateWithAlloc hasSlots x a
        idx <- translateWithAlloc hasSlots y b
        let offset = Wasm.Binop MulInt (Const (ValueI32 4)) idx
        let withTagOffset = Wasm.Binop AddInt (Const (ValueI32 4)) offset
        let addr = Wasm.Binop AddInt obj withTagOffset
        pure (Load addr)
    translateWithAlloc hasSlots (Tag x) (AllocTag y) = do
        objAddr <- translateWithAlloc hasSlots x y
        pure (Load objAddr)
    translateWithAlloc hasSlots (If x y z) (AllocIf a b c) = do
        cond <- translateWithAlloc hasSlots x a
        t <- translateWithAlloc hasSlots y b
        e <- translateWithAlloc hasSlots z c
        pure (If (Some I32) cond t e)
    translateWithAlloc hasSlots (Call fn args) (AllocCall x) = translateCall fn args x hasSlots
    translateWithAlloc hasSlots (CallVirt x y z) (AllocCallVirt a b c) = do
        fn <- translateWithAlloc hasSlots x a
        arg1 <- translateWithAlloc hasSlots y b
        arg2 <- translateWithAlloc hasSlots z c
        pure (CallIndirect fn arg1 arg2)
    translateWithAlloc hasSlots (Binop Add y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Binop AddInt lhs rhs)
    translateWithAlloc hasSlots (Binop Sub y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Binop SubInt lhs rhs)
    translateWithAlloc hasSlots (Binop Mul y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Binop MulInt lhs rhs)
    translateWithAlloc hasSlots (Binop Div y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        -- we actually don't know if this is supposed to be signed or unsigned
        -- division, so just assume signed because we just keep assuming that
        -- stuff won't overflow anyways
        pure (Binop (DivInt Signed) lhs rhs)
    translateWithAlloc hasSlots (Binop Rem y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Binop (RemInt Signed) lhs rhs)
    translateWithAlloc hasSlots (Binop Eq y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Relop EqInt lhs rhs)
    translateWithAlloc hasSlots (Binop Ne y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Relop NeInt lhs rhs)
    translateWithAlloc hasSlots (Binop Lt y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Relop (LtInt Signed) lhs rhs)
    translateWithAlloc hasSlots (Binop Le y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Relop (LeInt Signed) lhs rhs)
    translateWithAlloc hasSlots (Binop Gt y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Relop (GtInt Signed) lhs rhs)
    translateWithAlloc hasSlots (Binop Ge y z) (AllocBinop a b) = do
        lhs <- translateWithAlloc hasSlots y a
        rhs <- translateWithAlloc hasSlots z b
        pure (Relop (GeInt Signed) lhs rhs)
    translateWithAlloc hasSlots Crash AllocCrash = pure Unreachable

    translateCallArgs :
        {ctx : CodeCtx} ->
        (args : List (MExp Obj locals)) ->
        (types : List ValueType) ->
        (alloc : AllocList args slots) ->
        (hasSlots : HasSlots slots ctx) ->
        Trans (CallParams ctx types)
    translateCallArgs [] [] _ _ = pure ParamsNil
    translateCallArgs (_ :: _) [] _ _ = abort "call with too many params"
    translateCallArgs [] (_ :: _) _ _ = abort "call missing params"
    translateCallArgs (p :: ps) (I32 :: ts) (AllocCons a as) hasSlots = do
        arg <- translateWithAlloc hasSlots p a
        rest <- translateCallArgs ps ts as hasSlots
        pure (ParamsCons arg rest)

    translateCall {ctx} fn argList alloc hasSlots = do
        (MkFuncType args (Some I32) ** prf) <- findFunction ctx fn
            | _ => abort "calling a function that does not return anything"
        args' <- translateCallArgs argList args alloc hasSlots
        pure (Call fn {prf = prf} args')

proveHasSlots : (slots : Nat) -> HasSlots slots (MkCodeCtx functions (localList slots))
proveHasSlots Z = HasSlotsZ
proveHasSlots (S x) = HasSlotsS (proveHasSlots x)

mangleProofIntoShape : {a : Nat} -> {b : Nat} -> {c : Nat} -> (c = a + b) -> (b + a = c)
mangleProofIntoShape {a} {b} prf = rewrite plusCommutative b a in sym prf

translateDef :
    (ctx : FunctionCtx) ->
    (def : MDef) ->
    Trans (Function ctx (MkFuncType (localList (args def)) (Some I32)))
translateDef ctx (MkMDef argCount body) =
    let
        (slots ** alloc) = allocExp body
    in
        case diff slots argCount of
            -- we have more parameters than the required amount of slots,
            -- so we expand slot count to arg count
            Left (extraSlots ** prf) => do
                let expanded = allocMore {x = extraSlots} {slots = slots} body alloc
                let hasSlots = proveHasSlots argCount
                translatedBody <- translateWithAlloc
                    {slots = argCount}
                    {ctx = MkCodeCtx (functions ctx) (localList argCount)}
                    hasSlots
                    body
                    (rewrite sym prf in expanded)
                pure (MkFunction
                    []
                    (rewrite appendNilRightNeutral (localList argCount) in translatedBody))
            -- we need some extra slots for locals that are not args,
            -- and the correct slot allocation is given by `alloc`
            Right (nonArgLocals ** prf) => do
                let hasSlots = proveHasSlots slots
                translatedBody <- translateWithAlloc
                    {slots = slots}
                    {ctx = MkCodeCtx (functions ctx) (localList slots)}
                    hasSlots
                    body
                    alloc
                pure (MkFunction
                    (localList nonArgLocals)
                    (rewrite localListSize argCount nonArgLocals slots (mangleProofIntoShape prf) in translatedBody))

translateDefsGo :
    (ctx : FunctionCtx) ->
    (defs : List MDef) ->
    Trans (Functions ctx (translateDecls defs))
translateDefsGo ctx [] = pure FunctionsNil
translateDefsGo ctx (d :: ds) = pure (FunctionsCons !(translateDef ctx d) !(translateDefsGo ctx ds))

translateDefs : (defs : List MDef) -> Trans (Functions (MkFunctionCtx (translateDecls defs)) (translateDecls defs))
translateDefs defs = translateDefsGo (MkFunctionCtx (translateDecls defs)) defs

translateMain : (defs : List MDef) -> Fin (length defs) -> Fin (length (translateDecls defs))
translateMain [] FZ impossible
translateMain [] (FS _) impossible
translateMain (d :: ds) FZ = FZ
translateMain (d :: ds) (FS x) = FS (translateMain ds x)

export
translateModule : Mir.Module -> Trans Wasm.Module
translateModule (MkModule defs main) =
    let
        wasmDecls = translateDecls defs
    in
        pure (MkModule
            wasmDecls
            !(translateDefs defs)
            (makeTable (length wasmDecls))
            (translateMain defs main))
