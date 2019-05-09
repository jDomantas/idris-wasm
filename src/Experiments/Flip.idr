module Experiments.Flip

%default total

data Exp : Type where
    Num : Nat -> Exp
    Add : Exp -> Exp -> Exp

data Eval : Exp -> Nat -> Type where
    EvalNum : Eval (Num x) x
    EvalAdd : Eval a p -> Eval b q -> Eval (Add a b) (p + q)

eval : Exp -> Nat
eval (Num x) = x
eval (Add a b) = eval a + eval b

correctEval : (exp : Exp) -> Eval exp (eval exp)
correctEval (Num x) = EvalNum
correctEval (Add a b) = EvalAdd (correctEval a) (correctEval b)

correctEval2 : (exp : Exp) -> Eval exp x -> (eval exp = x)
correctEval2 (Num x) EvalNum = Refl
correctEval2 (Add a b) (EvalAdd ea eb) =
    rewrite correctEval2 a ea in
    rewrite correctEval2 b eb in
        Refl

rewriteFlip : Exp -> Exp
rewriteFlip (Num x) = Num x
rewriteFlip (Add a b) = Add (rewriteFlip b) (rewriteFlip a)

flipDoesNotChange : (exp : Exp) -> (eval exp = eval (rewriteFlip exp))
flipDoesNotChange (Num k) = Refl
flipDoesNotChange (Add x y) =
    rewrite flipDoesNotChange x in
    rewrite flipDoesNotChange y in
    rewrite plusCommutative (eval (rewriteFlip x)) (eval (rewriteFlip y)) in
        Refl

flipDoesNotChange2 : (exp : Exp) -> Eval exp a -> Eval (rewriteFlip exp) a
flipDoesNotChange2 (Num x) EvalNum = EvalNum
flipDoesNotChange2 (Add a b) (EvalAdd {p = p} {q = q} ea eb) =
    rewrite plusCommutative p q in
        EvalAdd (flipDoesNotChange2 b eb) (flipDoesNotChange2 a ea)
