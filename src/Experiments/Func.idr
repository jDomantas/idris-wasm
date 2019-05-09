module Experiments.Flip

import Data.List

%default total

Name : Type
Name = Nat

mutual
    data Exp : List Name -> Type where
        Val : Value -> Exp vars
        Add : Exp vars -> Exp vars -> Exp vars
        Lam : (x : Name) -> Exp (x :: vars) -> Exp vars
        App : Exp vars -> Exp vars -> Exp vars
        Var : Elem x vars -> Exp vars

    data Value : Type where
        Number : Nat -> Value
        Closure : (x : Name) -> Exp [x] -> Value

data LastElem : (list : List a) -> Elem x list -> Type where
    LastHere : LastElem [x] Here
    LastThere : LastElem xs later -> LastElem (x :: xs) (There later)

data ReplaceInExp : Exp (vars ++ [x]) -> Value -> Exp vars -> Type where
    ReplaceVal : ReplaceInExp (Val v) v2 (Val v)
    ReplaceAdd : ReplaceInExp x v x2 -> ReplaceInExp y v y2 -> ReplaceInExp (Add x y) v (Add x2 y2)
    ReplaceApp : ReplaceInExp x v x2 -> ReplaceInExp y v y2 -> ReplaceInExp (App x y) v (App x2 y2)
    ReplaceVar : LastElem (vars ++ [x]) var -> ReplaceInExp (Var {vars = vars ++ [x]} var) v (Val v)

data Eval : Exp [] -> Value -> Type where
    EvalVal : Eval (Val x) x
    EvalAdd : Eval a (Number p) -> Eval b (Number q) -> Eval (Add a b) (Number (p + q))
    EvalLam : Eval (Lam name body) (Closure name body)
    EvalApp : Eval f (Closure name body) -> Eval x v -> ReplaceInExp body v body2 -> Eval body2 result -> Eval (App f x) result

embedElem : Elem el (inner ++ outer) -> Elem el (inner ++ fresh :: outer)
embedElem {inner = []} e = There e
embedElem {inner = (x :: xs)} Here = Here
embedElem {inner = (x :: xs)} (There later) = There (embedElem later)

embed : Exp (inner ++ outer) -> Exp (inner ++ x :: outer)
embed (Val x) = Val x
embed (Add a b) = Add (embed a) (embed b)
embed {inner = inner} {outer = outer} (Lam a b) = Lam a (embed {inner = a :: inner} {outer = outer} b)
embed (App a b) = App (embed a) (embed b)
embed (Var y) = Var (embedElem y)

expand : Exp [] -> Exp []
expand exp = App (Lam 0 (embed {inner = []} {outer = []} exp)) (Val (Number 0))

expandDoesNotChangeResult : (exp : Exp []) -> Eval exp val -> Eval (expand exp) val
