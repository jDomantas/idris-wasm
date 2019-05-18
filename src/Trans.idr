module Trans

%default total
%access export

record Trans a where
    constructor MkTrans
    runTrans : String -> Either String a

run : Trans a -> String -> Either String a
run = runTrans

Functor Trans where
    map f fa = MkTrans (\ctx => map f (run fa ctx))

Applicative Trans where
    pure a = MkTrans (\_ => Right a)
    f <*> fa = MkTrans (\ctx => run f ctx <*> run fa ctx)

Monad Trans where
    join t = MkTrans (\ctx => run !(run t ctx) ctx)

inContext : (ctx : String) -> Trans a -> Trans a
inContext ctx trans = MkTrans (\_ => run trans ctx)

getContext : Trans String
getContext = MkTrans (\ctx => Right ctx)

abort : (msg : String) -> Trans a
abort msg = MkTrans (\_ => Left msg)
