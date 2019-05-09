module Translate

import BExp
import IR

%default total

translate : List BDef -> List IDef
translate _ = []

main : IO ()
main = putStrLn "Hello, world"
