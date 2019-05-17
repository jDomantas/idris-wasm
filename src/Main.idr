module Main

import Data.Fin
import Wasm
import WasmEmit
import Mir
import MirToWasm

wasmModule : Wasm.Module
wasmModule =
    MkModule
        [MkFuncType [I32] (Some I32)]
        (FunctionsCons (MkFunction [] (Binop MulInt (LocalGet 0 {prf = HasLocalHere}) (Const (ValueI32 5)))) FunctionsNil)
        []
        FZ

bytes : List Int
bytes = emitModule wasmModule

showByte : Int -> String
showByte x = nibble (x `div` 16) ++ nibble (x `mod` 16) ++ "  "
    where
        nibble2 : Int -> Char
        nibble2 x = if x < 10 then cast (x + 48) else cast (x + 55)
        nibble : Int -> String
        nibble x = singleton (nibble2 x)

writeBytes : List Int -> File -> IO (Either FileError ())
writeBytes [] file = pure (Right ())
writeBytes (x :: xs) file = do
    Right () <- fPutStr file (showByte x)
        | Left err => pure (Left err)
    writeBytes xs file

main : IO ()
main = do
    Right f <- openFile "output.wasm.txt" WriteTruncate
        | Left err => putStrLn "failed to open"
    Right () <- writeBytes bytes f
        | Left err => putStrLn "failed to write"
    putStrLn "done"
