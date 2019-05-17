module Main

import Data.Fin
import Wasm
import WasmEmit
import WasmEmitText
import Mir
import MirToWasm

mirModule : Mir.Module
mirModule =
    MkModule
        -- [MkMDef 1 (Create (Binop Mul (Const 3) (Tag (Local 0))) [])]
        -- [MkMDef 0 (Create (Const 123) [])]
        [MkMDef 1 (Local FZ)]
        FZ

wasmModule : Wasm.Module
wasmModule = MirToWasm.translateModule mirModule
    -- MkModule
    --     [MkFuncType [I32] (Some I32)]
    --     (FunctionsCons (MkFunction [] (Binop MulInt (LocalGet 0 {prf = HasLocalHere}) (Const (ValueI32 5)))) FunctionsNil)
    --     []
    --     FZ

bytes : List Int
bytes = WasmEmit.emitModule wasmModule

wat : String
wat = WasmEmitText.emitModule wasmModule

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
        | Left err => putStrLn "failed to open output.wasm.txt"
    Right () <- writeBytes bytes f
        | Left err => putStrLn "failed to write output.wasm.txt"
    Right f2 <- openFile "output.wat" WriteTruncate
        | Left err => putStrLn "failed to open output.wat"
    Right () <- fPutStr f2 wat
        | Left err => putStrLn "failed to write output.wat"
    putStrLn "done"
