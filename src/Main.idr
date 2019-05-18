module Main

import Data.Fin
import Trans
import Wasm
import WasmEmit
import WasmEmitText
import Mir
import MirToWasm
import TSExp
import TSExpToMir

mirModule : Mir.Module
mirModule =
    MkModule
        [MkMDef 1
            (Let
                (Create (Const 1) [])
                (Create (Tag (Local 1)) [Local 1, Local 0]))]
        FZ

wasmModule : Trans Wasm.Module
wasmModule = MirToWasm.translateModule mirModule

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
main = case run wasmModule "" of
    Left err => do
        putStrLn "failed to translate mir to wasm"
        putStrLn err
    Right mod => do
        Right f <- openFile "output.wasm.txt" WriteTruncate
            | Left err => putStrLn "failed to open output.wasm.txt"
        Right () <- writeBytes (WasmEmit.emitModule mod) f
            | Left err => putStrLn "failed to write output.wasm.txt"
        Right f2 <- openFile "output.wat" WriteTruncate
            | Left err => putStrLn "failed to open output.wat"
        Right () <- fPutStr f2 (WasmEmitText.emitModule mod)
            | Left err => putStrLn "failed to write output.wat"
        putStrLn "done"
