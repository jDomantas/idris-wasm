module Codegen

import Data.Fin
import Data.Vect
import Trans
import Wasm
import WasmEmit
import WasmEmitText
import Mir
import MirToWasm
import TSExp
import TSExpToMir

export
translateToWasm : TSExp.Module -> Either String String
translateToWasm tsexp = run (do
    mir <- TSExpToMir.translateModule tsexp
    wasm <- MirToWasm.translateModule mir
    pure (WasmEmitText.emitModule wasm)) ""
