module TSExpToMir

import TSExp
import Mir

export
translateModule : TSExp.Module -> Mir.Module
