/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.MEBV.MainPush
import LSG.MEBV.WustCosetB

/-!
# The vector-extension multiplicity estimate from the subgroup inputs

`multEstV_of : MEBVInputs → MultEstV`: α's `multEstV_of_wust` with β's Wüstholz lemma `wustInput`.
-/

namespace LSG.MEBV

/-- **`MultEstV` from the subgroup layer** (`MEBVInputs`). -/
theorem multEstV_of (hin : MEBVInputs) : MultEstV :=
  multEstV_of_wust hin fun _ _ _ _ => wustInput

end LSG.MEBV
