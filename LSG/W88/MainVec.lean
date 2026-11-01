/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7V
import LSG.MEV.MainVec4Gap

/-!
# `Theorem41VecLA` unconditionally

* **`LSG.MEV.multEstVec : LSG.MEV.MultEstVec`**: the multiplicity estimate for the
  vector-extension class, from the onto case (`multEstVec_of_surj`), the case `D₀ ≤ D₂`
  (`multEstVec_of_le`) and the 4-block estimate for the remaining case (`multEstVecGap`,
  STAGE5_MEV §10.3).
* **`LSG.W88.theorem41VecLA : LSG.W88.Vec.Theorem41VecLA`** (W88 §7 via
  `theorem41VecLA_of_ME`).
-/

namespace LSG.MEV

/-- **The multiplicity estimate `MultEstVec`.** -/
theorem multEstVec : MultEstVec := multEstVec_of_gap multEstVecGap

end LSG.MEV

/-- **W88 Theorem 4.1 for the class `𝒞` (linear-algebra form), unconditionally.** -/
theorem LSG.W88.theorem41VecLA : LSG.W88.Vec.Theorem41VecLA :=
  LSG.W88.theorem41VecLA_of_ME LSG.MEV.multEstVec

