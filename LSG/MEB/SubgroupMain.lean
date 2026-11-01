/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.SubgroupData
import LSG.MEB.HilbH0
import LSG.MEB.Main

/-!
# `MEBInputs`, and hence `MultEstB` (A4.3 + A4.5; β″ with α′'s `h0LowerBound`)

* **`mebInputs : MEBInputs`**: β″'s `SubgroupData.ofLower` (every field of `SubgroupData` except `coset_ge`, built in
  `SubgroupData.lean`) with α′'s unsliced Hilbert lower bound `h0LowerBound O : H0LowerBound O (cHB B)`
  (`HilbH0.lean`), through `mebInputs_of_lower`. The constant is `cL = cHB B · nLaw B · 2^m`.
* **`multEstB_holds : MultEstB`**: α's `multEstB_of mebInputs`.
-/

namespace LSG.MEB

/-- **The inputs of the assembly**, for every family of blocks. -/
theorem mebInputs : MEBInputs :=
  mebInputs_of_lower fun _ _ _ B => ⟨cHB B, one_le_cHB, h0LowerBound⟩

/-- **The multiplicity estimate on `G_a^{d₀} × G_m^{d₁} × B₁ × ⋯ × B_m`.** -/
theorem multEstB_holds : MultEstB := multEstB_of mebInputs

end LSG.MEB
