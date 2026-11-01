/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlock.Packages
import LSG.W88.AbVarSec7Defs

/-!
# The A-block packages in the form A5.7 consumes

* **`tayAll_aBlockW`**: `LSG.W88.TayAll (fun _ : Fin m => aBlock)` (STAGE_A5 §6.1);
* `aBlockAnF m : ∀ k : Fin m, AbBlockAn ((fun _ => aBlock) k)`, the constant package family.
-/

noncomputable section

namespace LSG.JacBlock

/-- **`TayAll` for the constant family `aBlock`.** -/
def tayAll_aBlockW (m : ℕ) : LSG.W88.TayAll (fun _ : Fin m => aBlock) := tayAll_aBlock m

/-- The constant analytic-package family. -/
def aBlockAnF (m : ℕ) : ∀ k : Fin m, LSG.AuxA.AbBlockAn ((fun _ : Fin m => aBlock) k) := fun _ => aBlockAn

end LSG.JacBlock
