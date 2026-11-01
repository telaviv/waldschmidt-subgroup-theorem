/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVar5dRat

/-!
# A5.9h: W88 §5d for `G_a^{d₀} × G_m^{d₁} × A^r`, unconditionally

**`hyperplaneKappaAbVar : HyperplaneKappaAbVar`**: `hyperplaneKappaAbVar_of_ratTangents` with γ's `ratTangentsA`
(`abTan_qbar`). The chain: `multEstB_holds` (α, β) → `theorem41B_of` (§7) → `hyperplaneKappaB_of_ME` (§5d engine:
Lemmas 5.1/5.2, `trans41B`, Roy, pivot) → `hyperplaneKappaAbVar_of_rat` (A-block, `TanA` coordinates) → `hratA_of`.
**`thm11KappaA5`**: `lean_mstar`'s Theorem A hypothesis for `B(1/5,1/5)` via `thm11KappaA5_of`.
-/

namespace LSG.W88

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × A^r` on toric-injective hyperplanes**, unconditionally. -/
theorem hyperplaneKappaAbVar : HyperplaneKappaAbVar :=
  hyperplaneKappaAbVar_of_ratTangents ratTangentsA

/-- **`lean_mstar`'s `Thm11KappaA` for `Jac(y⁵ = x(1 − x))`**, unconditionally. -/
theorem thm11KappaA5 : MStarCopy.Thm11KappaA 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 0 :=
  thm11KappaA5_of hyperplaneKappaAbVar

end LSG.W88
