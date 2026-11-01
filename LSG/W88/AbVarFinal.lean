/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVar5dFinal
import LSG.W88.AbVarMStarK

/-!
# lean_mstar's abelian-variety hypotheses for `y⁵ = x(1 − x)`, unconditionally

* `thm11KappaA5`: `Thm11KappaA 5 2 (·+1) perA5 0` (Theorem A at `B(1/5,1/5)`), in `AbVar5dFinal.lean`;
* `thm11KappaAK5`: `Thm11KappaAK 5 2 (·+1) perA5 0 ∅` (Corollary A2), from `thm11KappaAK5_of`.
Both are stated against verbatim copies of lean_mstar's definitions (`MStarCopyAbVar.lean`).
-/

namespace LSG.W88

/-- **`lean_mstar`'s `Thm11KappaAK` (with `LA = ∅`) for `Jac(y⁵ = x(1 − x))`**, unconditionally. -/
theorem thm11KappaAK5 : MStarCopy.Thm11KappaAK 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 0 ∅ :=
  thm11KappaAK5_of hyperplaneKappaAbVar

end LSG.W88
