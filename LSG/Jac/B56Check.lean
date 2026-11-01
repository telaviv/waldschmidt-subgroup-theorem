/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.CheckerP2

/-!
# Exact ideal-membership identities for B5 (core-only)

`idTerms D A B cs` encodes `D · A · B − Σ_{(c, g) ∈ cs} c · g` (single copy, all `SP`s with `Y`-codes `[0]`). The
kernel checks that it vanishes identically through `evalOd d idTree T0` (`CheckerP2`); soundness and the
ideal-membership reading are in `LSG.Jac.B56Sound`.
-/

namespace LSG.Jac

/-- `D · A · B − Σ c · g`. -/
def idTerms (D : Nat) (A B : SP) (cs : List (SP × SP)) : List Term :=
  ⟨D, false, A, B⟩ :: cs.map fun p => (⟨1, true, p.1, p.2⟩ : Term)

end LSG.Jac
