/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Checker

/-!
# Single-copy identities through the bidegree checker (computational)

A single-copy form `F(X)` of degree `d` is the product `F(X) · 1(Y)` of bidegree `(d, 0)`: the `X`-side table is the
degree-`d` normal-form table, the `Y`-side table is the degree-0 identity table `T0` (one leaf, `1 ↦ 1`).
`diagSP p` is the restriction `p(X, X)` of a bihomogeneous `SP` to the diagonal, as a single-copy `SP`.
Soundness: `LSG.Jac.Diag`. Core-only imports.
-/

namespace LSG.Jac

/-- The constant polynomial `1`. -/
def oneSP : SP := ⟨[(0, [(0, 1, false)])], [0]⟩

/-- The degree-0 identity table. -/
def T0 : T := .leaf ⟨0, 0, [(0, 1, false)], (1, 0)⟩

/-- `p(X, X)` as a single-copy `SP` (all `Y`-codes moved to the `X`-side). -/
def diagSP (p : SP) : SP :=
  ⟨p.rows.flatMap fun ra => ra.2.map fun t => (ra.1 + t.1, [(0, t.2.1, t.2.2)]), [0]⟩

/-- No carry in the codes merged by `diagSP`. -/
def diagOK (p : SP) : Bool := p.rows.all fun ra => ra.2.all fun t => nocarry ra.1 t.1

end LSG.Jac
