/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopyAbVar

/-!
# Verbatim copy of `lean_mstar`'s second-kind hypothesis `Thm11KappaAn` (M2.8 bridge)

Source: `lean_mstar` commit `8458732` (which narrowed `Thm11KappaAn` to the toric-injective hyperplanes, M2.md §1.6):
* `CM4E/AbVar/ThmAn.lean`: `perAngen`, `algAn`, `gmAn`, `Thm11KappaAn`, `perB5`.

The remaining dependencies (`GroupModel`, `HyperplaneKappaOn`, `TorInj`, `TF`, `gmF`, `IsAdaptedBasisD`, `zetaN`, `betaG`,
`perA5`) are the existing copies in `MStarCopy`, `MStarCopyMGn`, `MStarCopyAbVar`. Definition bodies, binders and the
`variable` context are copied verbatim; only the namespace is `LSG.W88.MStarCopy`. The copies are not trusted: lean_mstar's
`CM4E.Bridge.thm11KappaAn5_uncond` states lean_mstar's own definition and typechecks against `LSG.W88.thm11KappaAn5`.
Do not edit except to re-sync with the source.
-/

open Complex Module

namespace LSG.W88.MStarCopy

/-! ### `CM4E/AbVar/ThmAn.lean` -/

section ThmAn

variable (N g : ℕ) (κ : Fin g → ℕ) (P : Fin g → ℂ) (Pb : ℂ) {r : ℕ} (b : Fin r → ℂ)

/-- Generators of the periods of `Q''`: the images of `[ζ^e]γ̃` in copy `j`. -/
noncomputable def perAngen : Set ((Fin g × Fin r → ℂ) × ℂ) :=
  Set.range (fun je : Fin r × ℕ =>
    ((fun p => if p.2 = je.1 then zetaN N ^ (κ p.1 * je.2) * P p.1 else 0),
      b je.1 * zetaN N ^ ((N - 1) * je.2) * Pb))

/-- The `ℚ̄`-structure of `T(Q'')`. -/
def algAn (q : (Fin g × Fin r → ℂ) × ℂ) : Prop := (∀ p, IsAlgebraic ℚ (q.1 p)) ∧ IsAlgebraic ℚ q.2

/-- **The model of `G_m^{2n} × Q''`.** -/
noncomputable def gmAn : GroupModel (TF (Fin r × Fin N.totient) ((Fin g × Fin r → ℂ) × ℂ)) :=
  gmF (algAn g) (perAngen N g κ P Pb b) (LinearMap.snd ℂ _ ℂ)

/-- **The hypothesis for Theorem MG♮-A**: W88 §5d for `G_m^{2n} × Q''`, for every `F`-basis `b` of a number field,
restricted to the toric-injective hyperplanes (`TorInj`: no nonzero period of `Q''` alone lies in `V`). The restriction
only weakens the hypothesis (`HyperplaneKappa.on`); the proofs use it only at `ker phiF` and `ker phiW`, which are
toric-injective (`perAn_inj`; this needs every `κ s` prime to `N`). -/
def Thm11KappaAn : Prop :=
  ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedBasisD (zetaN N) N.totient b →
    HyperplaneKappaOn (gmAn N g κ P Pb b) (TorInj (gmAn N g κ P Pb b))

end ThmAn

/-! ### `CM4E/AbVar/ThmAn.lean` (instance) -/

/-- The second-kind period `P̄ = (1 − ζ₅⁴) B(4/5, 4/5)` (`∫_γ dx/y`). -/
noncomputable def perB5 : ℂ := (1 - zetaN 5 ^ 4) * betaG (4 / 5) (4 / 5)

end LSG.W88.MStarCopy
