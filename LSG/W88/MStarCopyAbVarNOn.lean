/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopyAbVarN

/-!
# Verbatim copy of `lean_mstar`'s `K`-form hypothesis `Thm11KappaAnK` (M2.8 bridge)

Source: `lean_mstar` commit `8458732`, `CM4E/AbVar/MGAK.lean`, section `MGAn`: `twistAn`, `lamAnK`, `gmAnK`, `Thm11KappaAnK`
(narrowed there to the toric-injective hyperplanes, M2.md §1.6). Only the namespace differs. `HyperplaneKappaOn`, `TorInj`
are the existing copies (`MStarCopyAbVar.lean`); `gmAn`, `algAn`, `perAngen` are in `MStarCopyAbVarN.lean`. The file keeps
its name from when it held the proposed narrowed forms `Thm11KappaAnOn`, `Thm11KappaAnKOn`; those are gone. The copies are
not trusted: lean_mstar's `CM4E.Bridge.thm11KappaAnK5_uncond` states lean_mstar's own definition and typechecks against
`LSG.W88.thm11KappaAnK5`. Do not edit except to re-sync with the source.
-/

open Complex Module

namespace LSG.W88.MStarCopy

/-! ### `CM4E/AbVar/MGAK.lean`, section `MGAn` (verbatim) -/

section MGAn

variable (N g : ℕ) (κ : Fin g → ℕ) {r : ℕ}

variable (P : Fin g → ℂ) (Pb : ℂ) (b : Fin r → ℂ) (LAn : Set ((Fin g → ℂ) × ℂ))

/-- `[ζ^e](v, w)` in copy `j` of `(A^♮)^r`, pushed to `Q''`: base `ζ^{κ s · e} v_s`, fibre `b_j ζ^{(N−1)e} w`. -/
noncomputable def twistAn (b : Fin r → ℂ) (j : Fin r) (e : ℕ) (vw : (Fin g → ℂ) × ℂ) : (Fin g × Fin r → ℂ) × ℂ :=
  (twistA N g κ j e vw.1, b j * zetaN N ^ ((N - 1) * e) * vw.2)

/-- Generators of the logarithms of `G_m^{2n} × Q''`. -/
def lamAnK : Set (TF (Fin r × Fin N.totient) ((Fin g × Fin r → ℂ) × ℂ)) :=
  {x | ∃ i y, IsAlgebraic ℚ (Complex.exp y) ∧ x = tor1 i y} ∪
    {x | ∃ i y, IsAlgebraic ℚ (Complex.exp y) ∧ x = tor2 i y} ∪
    {x | ∃ (j : Fin r) (e : ℕ), ∃ vw ∈ insert (P, Pb) LAn, x = qv (twistAn N g κ b j e vw)}

/-- The model of `G_m^{2n} × Q''` with logarithms of `A^♮` (frame `gmF2`). -/
noncomputable def gmAnK : GroupModel (TF (Fin r × Fin N.totient) ((Fin g × Fin r → ℂ) × ℂ)) :=
  gmF2 (thetaD (zetaN N) N.totient b) (algAn g) (lamAnK N g κ P Pb b LAn)
    (perGen (ι := Fin r × Fin N.totient) (perAngen N g κ P Pb b)) 0 (LinearMap.snd ℂ _ ℂ)
    (finrank ℂ ((Fin g × Fin r → ℂ) × ℂ))

/-- **The hypothesis for the `K`-form of MG♮-A**: W88 §5d for `G_m^{2n} × Q''`, every `F`-basis `b`, restricted to the
toric-injective hyperplanes (`TorInj`, as for `Thm11KappaAn`; this only weakens it, and the proof uses only `V''`, which
is toric-injective by `perAn_inj`). Claimed when `LAn`
consists of (eigen-coordinate tuple, `σ̄`-fibre value) pairs of logarithms of algebraic points of `A^♮` (normalised as
`(P, P̄)`). -/
def Thm11KappaAnK : Prop :=
  ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedBasisD (zetaN N) N.totient b →
    HyperplaneKappaOn (gmAnK N g κ P Pb b LAn) (TorInj (gmAnK N g κ P Pb b LAn))

end MGAn

end LSG.W88.MStarCopy
