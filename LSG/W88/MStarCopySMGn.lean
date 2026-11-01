/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopyMGn

/-!
# Verbatim copy of `lean_mstar`'s model `gmSMGn` and hypothesis `Thm11KappaSMGn`

Source (read 2026-10-31): `lean_mstar/CM4E/Gen/SMG.lean`, section `SMGn` (`QSn`, `muSn`,
`lamSn`, `algQSn`, `lamSSn`, `perSSn`, `gmSMGn`, `Thm11KappaSMGn`). Everything else it uses
(`TF`, `tor1`, `tor2`, `qv`, `gmF2`, `Qn`, `algQn`, `perQn`, `KappaOneZero`) is in
`MStarCopyMGn`. Definition bodies are copied verbatim (only the namespace is
`LSG.W88.MStarCopy`).

**Premise.** `Thm11KappaSMGn` is premised on `KappaOneZero L` (`κ₁ = 0`), exactly as
`Thm11KappaMGn` and `Thm11KappaMGnK`. This premise was requested from lean_mstar on 2026-10-31
(the version read on that date has none; without it the statement needs CM theory for non-unit
`α`, Masser's `κ ∈ ℚ̄`, which `lean_lsg` lacks). Do not edit except to re-sync with the source.
-/

open Complex Module

namespace LSG.W88.MStarCopy

/-! ### `CM4E/Gen/SMG.lean`, section `SMGn` -/

section SMGn

variable (L : CMLattice) {r : ℕ} (b : Fin r → ℂ)

/-- `T(G_a × Q'') = ℂ × (ℂ^n/ℂ·ker φ × ℂ)`. -/
abbrev QSn := ℂ × Qn L b

/-- `μ = a`. -/
noncomputable def muSn : QSn L b →ₗ[ℂ] ℂ := LinearMap.fst ℂ ℂ _
/-- `λ` = the fibre coordinate. -/
noncomputable def lamSn : QSn L b →ₗ[ℂ] ℂ := LinearMap.snd ℂ _ ℂ ∘ₗ LinearMap.snd ℂ ℂ _

lemma muSn_apply (q : QSn L b) : muSn L b q = q.1 := rfl
lemma lamSn_apply (q : QSn L b) : lamSn L b q = q.2.2 := rfl

/-- The `ℚ̄`-structure. -/
def algQSn (q : QSn L b) : Prop := IsAlgebraic ℚ q.1 ∧ algQn L b q.2

/-- Logarithms: toric logarithms, algebraic `G_a` vectors and fibre values, periods of `Q''`. -/
def lamSSn : Set (TF (Fin r × Fin 2) (QSn L b)) :=
  {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor1 i x} ∪
    {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor2 i x} ∪
    {v | ∃ a f : ℂ, IsAlgebraic ℚ a ∧ IsAlgebraic ℚ f ∧ v = qv ((a, (0, f)) : QSn L b)} ∪
    (fun q => qv (((0 : ℂ), q) : QSn L b)) '' perQn L b

/-- Periods: `2πi` in a toric slot, periods of `Q''`. -/
noncomputable def perSSn : Set (TF (Fin r × Fin 2) (QSn L b)) :=
  Set.range (fun j : Fin r × Fin 2 => (tor1 j (2 * Real.pi * I) : TF (Fin r × Fin 2) (QSn L b))) ∪
    Set.range (fun j : Fin r × Fin 2 => (tor2 j (2 * Real.pi * I) : TF (Fin r × Fin 2) (QSn L b))) ∪
    (fun q => qv (((0 : ℂ), q) : QSn L b)) '' perQn L b

/-- The model of `G_a × G_m^{2n} × Q''` (`d₂ = dim Q''`). -/
noncomputable def gmSMGn : GroupModel (TF (Fin r × Fin 2) (QSn L b)) :=
  gmF2 (theta L.α b) (algQSn L b) (lamSSn L b) (perSSn L b) (muSn L b) (lamSn L b) (finrank ℂ (Qn L b))

/-- **The hypothesis for Theorem SMG♮**: W88 §5d for `G_a × G_m^{2n} × Q''`, every adapted basis. Premised on
`κ₁ = 0` (`KappaOneZero L`; requested from lean_mstar 2026-10-31). -/
def Thm11KappaSMGn : Prop :=
  KappaOneZero L → IsAlgebraic ℚ L.pp.g₂ → IsAlgebraic ℚ L.pp.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis L.α b → HyperplaneKappa (gmSMGn L b)

end SMGn

end LSG.W88.MStarCopy
