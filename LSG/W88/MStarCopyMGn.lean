/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopyMX

/-!
# Verbatim copy of `lean_mstar`'s models `gmMGn`, `gmMGnK` and hypotheses `Thm11KappaMGn`, `Thm11KappaMGnK`

Sources (read 2026-10-31): `lean_mstar/CM4E/Gen/CMLattice.lean` (`CMLattice`), `CM4E/Gen/Frame.lean` (`TF`, `tor1`,
`tor2`, `qv`, `algF`, `lamGen`, `perGen`, `torSub`, `gmF`; `dotL` is in `MStarCopyMX`), `CM4E/Gen/Frame2.lean`
(`PsiG`, `gmF2`), `CM4E/Gen/MGn.lean` (`kSet`, `Wphi`, `Qn`, `algQn`, `perQn`, `gmMGn`, `KappaOneZero`,
`Thm11KappaMGn`), `CM4E/Gen/MGnK.lean` (`etaL`, `lamMGnK`, `gmMGnK`, `Thm11KappaMGnK`). Definition bodies are copied
verbatim (only the namespace is `LSG.W88.MStarCopy`; `CM4E.Ext.Weierstrass.zeta` is `Ext.zeta`). Checked against the
unmodified sources with `lake env lean` from `lean_mstar` (structure types `CMLattice`, `IsAdaptedFieldBasis` by
field-by-field adapters). Do not edit except to re-sync with the source.
-/

open Complex Module

namespace LSG.W88.MStarCopy

/-! ### `CM4E/Gen/CMLattice.lean` -/

/-- A CM lattice `ω ℤ[α]` with quasi-period `η₀`. -/
structure CMLattice where
  /-- the period pair `(ω, αω)` -/
  pp : PeriodPair
  ω : ℂ
  α : ℂ
  η₀ : ℂ
  p : ℚ
  q : ℚ
  hω₁ : pp.ω₁ = ω
  hω₂ : pp.ω₂ = α * ω
  hquad : α ^ 2 = p + q * α
  him : 0 < α.im
  legendre : ω * η₀ * (α - starRingEnd ℂ α) = 2 * Real.pi * I

/-! ### `CM4E/Gen/Frame.lean` -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q]

/-- The tangent space `((ι → ℂ) × (ι → ℂ)) × Q` of `G_m^{2n} × G₂`. -/
abbrev TF (ι Q : Type) [AddCommGroup Q] := ((ι → ℂ) × (ι → ℂ)) × Q

/-- A logarithm in the first `G_m^n` block, slot `j`. -/
def tor1 (j : ι) (x : ℂ) : TF ι Q := ((Pi.single j x, 0), 0)
/-- A logarithm in the second `G_m^n` block, slot `j`. -/
def tor2 (j : ι) (x : ℂ) : TF ι Q := ((0, Pi.single j x), 0)
/-- A vector of `Q`. -/
def qv (q : Q) : TF ι Q := ((0, 0), q)

/-- Algebraic coordinates (`algQ` is the `ℚ̄`-structure of `Q`). -/
def algF (algQ : Q → Prop) (v : TF ι Q) : Prop :=
  (∀ j, IsAlgebraic ℚ (v.1.1 j)) ∧ (∀ j, IsAlgebraic ℚ (v.1.2 j)) ∧ algQ v.2

/-- Generators of `lam`: logarithms of algebraic numbers in one toric slot, and the periods of `G₂`. -/
def lamGen (perQ : Set Q) : Set (TF ι Q) :=
  {v | ∃ j x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor1 j x} ∪
    {v | ∃ j x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor2 j x} ∪ qv '' perQ

/-- Generators of the periods: `2πi` in one toric slot, and the periods of `G₂`. -/
noncomputable def perGen (perQ : Set Q) : Set (TF ι Q) :=
  Set.range (fun j : ι => (tor1 j (2 * Real.pi * I) : TF ι Q)) ∪
    Set.range (fun j : ι => (tor2 j (2 * Real.pi * I) : TF ι Q)) ∪ qv '' perQ

/-- The Lie algebra of the subtorus `T_L`, `L ⊂ ℚ^{2n}`. -/
noncomputable def torSub (L : Submodule ℚ ((ι → ℚ) × (ι → ℚ))) : Submodule ℂ ((ι → ℂ) × (ι → ℂ)) :=
  Submodule.span ℂ ((fun l : (ι → ℚ) × (ι → ℚ) => ((fun j => ((l.1 j : ℚ) : ℂ)), (fun j => ((l.2 j : ℚ) : ℂ)))) ''
    (L : Set ((ι → ℚ) × (ι → ℚ))))

/-- **The group model of `G_m^{2n} × G₂`.** Sound when: `algQ`, `perQ` are the `ℚ̄`-structure and (generators of the
`ℚ`-span of) the periods of `G₂`; `G₂` has no `G_a` or `G_m` factor; and every nonzero connected algebraic subgroup of
`G₂` has a tangent vector with `λ ≠ 0`. Connected subgroups of `G_m^{2n} × G₂` are then products `T_L × H` (Goursat:
no subquotient of `G₂` is a torus and no subquotient of a torus is a quotient of a subgroup of `G₂`, which holds for the
`G₂` used here: abelian varieties and anti-affine extensions of them by `G_a`). -/
noncomputable def gmF (algQ : Q → Prop) (perQ : Set Q) (lam : Q →ₗ[ℂ] ℂ) [FiniteDimensional ℂ Q] :
    GroupModel (TF ι Q) where
  d₁ := 2 * Fintype.card ι
  d₂ := finrank ℂ Q
  alg := algF algQ
  lam := (Submodule.span ℚ (lamGen (ι := ι) perQ) : Set (TF ι Q))
  per := Submodule.span ℚ (perGen (ι := ι) perQ)
  sub := fun S => ∃ (L : Submodule ℚ ((ι → ℚ) × (ι → ℚ))) (h : Submodule ℂ Q),
    (h = ⊥ ∨ ∃ x ∈ h, lam x ≠ 0) ∧ S = (torSub L).prod h

/-! ### `CM4E/Gen/Frame2.lean` -/

/-- `Ψ'' = (θᵀx + μ(q), θᵀy + λ(q))`. -/
noncomputable def PsiG (θ : ι → ℂ) (μ lam : Q →ₗ[ℂ] ℂ) : TF ι Q →ₗ[ℂ] ℂ × ℂ :=
  (dotL θ ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _) + μ ∘ₗ LinearMap.snd ℂ _ _).prod
    (dotL θ ∘ₗ (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _) + lam ∘ₗ LinearMap.snd ℂ _ _)

/-- **The group model of `G_m^{2n} × G₂`** with linear forms `μ, λ`. Sound when `lamS` consists of logarithms of
algebraic points, `perS` of periods, `d₂ = dim Q − d₀` (`d₀`, `d₁ = 2n` maximal), and no nonzero connected algebraic
subgroup has its tangent space in `ker Ψ''`. -/
noncomputable def gmF2 (θ : ι → ℂ) (algQ : Q → Prop) (lamS perS : Set (TF ι Q)) (μ lam : Q →ₗ[ℂ] ℂ)
    (d₂ : ℕ) : GroupModel (TF ι Q) where
  d₁ := 2 * Fintype.card ι
  d₂ := d₂
  alg := algF algQ
  lam := (Submodule.span ℚ lamS : Set (TF ι Q))
  per := Submodule.span ℚ perS
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algF algQ x ∧ PsiG θ μ lam x ≠ 0

end Frame

/-! ### `CM4E/Gen/MGn.lean` -/

section MGn

variable (L : CMLattice) {r : ℕ} (b : Fin r → ℂ)

/-- `ℚ(α)`, as a set. -/
def kSet (α : ℂ) : Set ℂ := {z | ∃ u v : ℚ, z = u + v * α}

/-- `ℂ · ker φ`, `φ(m) = Σ θ_j m̄_j` on `k^n`. -/
noncomputable def Wphi : Submodule ℂ (Fin r × Fin 2 → ℂ) :=
  Submodule.span ℂ {v | (∀ j, v j ∈ kSet L.α) ∧ ∑ j, theta L.α b j * starRingEnd ℂ (v j) = 0}

/-- `T(Q'') = ℂ^n / ℂ·ker φ × ℂ`. -/
abbrev Qn := ((Fin r × Fin 2 → ℂ) ⧸ Wphi L b) × ℂ

/-- The `ℚ̄`-structure of `T(Q'')`. -/
def algQn (x : Qn L b) : Prop :=
  (∃ v : Fin r × Fin 2 → ℂ, (∀ j, IsAlgebraic ℚ (v j)) ∧ Submodule.Quotient.mk v = x.1) ∧
    IsAlgebraic ℚ x.2

/-- Generators of the periods of `Q''`. -/
noncomputable def perQn : Set (Qn L b) :=
  Set.range (fun j => ((Submodule.Quotient.mk (Pi.single j L.ω) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b),
      theta L.α b j * L.η₀)) ∪
    Set.range (fun j => ((Submodule.Quotient.mk (Pi.single j (L.α * L.ω)) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b),
      theta L.α b j * (starRingEnd ℂ L.α * L.η₀)))

/-- The model of `G_m^{2n} × Q''`. -/
noncomputable def gmMGn : GroupModel (TF (Fin r × Fin 2) (Qn L b)) :=
  gmF (algQn L b) (perQn L b) (LinearMap.snd ℂ _ ℂ)

/-- `κ₁ = 0`, in the form `ζ(αz) = ᾱζ(z)` (true when `α` is a unit, as for `ϖℤ[i]` and `Ω_ρℤ[ρ]`). It makes the
quasi-periods conjugate-linear, so the standard `ζ` is the conjugate-eigen `ζ*` and `η₀ = η(ω)`. -/
def KappaOneZero (L : CMLattice) : Prop :=
  ∀ z : ℂ, Ext.zeta L.pp (L.α * z) = starRingEnd ℂ L.α * Ext.zeta L.pp z

/-- **The hypothesis for Theorem MG♮ (general `c`)**: W88 §5d for `G_m^{2n} × Q''`, for every adapted basis. Same form
as all other hypotheses of the project (`HyperplaneKappa` of a group model). -/
def Thm11KappaMGn : Prop :=
  KappaOneZero L → IsAlgebraic ℚ L.pp.g₂ → IsAlgebraic ℚ L.pp.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis L.α b → HyperplaneKappa (gmMGn L b)

end MGn

/-! ### `CM4E/Gen/MGnK.lean` -/

/-- The quasi-period `η*((m + nα)ω) = (m + nᾱ)η₀` of a CM lattice. -/
noncomputable def etaL (L : CMLattice) (m n : ℤ) : ℂ := ((m : ℂ) + n * starRingEnd ℂ L.α) * L.η₀

section MGnK

variable (L : CMLattice) {r : ℕ} (b : Fin r → ℂ)

/-- Generators of the logarithms of `G_m^{2n} × Q''`. -/
def lamMGnK : Set (TF (Fin r × Fin 2) (Qn L b)) :=
  {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor1 i x} ∪
    {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor2 i x} ∪
    {v | ∃ i u w, LogNat L.pp (etaL L) u w ∧
      v = qv (((Submodule.Quotient.mk (Pi.single i u) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), theta L.α b i * w) :
        Qn L b)}

/-- The model of `G_m^{2n} × Q''` with logarithms of algebraic points of `(E^♮)^n`. -/
noncomputable def gmMGnK : GroupModel (TF (Fin r × Fin 2) (Qn L b)) :=
  gmF2 (theta L.α b) (algQn L b) (lamMGnK L b) (perGen (ι := Fin r × Fin 2) (perQn L b)) 0
    (LinearMap.snd ℂ _ ℂ) (finrank ℂ (Qn L b))

/-- **The hypothesis for the `K`-form of Theorem MG♮**: W88 §5d for `G_m^{2n} × Q''`, for every adapted basis.
Premised on `κ₁ = 0` (`KappaOneZero L`). -/
def Thm11KappaMGnK : Prop :=
  KappaOneZero L → IsAlgebraic ℚ L.pp.g₂ → IsAlgebraic ℚ L.pp.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis L.α b → HyperplaneKappa (gmMGnK L b)

end MGnK

end LSG.W88.MStarCopy
