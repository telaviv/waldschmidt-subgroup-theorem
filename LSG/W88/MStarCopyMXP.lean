/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopyMX

/-!
# Verbatim copy of `lean_mstar`'s model `gmXP` and its hypothesis `Thm11KappaMXP` (Theorem MX′)

Source (read 2026-10-31): `lean_mstar/CM4E/Gen/MXP.lean` (`TXP`, `psiP1`, `psiP2`, `gPI`, `gPR`,
`gPA`, `lamGenP`, `GP1`, …, `perXP`, `algXP`, `gmXP`, `Thm11KappaMXP`). The definition bodies are
copied verbatim; only the namespace is `LSG.W88.MStarCopy`. The shared definitions (`theta`,
`dotL`, `LogNat`, the period pairs, `GroupModel`, `HyperplaneKappa`) are the copies of
`MStarCopyMX.lean` / `MStarCopy.lean`. Do not edit except to re-sync with the source.
-/

open Complex Module Real

namespace LSG.W88.MStarCopy

variable {r : ℕ}

/-- The tangent space `ℂ^n × ℂ^n × ℂ × ℂ`, coordinates `(z_i, z_ρ, s₁, s₂)`. -/
abbrev TXP (r : ℕ) := (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ) × ℂ × ℂ

variable (b : Fin r → ℂ)

/-- `Ψ''₁ = θᵀz_i + s₁`. -/
noncomputable def psiP1 : TXP r →ₗ[ℂ] ℂ :=
  dotL (theta I b) ∘ₗ LinearMap.fst ℂ _ _ +
    LinearMap.fst ℂ ℂ ℂ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _
/-- `Ψ''₂ = θᵀz_ρ + s₂`. -/
noncomputable def psiP2 : TXP r →ₗ[ℂ] ℂ :=
  dotL (theta I b) ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ +
    LinearMap.snd ℂ ℂ ℂ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _

/-- `(z, w) ∈ T(E_i^♮)` in copy `h` (its fibre value goes to `s₂`). -/
noncomputable def gPI (h : Fin r × Fin 2) (z w : ℂ) : TXP r := (Pi.single h z, 0, 0, theta I b h * w)
/-- `(z, w) ∈ T(E_ρ^♮)` in copy `h` (its fibre value goes to `s₁`). -/
noncomputable def gPR (h : Fin r × Fin 2) (z w : ℂ) : TXP r := (0, Pi.single h z, theta I b h * w, 0)
/-- `(a₁, a₂) ∈ T(G_a²)` in copy `h`. -/
noncomputable def gPA (h : Fin r × Fin 2) (a c : ℂ) : TXP r := (0, 0, theta I b h * a, theta I b h * c)

/-- Generators of `lam`. -/
def lamGenP : Set (TXP r) :=
  {v | ∃ h z w, LogNat lemniscatic etaLem z w ∧ v = gPI b h z w} ∪
    {v | ∃ h z w, LogNat equianharmonic etaR z w ∧ v = gPR b h z w} ∪
    {v | ∃ h a c, IsAlgebraic ℚ a ∧ IsAlgebraic ℚ c ∧ v = gPA b h a c}

/-- Period generators in copy `j`. -/
noncomputable def GP1 (j : Fin r × Fin 2) : TXP r := gPI b j varpi (Real.pi / varpi)
noncomputable def GP2 (j : Fin r × Fin 2) : TXP r := gPI b j (I * varpi) (-I * (Real.pi / varpi))
noncomputable def HP1 (j : Fin r × Fin 2) : TXP r := gPR b j omegaRho etaRho
noncomputable def HP2 (j : Fin r × Fin 2) : TXP r := gPR b j (rho * omegaRho) (rhoBar * etaRho)

/-- The `ℚ`-span of the periods. -/
noncomputable def perXP : Submodule ℚ (TXP r) :=
  Submodule.span ℚ (Set.range (GP1 b) ∪ Set.range (GP2 b) ∪ Set.range (HP1 b) ∪ Set.range (HP2 b))

/-- Algebraic coordinates. -/
def algXP (v : TXP r) : Prop :=
  (∀ j, IsAlgebraic ℚ (v.1 j)) ∧ (∀ j, IsAlgebraic ℚ (v.2.1 j)) ∧ IsAlgebraic ℚ v.2.2.1 ∧
    IsAlgebraic ℚ v.2.2.2

/-- The model of `G''` (extension of `E_i^n × E_ρ^n` by `G_a²`). -/
noncomputable def gmXP : GroupModel (TXP r) where
  d₁ := 0
  d₂ := 2 * Fintype.card (Fin r × Fin 2) + 2
  alg := algXP
  lam := (Submodule.span ℚ (lamGenP b) : Set (TXP r))
  per := perXP b
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algXP x ∧ (psiP1 b x ≠ 0 ∨ psiP2 b x ≠ 0)

/-- **The hypothesis for Proposition D′**: W88 §5d for `G''`, every adapted basis of a number field containing `i`. -/
def Thm11KappaMXP : Prop :=
  IsAlgebraic ℚ lemniscatic.g₂ → IsAlgebraic ℚ lemniscatic.g₃ →
    IsAlgebraic ℚ equianharmonic.g₂ → IsAlgebraic ℚ equianharmonic.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b → HyperplaneKappa (gmXP b)

end LSG.W88.MStarCopy
