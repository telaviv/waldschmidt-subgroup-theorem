/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopyMX

/-!
# Verbatim copy of `lean_mstar`'s model `gmQ` and hypothesis `Thm11KappaNat` (Theorem 1(a))

Source (read 2026-10-31): `lean_mstar/CM4E/MainNat.lean` (namespace `CM4E.MainNat`): `TN`, `r2`, `θ`, `θ₁`, `θ₂`,
`perImg`, `perQ`, `gmQ`, `Thm11KappaNat`. Bodies copied verbatim; only the namespace is `LSG.W88.MStarCopy.Nat`
(`varpi`, `etaLem`, `lemniscatic`, `GroupModel`, `HyperplaneKappa` are the copies in `LSG.W88.MStarCopy`). Checked
against the unmodified source with `lake env lean` from `lean_mstar`. Do not edit except to re-sync with the source.
-/

open Complex Module

namespace LSG.W88.MStarCopy.Nat

open LSG.W88.MStarCopy

/-- The tangent space `ℂ⁸ × ℂ³` of `G_m⁸ × Q''`. -/
abbrev TN := (Fin 8 → ℂ) × (Fin 3 → ℂ)

/-- `√2` as a complex number. -/
noncomputable def r2 : ℂ := (Real.sqrt 2 : ℂ)

/-- The basis `θ = (1, i, √2, i√2)` of `ℚ(i, √2)`. -/
noncomputable def θ : Fin 4 → ℂ := ![1, I, r2, I * r2]
/-- `τ₁(θ)`, `τ₁ : i ↦ −i, √2 ↦ √2`. -/
noncomputable def θ₁ : Fin 4 → ℂ := ![1, -I, r2, -I * r2]
/-- `τ₂(θ)`, `τ₂ : i ↦ −i, √2 ↦ −√2`. -/
noncomputable def θ₂ : Fin 4 → ℂ := ![1, -I, -r2, I * r2]

/-- The image in `T(Q'')` of the period `((λ_j, η(λ_j)))_j` of `(E^♮)⁴`, `λ_j = (m_j + n_j i)ϖ`. -/
noncomputable def perImg (m n : Fin 4 → ℤ) : Fin 3 → ℂ :=
  ![∑ j, θ₁ j * (((m j : ℂ) + n j * I) * varpi), ∑ j, θ₂ j * (((m j : ℂ) + n j * I) * varpi),
    ∑ j, θ j * etaLem (m j) (n j)]

/-- The periods of `Q''`. -/
def perQ : Set (Fin 3 → ℂ) := Set.range (fun mn : (Fin 4 → ℤ) × (Fin 4 → ℤ) => perImg mn.1 mn.2)

/-- The model of `G_m⁸ × Q''`. -/
noncomputable def gmQ : GroupModel TN where
  d₁ := 8
  d₂ := 3
  alg := fun v => (∀ j, IsAlgebraic ℚ (v.1 j)) ∧ ∀ j, IsAlgebraic ℚ (v.2 j)
  lam := {y | (∀ j, IsAlgebraic ℚ (Complex.exp (y.1 j))) ∧ y.2 ∈ perQ}
  per := Submodule.span ℚ
    (Set.range (fun j : Fin 8 => ((Pi.single j (2 * Real.pi * I) : Fin 8 → ℂ), (0 : Fin 3 → ℂ))) ∪
      (fun q => ((0 : Fin 8 → ℂ), q)) '' perQ)
  sub := fun S => ∃ (L : Submodule ℚ (Fin 8 → ℚ)) (h : Submodule ℂ (Fin 3 → ℂ)),
    (h = ⊥ ∨ Pi.single 2 1 ∈ h) ∧
    S = (Submodule.span ℂ ((fun l : Fin 8 → ℚ => fun j => ((l j : ℚ) : ℂ)) '' (L : Set _))).prod h

/-- **The hypothesis for Theorem 1(a)**: W88 §5d for `G_m⁸ × Q''` (same form as `Thm11Kappa`). -/
def Thm11KappaNat : Prop :=
  IsAlgebraic ℚ lemniscatic.g₂ → IsAlgebraic ℚ lemniscatic.g₃ → HyperplaneKappa gmQ

end LSG.W88.MStarCopy.Nat
