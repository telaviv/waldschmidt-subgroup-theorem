/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.LemniscateIndep.Main
import LSG.SchneiderMain

/-!
# The lemniscatic lattice: inputs for `lean_mstar`

`lean_mstar` (library `CM4E`) works with the period pair `CM4E.lemniscatic = (ϖ, iϖ)`, where
`CM4E.varpi = Γ(1/4)² / (2√(2π))`, and assumes `hg₂ : IsAlgebraic ℚ lemniscatic.g₂` and
`hS : Irrational (varpi / π)`. This file proves both, for any period pair `(ϖ, iϖ)` with `ϖ` given
by the same formula (`LSG.LemniscateIndep.varpi`):
* `isAlgebraic_g₂` (from `g₂ = 4`, proved in `LSG/LemniscateIndep/`);
* `transcendental_varpi_div_pi` and `irrational_varpi_div_pi` (Schneider's theorem
  `LSG.Schneider.period_div_pi_transcendental` at the period `ϖ`).
With `lean_mstar`'s definitions: `isAlgebraic_g₂ CM4E.lemniscatic rfl rfl` and
`irrational_varpi_div_pi` (after unfolding `CM4E.varpi`, which has the same body).
-/

open Complex

namespace LSG.Bridge

open LSG.LemniscateIndep

/-- `g₂(ϖℤ[i])` is algebraic (it is `4`). -/
theorem isAlgebraic_g₂ (L : PeriodPair) (h₁ : L.ω₁ = (varpi : ℂ)) (h₂ : L.ω₂ = I * varpi) :
    IsAlgebraic ℚ L.g₂ :=
  g₂_isAlgebraic_of L h₁ h₂

/-- `ϖ / π` is transcendental. -/
theorem transcendental_varpi_div_pi (L : PeriodPair) (h₁ : L.ω₁ = (varpi : ℂ))
    (h₂ : L.ω₂ = I * varpi) : Transcendental ℚ ((varpi : ℂ) / (Real.pi : ℂ)) := by
  have hg₃ : IsAlgebraic ℚ L.g₃ := by rw [g₃_eq_zero_of L h₁ h₂]; exact isAlgebraic_zero
  have hω : (varpi : ℂ) ∈ L.lattice := h₁ ▸ L.ω₁_mem_lattice
  have h0 : (varpi : ℂ) ≠ 0 := by
    rw [← h₁]; intro h
    have := L.indep.ne_zero 0
    simp_all
  exact LSG.Schneider.period_div_pi_transcendental (isAlgebraic_g₂ L h₁ h₂) hg₃ hω h0

/-- **`ϖ / π` is irrational** (discharges `lean_mstar`'s `hS`), given any period pair `(ϖ, iϖ)`. -/
theorem irrational_varpi_div_pi_of (L : PeriodPair) (h₁ : L.ω₁ = (varpi : ℂ))
    (h₂ : L.ω₂ = I * varpi) : Irrational (varpi / Real.pi) := by
  rintro ⟨q, hq⟩
  apply transcendental_varpi_div_pi L h₁ h₂
  have : ((varpi : ℂ) / (Real.pi : ℂ)) = ((q : ℚ) : ℂ) := by
    rw [← ofReal_div, ← hq]; push_cast; rfl
  rw [this]; exact isAlgebraic_algebraMap (q : ℚ)

end LSG.Bridge
