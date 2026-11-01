/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.LemniscateIndep.RealLine

/-!
# The lemniscatic lattice `ϖ ℤ[i]` has `g₂ = 4`, `g₃ = 0`

Here `ϖ = varpi = Γ(1/4)² / (2 √(2π))`. Independent proof: `g₃ = 0` by the symmetry `z ↦ i z`;
`g₂ = 4 (ϖ / a)⁴` for the square lattice `a ℤ[i]` (`Sq.g₂_eq_of_square`), from the real branch
of `℘` on `(0, a/2]` and `ϖ = 2 ∫₀¹ dt / √(1 - t⁴)`.
-/

noncomputable section

open Complex

namespace LSG.LemniscateIndep

theorem g₂_eq_four_of (L : PeriodPair) (h₁ : L.ω₁ = (varpi : ℂ))
    (h₂ : L.ω₂ = Complex.I * varpi) : L.g₂ = 4 := by
  rw [Sq.g₂_eq_of_square ⟨varpi_pos, h₁, h₂⟩, div_self varpi_pos.ne']
  norm_num

theorem g₃_eq_zero_of (L : PeriodPair) (h₁ : L.ω₁ = (varpi : ℂ))
    (h₂ : L.ω₂ = Complex.I * varpi) : L.g₃ = 0 :=
  g₃_eq_zero_of_square h₁ h₂

theorem g₂_isAlgebraic_of (L : PeriodPair) (h₁ : L.ω₁ = (varpi : ℂ))
    (h₂ : L.ω₂ = Complex.I * varpi) : IsAlgebraic ℚ L.g₂ := by
  rw [g₂_eq_four_of L h₁ h₂]
  simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (4 : ℚ)

end LSG.LemniscateIndep
