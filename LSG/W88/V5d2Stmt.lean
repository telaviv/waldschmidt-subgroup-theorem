/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.StatementVec

/-!
# Theorem 4.1 and §5d for the class `𝒞` with `d₀ = 0`, `r ≤ 2` (design: `STAGE6_MXP.md`)

* `Theorem41Vec2`: `Theorem41Vec` with the premises `d₀ = 0`, `r ≤ 2`, `LiftAlg Ls`,
  `PerTanRat Ls` and `dim (V ∩ fibre) ≤ 1` (in place of `Theorem41VecLA`'s `r ≤ 1`,
  `V ∩ fibre = 0`).
* `HyperplaneKappaVec2`: W88 §5d for the class under `d₀ = 0`, `r ≤ 2`, `LiftAlg`, `PerTanRat`.

These cover Theorem MX′ (`gmXP`: `d₀ = d₁ = 0`, `r = 2`), where a hyperplane always meets the
two-dimensional fibre.
-/

open Complex Module

namespace LSG.W88.Vec

/-- **W88 Theorem 4.1 for the class `𝒞` with `d₀ = 0`, `r ≤ 2`, `dim (V ∩ fibre) ≤ 1`**
(under (NR), `LiftAlg`, `PerTanRat`). -/
def Theorem41Vec2 : Prop :=
  ∀ (d0 d1 m r : ℕ) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ),
    (∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) → AlgMat M →
    d0 = 0 → r ≤ 2 → LiftAlg Ls → PerTanRat Ls →
    ∀ (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r)),
      finrank ℂ V < d0 + d1 + m + r → W ≤ V → RatSubV W →
      finrank ℂ ↥(V ⊓ fibreV) ≤ 1 →
      Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M) →
      d1 + 2 * d0 + rk (Y ⊓ PerV Ls M) ≤ 2 * finrank ℂ V →
      Concl41 Ls M V W Y

/-- **W88 §5d for the class with `d₀ = 0`, `r ≤ 2`.** -/
def HyperplaneKappaVec2 : Prop :=
  ∀ (d0 d1 m r : ℕ) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ),
    (∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) → AlgMat M →
    d0 = 0 → r ≤ 2 → LiftAlg Ls → PerTanRat Ls →
    ∀ (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r)),
      finrank ℂ V + 1 = d0 + d1 + m + r → W ≤ V → RatSubV W →
      Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M) →
      ((rk Y : ℤ) > ((d1 : ℤ) + 2 * (m + r) - rk (Y ⊓ PerV Ls M)) *
        ((d0 + d1 + m + r : ℤ) - 1 - finrank ℂ W)) →
      ∃ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan ≠ ⊥ ∧ H.tan ≤ V

end LSG.W88.Vec
