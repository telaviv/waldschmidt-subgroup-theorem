/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Stage 1 interfaces

This file only *states* the pieces of Stage 1 as `Prop`s, so that they can be proved in parallel
and assembled in `LSG/Schneider.lean`.

* `LSG.GrowthLE ρ g` : `‖g z‖ ≤ exp (C (1 + ‖z‖)^ρ)` for some `C`.
* `LSG.SchneiderLang` : the Schneider–Lang criterion in one variable (Lang, *Introduction to
  transcendental numbers*, Ch. III, Thm 1; Waldschmidt, *Nombres transcendants*, LNM 402, Ch. 3).
  Meromorphic functions of finite order are written as `gᵢ / h` with `gᵢ, h` entire of order
  `≤ ρ`; the conclusion is the finiteness of the set of points `w` with `h w ≠ 0` where all
  `fᵢ = gᵢ / h` take values in the number field `K`.
* `LSG.WeierstrassOrderTwo L` : `℘` and `℘'` are quotients of entire functions of order `≤ 2`
  by a common entire denominator vanishing exactly on the lattice.
-/

open Complex

namespace LSG

/-- `g` has growth of order at most `ρ`: `‖g z‖ ≤ exp (C (1 + ‖z‖)^ρ)` for some constant `C`. -/
def GrowthLE (ρ : ℝ) (g : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ z : ℂ, ‖g z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ)

/-- **The Schneider–Lang criterion (one variable).** Let `K ⊂ ℂ` be a number field, and let
`fᵢ = gᵢ / h` (`i < N`) with `gᵢ, h` entire of order at most `ρ`. Assume that on `{h ≠ 0}`
* each derivative `fᵢ'` is a polynomial with coefficients in `K` in `f₀, …, f_{N-1}`, and
* two of the `fᵢ` are algebraically independent over `K`.

Then only finitely many `w` with `h w ≠ 0` have `fᵢ(w) ∈ K` for all `i`. -/
def SchneiderLang : Prop :=
  ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (N : ℕ) (g : Fin N → ℂ → ℂ) (h : ℂ → ℂ)
    (ρ : ℝ),
    (∀ i, Differentiable ℂ (g i)) → Differentiable ℂ h →
    (∀ i, GrowthLE ρ (g i)) → GrowthLE ρ h →
    (∀ i, ∃ Q : MvPolynomial (Fin N) K, ∀ z, h z ≠ 0 →
      HasDerivAt (fun x => g i x / h x) (MvPolynomial.aeval (fun j => g j z / h z) Q) z) →
    (∃ i₁ i₂ : Fin N, ∀ P : MvPolynomial (Fin 2) K,
      (∀ z, h z ≠ 0 → MvPolynomial.aeval ![g i₁ z / h z, g i₂ z / h z] P = 0) → P = 0) →
    Set.Finite {w : ℂ | h w ≠ 0 ∧ ∀ i, ∃ k : K, g i w / h w = (k : ℂ)}

/-- `℘` and `℘'` are quotients `g₁ / h`, `g₂ / h` of entire functions of order at most `2`, with a
common denominator `h` vanishing exactly on the lattice. (Take `h = σ³`.) -/
def WeierstrassOrderTwo (L : PeriodPair) : Prop :=
  ∃ h gP gP' : ℂ → ℂ,
    Differentiable ℂ h ∧ Differentiable ℂ gP ∧ Differentiable ℂ gP' ∧
    GrowthLE 2 h ∧ GrowthLE 2 gP ∧ GrowthLE 2 gP' ∧
    (∀ z, h z = 0 ↔ z ∈ L.lattice) ∧
    ∀ z, z ∉ L.lattice → L.weierstrassP z = gP z / h z ∧ L.derivWeierstrassP z = gP' z / h z

end LSG
