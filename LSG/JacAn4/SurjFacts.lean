/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.A1Facts

/-!
# `SurjFacts`: the algebraic inputs of A4.1b (surjectivity), separate from `A1Facts`

The fields are stated as in STAGE_A1.md, section "Requests from the A3 agent for A4.1b". The certificate agent γ
(`LSG/JacBlock/`) discharges them with A1's checker.

* `affine_chart` (S-a): points of the model with `X₀ = 1` are Grant points of the Mumford chart.
* `anchor` (S-b): `law0(2D₀, −P₀) = λ P₀`, `λ ≠ 0`, at the special base `D₀ = (0,−1) + (α,3)`, `α⁵ = 2`, for an
  explicit generic divisor `2D₀`.
* `gensI`, `gensI_iff`, `tanC4/8`, `gensI_tan4/8` (S-c): generators of the ideal and tangency of the chart-4/8 fields in
  ideal form.
* `exit4/8` (S-c): flow exit words, the semantic form of `X_c^N ∈ I_A + (X₀, D-words of X₀ of order ≤ 3)`.
-/

noncomputable section

namespace LSG.JacAn

/-- The derivative of `h` along `v₀ W₀ + v₁ W₁`. -/
def derivW (W : Fin 2 → P9 → P9) (v : Fin 2 → ℂ) (h : P9 → ℂ) : P9 → ℂ :=
  fun X => fderiv ℂ h X (v 0 • W 0 X + v 1 • W 1 X)

/-- The exit words `D_v^k X₀`. -/
def exitWord (W : Fin 2 → P9 → P9) (v : Fin 2 → ℂ) (k : ℕ) : P9 → ℂ := (derivW W v)^[k] (fun X => X 0)

/-- The special base point `P₀(α) = grant((0, −1) + (α, 3))`. -/
def P0of (α : ℂ) : P9 := grantJ (mumfordPts' 0 (-1) α 3)

/-- **The algebraic inputs of surjectivity.** -/
structure SurjFacts (A : A1Facts) where
  affine_chart : ∀ X : P9, A.OnQ X → X 0 = 1 →
    X = grantJ ![X 3, -X 2, X 7, X 6] ∧ chartR1J ![X 3, -X 2, X 7, X 6] = 0 ∧
      chartR0J ![X 3, -X 2, X 7, X 6] = 0
  anchor : ∃ α : ℂ, α ^ 5 = 2 ∧ A.law0 (P0of α) (A.negP (P0of α)) 4 ≠ 0 ∧
    ∃ x₁ y₁ x₂ y₂ : ℂ, y₁ ^ 2 = 4 * x₁ ^ 5 + 1 ∧ y₂ ^ 2 = 4 * x₂ ^ 5 + 1 ∧ x₁ ≠ x₂ ∧ y₁ ≠ 0 ∧ y₂ ≠ 0 ∧
      ∃ lam : ℂ, lam ≠ 0 ∧ A.law0 (grantJ (mumfordPts' x₁ y₁ x₂ y₂)) (A.negP (P0of α)) = lam • P0of α
  gensI : Fin 12 → P9 → ℂ
  gensI_diff : ∀ i, Differentiable ℂ (gensI i)
  gensI_iff : ∀ X, A.OnQ X ↔ ∀ i, gensI i X = 0
  tanC4 : Fin 2 → Fin 12 → Fin 12 → P9 → ℂ
  tanC8 : Fin 2 → Fin 12 → Fin 12 → P9 → ℂ
  tanC4_cont : ∀ j i k, Continuous (tanC4 j i k)
  tanC8_cont : ∀ j i k, Continuous (tanC8 j i k)
  gensI_tan4 : ∀ (j : Fin 2) (i : Fin 12) (X : P9),
    fderiv ℂ (gensI i) X (A.W4 j X) = ∑ k, tanC4 j i k X * gensI k X
  gensI_tan8 : ∀ (j : Fin 2) (i : Fin 12) (X : P9),
    fderiv ℂ (gensI i) X (A.W8 j X) = ∑ k, tanC8 j i k X * gensI k X
  exit4 : ∀ X : P9, A.OnQ X → X 0 = 0 → X 4 ≠ 0 →
    ∃ v : Fin 2 → ℂ, ∃ k : ℕ, 1 ≤ k ∧ k ≤ 3 ∧ exitWord A.W4 v k X ≠ 0
  exit8 : ∀ X : P9, A.OnQ X → X 0 = 0 → X 8 ≠ 0 →
    ∃ v : Fin 2 → ℂ, ∃ k : ℕ, 1 ≤ k ∧ k ≤ 3 ∧ exitWord A.W8 v k X ≠ 0

end LSG.JacAn
