/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Glue

/-!
# Local branches of `y² = f(x)` and the local Abel integrals (genus-generic)

For a polynomial `f` (in Stage A2: `deg f = 2g + 1`, e.g. `f = 4x⁵ + 1`) and a point `(x₀, y₀)` of the affine curve
`y² = f(x)` with `y₀ ≠ 0`, a `LocalBranch f g` packages

* a disc `ball x₀ r` and a holomorphic `Y` on it with `Y² = f`, `Y ≠ 0`, `Y x₀ = y₀`;
* the vector of local Abel integrals `I(x) = ∫_{x₀}^x (ξ^k dξ / Y(ξ))_{k < g}`, analytic, `I x₀ = 0`, `I' = ω`.

`LocalBranch.exists_of_mem` builds one at any such point (`exists_sqrt_branch` + `exists_primitive_ball`).
-/

noncomputable section

open Polynomial Metric Filter Topology

namespace LSG.JacAn

/-- The holomorphic differentials `ω_k = x^k dx / y` (`k < g`) in the branch `Y`, as a vector. -/
def omegaVec (g : ℕ) (Y : ℂ → ℂ) (x : ℂ) : Fin g → ℂ := fun k => x ^ (k : ℕ) / Y x

/-- A local holomorphic branch of `y² = f(x)` over a disc, with its Abel integrals. -/
structure LocalBranch (f : ℂ[X]) (g : ℕ) where
  /-- centre of the disc -/
  x₀ : ℂ
  /-- radius of the disc -/
  r : ℝ
  r_pos : 0 < r
  /-- the branch `y = Y(x)` -/
  Y : ℂ → ℂ
  Y_sq : ∀ x ∈ ball x₀ r, Y x ^ 2 = f.eval x
  Y_ne : ∀ x ∈ ball x₀ r, Y x ≠ 0
  Y_an : AnalyticOnNhd ℂ Y (ball x₀ r)
  /-- the local Abel integrals `∫_{x₀}^x ω` -/
  I : ℂ → (Fin g → ℂ)
  I_zero : I x₀ = 0
  I_deriv : ∀ x ∈ ball x₀ r, HasDerivAt I (omegaVec g Y x) x
  I_an : AnalyticOnNhd ℂ I (ball x₀ r)

namespace LocalBranch

variable {f : ℂ[X]} {g : ℕ}

lemma omegaVec_analyticAt (B : LocalBranch f g) {x : ℂ} (hx : x ∈ ball B.x₀ B.r) :
    AnalyticAt ℂ (omegaVec g B.Y) x := by
  rw [analyticAt_pi_iff]
  intro k
  exact ((analyticAt_id.pow _).div (B.Y_an x hx) (B.Y_ne x hx))

lemma mem_ball_center (B : LocalBranch f g) : B.x₀ ∈ ball B.x₀ B.r := mem_ball_self B.r_pos

/-- **Existence of local branches** at every affine point with `y₀ ≠ 0`. -/
theorem exists_of_mem {x₀ y₀ : ℂ} (hy : y₀ ^ 2 = f.eval x₀) (hy0 : y₀ ≠ 0) :
    ∃ B : LocalBranch f g, B.x₀ = x₀ ∧ B.Y x₀ = y₀ := by
  obtain ⟨Y, hYan, hY0, hYsq⟩ :=
    exists_sqrt_branch (F := fun x => f.eval x)
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) f x₀ (Set.mem_univ _)) hy hy0
  obtain ⟨r₁, hr₁, hYr₁⟩ := hYan.exists_ball_analyticOnNhd
  have hne : ∀ᶠ x in 𝓝 x₀, Y x ≠ 0 := hYan.continuousAt.eventually_ne (hY0 ▸ hy0)
  obtain ⟨r₂, hr₂, hYr₂⟩ := Metric.eventually_nhds_iff_ball.mp hne
  set r := min r₁ r₂ with hr
  have hr0 : 0 < r := lt_min hr₁ hr₂
  have hb₁ : ball x₀ r ⊆ ball x₀ r₁ := ball_subset_ball (min_le_left _ _)
  have hb₂ : ball x₀ r ⊆ ball x₀ r₂ := ball_subset_ball (min_le_right _ _)
  have hω : DifferentiableOn ℂ (omegaVec g Y) (ball x₀ r) := by
    intro x hx
    refine DifferentiableAt.differentiableWithinAt ?_
    rw [differentiableAt_pi]
    intro k
    exact ((differentiableAt_id.pow _).div (hYr₁ x (hb₁ hx)).differentiableAt (hYr₂ x (hb₂ hx)))
  obtain ⟨I, hI0, hId, hIan⟩ := exists_primitive_ball hω
  exact ⟨⟨x₀, r, hr0, Y, fun x _ => hYsq x, fun x hx => hYr₂ x (hb₂ hx), hYr₁.mono hb₁, I, hI0,
    hId, hIan⟩, rfl, hY0⟩

end LocalBranch

end LSG.JacAn
