/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import StrongSix.Analytic.Schwarz

/-!
# One-variable interpolation with approximate values

The one-variable step of the grid interpolation that replaces W83's Lemma 2.3 (see
`STAGE3_D2.md`, O2): an entire function that is small at the nodes `Z ⊂ D(0, r)` and bounded on
the circle of radius `R` is small on `D(0, r)`:

  `|f(z)| ≤ #Z·Λ_r·ε + (M + #Z·Λ_R·ε)·(2r/(R − r))^{#Z}`,

where `Λ_r`, `Λ_R` bound the Lagrange basis polynomials on `D(0, r)` and on the circle `|w| = R`.
Proof: `f − (Lagrange interpolant)` vanishes on `Z`; apply StrongSix's Schwarz lemma
`StrongSix.norm_le_of_zeros`.

* `LSG.Aux.lagBasis`, `LSG.Aux.lagInterp`: Lagrange basis and interpolant.
* `LSG.Aux.norm_le_interp`: the estimate.
-/

open Complex Finset

namespace LSG.Aux

/-- The Lagrange basis polynomial of the node `ζ` for the node set `Z`. -/
noncomputable def lagBasis (Z : Finset ℂ) (ζ w : ℂ) : ℂ :=
  ∏ ζ' ∈ Z.erase ζ, (w - ζ') / (ζ - ζ')

/-- The Lagrange interpolant of `f` on the node set `Z`. -/
noncomputable def lagInterp (Z : Finset ℂ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∑ ζ ∈ Z, f ζ * lagBasis Z ζ w

lemma lagBasis_self {Z : Finset ℂ} {ζ : ℂ} : lagBasis Z ζ ζ = 1 := by
  unfold lagBasis
  refine prod_eq_one fun ζ' hζ' => ?_
  have hne : ζ - ζ' ≠ 0 := sub_ne_zero.mpr (ne_of_mem_erase hζ').symm
  exact div_self hne

lemma lagBasis_of_ne {Z : Finset ℂ} {ζ ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ Z) (hne : ζ₀ ≠ ζ) :
    lagBasis Z ζ ζ₀ = 0 := by
  unfold lagBasis
  refine prod_eq_zero (mem_erase.mpr ⟨hne, hζ₀⟩) ?_
  simp

lemma lagInterp_node {Z : Finset ℂ} (f : ℂ → ℂ) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ Z) :
    lagInterp Z f ζ₀ = f ζ₀ := by
  unfold lagInterp
  rw [sum_eq_single ζ₀]
  · rw [lagBasis_self, mul_one]
  · intro ζ _ hζ
    rw [lagBasis_of_ne hζ₀ (Ne.symm hζ), mul_zero]
  · intro h; exact absurd hζ₀ h

lemma differentiable_lagBasis (Z : Finset ℂ) (ζ : ℂ) : Differentiable ℂ (lagBasis Z ζ) := by
  unfold lagBasis
  exact Differentiable.fun_finsetProd fun ζ' _ => (differentiable_id.sub_const _).div_const _

lemma differentiable_lagInterp (Z : Finset ℂ) (f : ℂ → ℂ) : Differentiable ℂ (lagInterp Z f) := by
  unfold lagInterp
  exact Differentiable.fun_sum fun ζ _ => (differentiable_lagBasis Z ζ).const_mul _

lemma norm_lagInterp_le {Z : Finset ℂ} {f : ℂ → ℂ} {ε Λ : ℝ} {w : ℂ}
    (hε : ∀ ζ ∈ Z, ‖f ζ‖ ≤ ε) (hΛ : ∀ ζ ∈ Z, ‖lagBasis Z ζ w‖ ≤ Λ) :
    ‖lagInterp Z f w‖ ≤ Z.card * Λ * ε := by
  unfold lagInterp
  calc ‖∑ ζ ∈ Z, f ζ * lagBasis Z ζ w‖ ≤ ∑ ζ ∈ Z, ‖f ζ * lagBasis Z ζ w‖ := norm_sum_le _ _
    _ ≤ ∑ _ζ ∈ Z, Λ * ε := by
        refine sum_le_sum fun ζ hζ => ?_
        rw [norm_mul, mul_comm Λ]
        exact mul_le_mul (hε ζ hζ) (hΛ ζ hζ) (norm_nonneg _) ((norm_nonneg _).trans (hε ζ hζ))
    _ = Z.card * Λ * ε := by rw [sum_const, nsmul_eq_mul]; ring

/-- **One-variable interpolation with approximate values.** -/
theorem norm_le_interp (f : ℂ → ℂ) (hf : Differentiable ℂ f) (Z : Finset ℂ) {r R ε M Λr ΛR : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hZr : ∀ ζ ∈ Z, ‖ζ‖ ≤ r) (hε : ∀ ζ ∈ Z, ‖f ζ‖ ≤ ε)
    (hM : ∀ w : ℂ, ‖w‖ = R → ‖f w‖ ≤ M)
    (hΛr : ∀ ζ ∈ Z, ∀ w : ℂ, ‖w‖ ≤ r → ‖lagBasis Z ζ w‖ ≤ Λr)
    (hΛR : ∀ ζ ∈ Z, ∀ w : ℂ, ‖w‖ = R → ‖lagBasis Z ζ w‖ ≤ ΛR) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ Z.card * Λr * ε + (M + Z.card * ΛR * ε) * (2 * r / (R - r)) ^ Z.card := by
  set g : ℂ → ℂ := fun w => f w - lagInterp Z f w with hg
  have hgd : Differentiable ℂ g := hf.sub (differentiable_lagInterp Z f)
  have hgZ : ∀ ζ ∈ Z, g ζ = 0 := fun ζ hζ => by simp [hg, lagInterp_node f hζ]
  have hgR : ∀ w : ℂ, ‖w‖ = R → ‖g w‖ ≤ M + Z.card * ΛR * ε := by
    intro w hw
    calc ‖g w‖ ≤ ‖f w‖ + ‖lagInterp Z f w‖ := norm_sub_le _ _
      _ ≤ M + Z.card * ΛR * ε := add_le_add (hM w hw)
          (norm_lagInterp_le hε fun ζ hζ => hΛR ζ hζ w hw)
  have h1 := StrongSix.norm_le_of_zeros g hgd Z hgZ hr hrR hZr hgR hz
  have h2 : ‖lagInterp Z f z‖ ≤ Z.card * Λr * ε :=
    norm_lagInterp_le hε fun ζ hζ => hΛr ζ hζ z hz
  have h3 : f z = lagInterp Z f z + g z := by simp [hg]
  rw [h3]
  exact (norm_add_le _ _).trans (add_le_add h2 h1)

end LSG.Aux
