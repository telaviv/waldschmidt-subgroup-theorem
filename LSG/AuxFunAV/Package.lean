/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunA.Package
import LSG.MEBV.Block

/-!
# M2.6.1: the analytic package of a vector block (`VBlockAn`)

What the M2.6 consumer needs from a `VBlock` beyond the frozen fields (M2.md "M2.6 plan", step 1):
* `an : AbBlockAn b.base`: the base package (`lat ≤ per`, `per ⊆ ℚ·lat`, growth and quasi-periodicity of `θ`);
* `cT`, `growthT`: order-2 growth of the fibre coordinates, linear in `w`
  (for `aBlockV`: `ThetaData.fibT_growth`);
* `span_perV`: the counted fibre periods `{(ω, η ω) : ω ∈ lat}` span `ℂ^{g+1}` (anti-affineness; for `aBlockV`:
  `ThetaData.period_det_ne_zero` plus `perVec_eq`).

Derived here:
* **`VBlockAn.T_qp`**: the fibre coordinates are quasi-periodic with the *same* multiplier as `θ`:
  `T(z + ω, w + η ω) = (κ e^{L z}) • T(z, w)` (from `lift_per` and `exists_fc_ne`); so monomials in `(θ, T)` of a
  fixed block degree share one multiplier (Tier 1′ of Prop 2.1 applies).
-/

open Complex Module

noncomputable section

namespace LSG.AuxAV

open LSG.MEB LSG.MEBV LSG.AuxA

/-- **The analytic package of a vector block.** -/
structure VBlockAn (b : VBlock) where
  an : AbBlockAn b.base
  cT : ℝ
  cT_nonneg : 0 ≤ cT
  growthT : ∀ (z : Fin b.g → ℂ) (w : ℂ) (t : Fin b.nT), ‖b.T z w t‖ ≤ (1 + ‖w‖) * Real.exp (cT * (1 + ‖z‖) ^ 2)
  span_perV : Submodule.span ℂ {p : (Fin b.g → ℂ) × ℂ | p ∈ b.perV ∧ p.1 ∈ an.lat} = ⊤

namespace VBlockAn

variable {b : VBlock} (P : VBlockAn b)

/-- **The fibre coordinates share the multiplier of `θ`.** -/
theorem T_qp {ω : Fin b.g → ℂ} (hω : ω ∈ b.base.per) {κ : ℂ} {L : (Fin b.g → ℂ) →ₗ[ℂ] ℂ}
    (hθ : ∀ z, b.base.θ (z + ω) = (κ * Complex.exp (L z)) • b.base.θ z) (z : Fin b.g → ℂ) (w : ℂ) :
    b.T (z + ω) (w + b.η ω) = (κ * Complex.exp (L z)) • b.T z w := by
  obtain ⟨c, -, hc⟩ := b.lift_per ω hω (z, w)
  obtain ⟨t, ht⟩ := b.exists_fc_ne z
  -- the base components identify `c`
  have hbase : ∀ k, b.base.θ (z + ω) k = c * b.base.θ z k := fun k => by
    have := congrFun hc (Sum.inl k)
    simpa [liftOf] using this
  have hck : c = κ * Complex.exp (L z) := by
    have h1 := hbase (b.fc t)
    rw [hθ z] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    exact (mul_right_cancel₀ ht h1).symm
  funext t'
  have := congrFun hc (Sum.inr t')
  simp only [liftOf, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add] at this
  simp only [VBlock.T, Pi.smul_apply, smul_eq_mul]
  rw [← hck]
  exact this

end VBlockAn

end LSG.AuxAV
