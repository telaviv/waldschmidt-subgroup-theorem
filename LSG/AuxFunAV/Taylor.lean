/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunAV.Package
import LSG.AuxFunA.LemmaUFac

/-!
# M2.6.2: the Taylor package of a vector block (`VBlockTay`)

The fibre ratio of a vector block is `τ(z) = T_{t₀}(z, 0)/θ_{i₀}(z)` (`tauV`). Since `fc t₀ = i₀` and `T` is affine in
`w` with slope `θ_{fc t}`, on `θ_{i₀} ≠ 0`

  `T_{t₀}(z, w) = θ_{i₀}(z) · (w + τ(z))`   (`T_t₀_eq`),

so `T_{t₀}/θ_{i₀}` is the fibre coordinate `w` shifted by the entire-on-`θ_{i₀} ≠ 0` function `τ`.

**`VBlockTay b ι`** is the base Taylor package `AbBlockTay b.base ι` (the ratios `θ_{is j}/θ_{i₀}` along algebraic
directions have `KS`-controlled Taylor coefficients) plus the same statement for `τ` (`ksT`), with the same
constants.

Design note (M2.md, "M2.6 plan", step 2). The plan derived `ksT` generically from the chart-`i₀` fibre flow
`T_flow` and `ks_quadODE`, with the initial value `τ(0) = 0`. That derivation needs the `KS` data of *all* chart-`i₀`
ratios `θ_c/θ_{i₀}` (the flow `WT` is a quadric in all of `θ`) and the algebraicity of the coefficients of `WT`, which
`AbBlockTay` does not carry. So `ksT` is a field, exactly as the base's `ks` is a field of `AbBlockTay`; the instance
(`aBlockV`, `LSG/JacBlockV/`) proves it from `fibT_flow` and `ks_quadODE`. The value `τ(0)` need not vanish: `KS`
already controls `tco 0 τ = τ(0)`, so the consumer never uses `τ₀ = 0`.
-/

open Complex

noncomputable section

namespace LSG.AuxAV

open LSG.MEB LSG.MEBV LSG.AuxA LSG.Aux

/-- **The fibre ratio** `τ(z) = T_{t₀}(z, 0)/θ_{i₀}(z)`. -/
def tauV (b : VBlock) (z : Fin b.g → ℂ) : ℂ := b.T z 0 b.t₀ / b.base.θ z b.base.i₀

/-- `T_{t₀}(z, w) = θ_{i₀}(z) w + T_{t₀}(z, 0)`. -/
theorem T_t₀_add (b : VBlock) (z : Fin b.g → ℂ) (w : ℂ) :
    b.T z w b.t₀ = b.base.θ z b.base.i₀ * w + b.T z 0 b.t₀ := by
  have h := b.T_add z 0 w b.t₀
  rw [zero_add, b.fc_t₀] at h
  rw [h]; ring

/-- **`T_{t₀} = θ_{i₀} (w + τ)`** on `θ_{i₀} ≠ 0`. -/
theorem T_t₀_eq (b : VBlock) (z : Fin b.g → ℂ) (w : ℂ) (hz : b.base.θ z b.base.i₀ ≠ 0) :
    b.T z w b.t₀ = b.base.θ z b.base.i₀ * (w + tauV b z) := by
  rw [T_t₀_add, tauV]; field_simp

theorem T_zero_eq (b : VBlock) (z : Fin b.g → ℂ) (hz : b.base.θ z b.base.i₀ ≠ 0) :
    b.T z 0 b.t₀ = b.base.θ z b.base.i₀ * tauV b z := by
  rw [T_t₀_eq b z 0 hz, zero_add]

lemma differentiable_T (b : VBlock) (w : ℂ) (t : Fin b.nT) : Differentiable ℂ fun z => b.T z w t := by
  intro z
  have hθ : DifferentiableAt ℂ (fun z => b.base.θ z (b.fc t)) z :=
    ((analyticAt_pi_iff.mp (b.base.θ_analytic z)) (b.fc t)).differentiableAt
  have hΦ : DifferentiableAt ℂ (fun z => b.Φ z t) z :=
    ((analyticAt_pi_iff.mp (b.Φ_analytic z)) t).differentiableAt
  simp only [VBlock.T_apply]
  exact (hθ.mul_const w).sub hΦ

lemma analyticAt_T (b : VBlock) (w : ℂ) (t : Fin b.nT) (z : Fin b.g → ℂ) :
    AnalyticAt ℂ (fun z => b.T z w t) z := by
  have hθ := (analyticAt_pi_iff.mp (b.base.θ_analytic z)) (b.fc t)
  have hΦ := (analyticAt_pi_iff.mp (b.Φ_analytic z)) t
  simp only [VBlock.T_apply]
  exact (hθ.mul analyticAt_const).sub hΦ

variable {K : Type*} [Field K] [NumberField K]

/-- **The Taylor package of a vector block**: the base package, and the same control for the fibre ratio `τ`
along algebraic directions. -/
structure VBlockTay (b : VBlock) (ι : K →+* ℂ) extends AbBlockTay b.base ι where
  ksT : ∀ (v : Fin b.g → ℂ) (Hc : ℝ) (dc : ℕ), 1 ≤ Hc → (∀ j, Sz ι Hc dc (v j)) →
    KS ι A (cB * Hc) E (dc * δ) (fun s => tauV b (s • v))

end LSG.AuxAV
