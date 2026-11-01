/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Branch
import LSG.JacAn.BetaPeriods

/-!
# Curve integrals on a branch disc (building block of the continuation lemma, ABVAR §2.2 a6)

For a `C¹` path `t ↦ (u(t), Y(u(t)))` on the curve that stays in the disc of a local branch `B`, the curve integral
of `ω_j = x^j dx/y` (Mathlib's `curveIntegral`, the form `Beta.omegaJ j` of `BetaPeriods`) is the difference of the
local Abel integrals:

* `integral_omega_eq_sub`: `∫₀¹ u^j u'/Y(u) dt = I_j(u 1) − I_j(u 0)`;
* `curveIntegral_eq_sub`: the same for `∫ᶜ p in γ, omegaJ j p` when `γ.extend = (u, Y ∘ u)` on `[0, 1]`.

This ties the local exponential (`Abel2`) to the period computation (`BetaPeriods`): the continuation lemma a6 chains
it over a cover of a path by branch discs (plus charts at the Weierstrass points and at `∞`; see STAGE_A2.md).
-/

noncomputable section

open Polynomial Metric Set MeasureTheory Filter Topology

namespace LSG.JacAn

variable {f : ℂ[X]} {g : ℕ}

/-- **FTC on a branch disc.** -/
theorem integral_omega_eq_sub (B : LocalBranch f g) {u u' : ℝ → ℂ}
    (hu : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt u (u' t) t) (hu' : ContinuousOn u' (uIcc 0 1))
    (hball : ∀ t ∈ uIcc (0 : ℝ) 1, u t ∈ ball B.x₀ B.r) (j : Fin g) :
    ∫ t in (0 : ℝ)..1, u t ^ (j : ℕ) / B.Y (u t) * u' t = B.I (u 1) j - B.I (u 0) j := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => B.I (u t) j)
    (fun t ht => ?_) ?_
  · have h := hasDerivAt_pi.mp ((B.I_deriv _ (hball t ht)).scomp t (hu t ht)) j
    refine h.congr_deriv ?_
    rw [Pi.smul_apply, smul_eq_mul, omegaVec]; ring
  · apply ContinuousOn.intervalIntegrable
    have hcu : ContinuousOn u (uIcc 0 1) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
    refine ContinuousOn.mul (ContinuousOn.div (hcu.pow _) ?_ fun t ht => B.Y_ne _ (hball t ht)) hu'
    exact fun t ht =>
      ((B.Y_an _ (hball t ht)).continuousAt.comp (hu t ht).continuousAt).continuousWithinAt

/-- **Curve integrals of `x^j dx/y` on a branch disc** are differences of the local Abel integrals. -/
theorem curveIntegral_eq_sub (B : LocalBranch f g) {P Q : ℂ × ℂ} (γ : Path P Q) {u u' : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t = (u t, B.Y (u t)))
    (hu : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt u (u' t) t) (hu' : ContinuousOn u' (uIcc 0 1))
    (hball : ∀ t ∈ uIcc (0 : ℝ) 1, u t ∈ ball B.x₀ B.r) (j : Fin g) :
    ∫ᶜ p in γ, Beta.omegaJ j p = B.I (u 1) j - B.I (u 0) j := by
  rw [curveIntegral_def, ← integral_omega_eq_sub B hu hu' hball j]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(countable_singleton (1 : ℝ)).ae_notMem volume] with t ht1 hmem
  rw [uIoc_of_le zero_le_one] at hmem
  have h0 : 0 < t := hmem.1
  have h1 : t < 1 := lt_of_le_of_ne hmem.2 ht1
  have htI : t ∈ uIcc (0 : ℝ) 1 := by rw [uIcc_of_le zero_le_one]; exact ⟨h0.le, h1.le⟩
  have hev : γ.extend =ᶠ[𝓝 t] fun s => (u s, B.Y (u s)) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with s hs using hγ s (Ioo_subset_Icc_self hs)
  have hY : HasDerivAt (fun s => B.Y (u s)) (deriv B.Y (u t) * u' t) t :=
    ((B.Y_an _ (hball t htI)).differentiableAt.hasDerivAt).comp t (hu t htI)
  have hd : derivWithin γ.extend unitInterval t = (u' t, deriv B.Y (u t) * u' t) := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds h0 h1), hev.deriv_eq, ((hu t htI).prodMk hY).deriv]
  rw [curveIntegralFun_def, hd, hev.eq_of_nhds]
  simp [Beta.omegaJ]

end LSG.JacAn
