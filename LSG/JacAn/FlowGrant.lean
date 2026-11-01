/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Flow
import LSG.JacAn.LocalExpODE
import LSG.JacAn.Follow
import LSG.JacAn.PeriodPath

/-!
# (N1): Grant's embedding of the local exponential solves the invariant flow

For the model `f₅ = 4x⁵ + 1`:

* `grantJ m ∈ ℂ⁹`: Grant's 3Θ coordinates of the Mumford point `m = (s₁, s₂, b₁, b₀)` (ABVAR A0.1; equal to A1's
  `LSG.Jac.grant`, i.e. `grantZ / 4`, coordinate by coordinate);
* `chartR1J`, `chartR0J`: the chart relations (A1's `chartR1`, `chartR0`); `chartR_mumfordPts`: they hold at the
  Mumford coordinates of two points of the curve with distinct `x`;
* **`grant_localExp_flow`** (N1): near `z₀`, `z ↦ grantJ (localExp z)` is a chart-0 solution of the flow `flowW` of
  STAGE_A1 §4.2. This is the push-forward of A2's `odeVF` (`localExp_ode`) along `grantJ`, checked here coordinate by
  coordinate (5 of the 16 identities use the chart relations). In particular A1's `flow_W.json` agrees with `odeVF`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

/-- Grant's coordinates `X₀ … X₈` of a Mumford point `m = (s₁, s₂, b₁, b₀)` (= A1's `grant`). -/
def grantJ (m : Fin 4 → ℂ) : P9 :=
  ![1, m 2 ^ 2 / 4 - m 0 ^ 3 + m 0 * m 1, -m 1, m 0,
    -2 * m 3 * m 0 ^ 2 + m 3 * m 1 - m 2 ^ 3 / 4 + m 2 * m 0 ^ 3 - 3 * m 2 * m 0 * m 1,
    -m 3 * m 0 - m 2 * m 1, m 3, m 2, m 3 * m 2 / 2 + 2 * m 0 ^ 2 * m 1]

/-- First chart relation (A1's `chartR1`). -/
def chartR1J (p : Fin 4 → ℂ) : ℂ :=
  -2 * p 3 * p 2 - p 2 ^ 2 * p 0 + 4 * p 0 ^ 4 - 12 * p 0 ^ 2 * p 1 + 4 * p 1 ^ 2

/-- Second chart relation (A1's `chartR0`). -/
def chartR0J (p : Fin 4 → ℂ) : ℂ :=
  -p 3 ^ 2 + p 2 ^ 2 * p 1 - 4 * p 0 ^ 3 * p 1 + 8 * p 0 * p 1 ^ 2 + 1

/-- The chart relations hold at the Mumford coordinates of two points of `y² = 4x⁵ + 1` with distinct `x`. -/
theorem chartR_mumfordPts {x₁ y₁ x₂ y₂ : ℂ} (hx : x₁ ≠ x₂) (h₁ : y₁ ^ 2 = 4 * x₁ ^ 5 + 1)
    (h₂ : y₂ ^ 2 = 4 * x₂ ^ 5 + 1) :
    chartR1J (mumfordPts x₁ y₁ x₂ y₂) = 0 ∧ chartR0J (mumfordPts x₁ y₁ x₂ y₂) = 0 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  constructor
  · simp only [chartR1J, mumfordPts]
    simp
    linear_combination (norm := skip) ((x₂ - x₁) / (x₁ - x₂) ^ 2) * h₁ + ((x₁ - x₂) / (x₁ - x₂) ^ 2) * h₂
    field_simp
    ring
  · simp only [chartR0J, mumfordPts]
    simp
    linear_combination (norm := skip) (x₂ * (x₁ - x₂) / (x₁ - x₂) ^ 2) * h₁ +
      (-x₁ * (x₁ - x₂) / (x₁ - x₂) ^ 2) * h₂
    field_simp
    ring

lemma f₅_eq_quintic : f₅ = quintic 1 0 0 0 0 4 := by
  simp [f₅, quintic]

section N1

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2)

include hp hx in
/-- The chart relations hold along the local exponential. -/
theorem eventually_chartR_localExp :
    ∀ᶠ z in 𝓝 (abel2 B₁ B₂ p),
      chartR1J (localExp hp hx z) = 0 ∧ chartR0J (localExp hp hx z) = 0 := by
  filter_upwards [eventually_abelInv_good hp hx] with z hz
  have h1 := B₁.Y_sq _ hz.1.1
  have h2 := B₂.Y_sq _ hz.1.2
  rw [f₅_eval] at h1 h2
  exact chartR_mumfordPts hz.2 h1 h2

include hp hx in
/-- **(N1)** `grantJ ∘ localExp` is a chart-0 solution of the invariant flow near `z₀`. -/
theorem grant_localExp_flow :
    ∀ᶠ z in 𝓝 (abel2 B₁ B₂ p), IsFlowSol flowW 1 0 (fun z => grantJ (localExp hp hx z)) z := by
  have hf := f₅_eq_quintic
  filter_upwards [localExp_ode hp hx hf 0, localExp_ode hp hx hf 1, localExp_ode hp hx hf 2,
    localExp_ode hp hx hf 3, eventually_chartR_localExp hp hx] with z h0 h1 h2 h3 hr
  refine ⟨by simp [grantJ], ?_⟩
  set m := localExp hp hx z with hm
  obtain ⟨hr1, hr0⟩ := hr
  simp only [chartR1J, chartR0J] at hr1 hr0
  refine hasFDerivAt_pi'' fun i => ?_
  fin_cases i
  · refine (hasFDerivAt_const (1 : ℂ) z).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [flowCLM_apply, flowW, grantJ]
  · have h := ((h2.pow 2).const_mul (1 / 4)).sub (h0.pow 3) |>.add (h0.mul h1)
    convert h using 1
    · funext w; simp [grantJ] <;> ring
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [flowCLM_apply, flowW, grantJ, odeVF, odeB1z0, odeB1z1, odeB0z0, ← hm]
      ring
  · have h := h1.neg
    convert h using 1
    · funext w; simp [grantJ] <;> ring
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [flowCLM_apply, flowW, grantJ, odeVF, odeB1z0, odeB1z1, odeB0z0, ← hm]
      ring
  · convert h0 using 1
    · funext w; simp [grantJ] <;> ring
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [flowCLM_apply, flowW, grantJ, odeVF, odeB1z0, odeB1z1, odeB0z0, ← hm]
      ring
  · have h := (((((h3.mul (h0.pow 2)).const_mul (-2)).add (h3.mul h1)).sub ((h2.pow 3).const_mul (1 / 4))).add
      (h2.mul (h0.pow 3))).sub (((h2.mul h0).mul h1).const_mul 3)
    convert h using 1
    · funext w; simp [grantJ] <;> ring
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [flowCLM_apply, flowW, grantJ, odeVF, odeB1z0, odeB1z1, odeB0z0, ← hm]
      linear_combination (v 0 * (m 0 ^ 2 - 3 / 2 * m 1) - v 1 * (m 0 / 2)) * hr1 + (-3 * v 0 * m 0 - v 1) * hr0
  · have h := ((h3.mul h0).neg).sub (h2.mul h1)
    convert h using 1
    · funext w; simp [grantJ] <;> ring
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [flowCLM_apply, flowW, grantJ, odeVF, odeB1z0, odeB1z1, odeB0z0, ← hm]
      linear_combination -(v 0) * hr0 - v 1 * hr1
  · convert h3 using 1
    · funext w; simp [grantJ] <;> ring
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [flowCLM_apply, flowW, grantJ, odeVF, odeB1z0, odeB1z1, odeB0z0, ← hm]
      linear_combination (-(3 / 2) * v 0) * hr1
  · convert h2 using 1
    · funext w; simp [grantJ] <;> ring
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [flowCLM_apply, flowW, grantJ, odeVF, odeB1z0, odeB1z1, odeB0z0, ← hm]
      ring
  · have h := ((h3.mul h2).const_mul (1 / 2)).add (((h0.pow 2).mul h1).const_mul 2)
    convert h using 1
    · funext w; simp [grantJ] <;> ring
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [flowCLM_apply, flowW, grantJ, odeVF, odeB1z0, odeB1z1, odeB0z0, ← hm]
      ring

end N1

end LSG.JacAn
