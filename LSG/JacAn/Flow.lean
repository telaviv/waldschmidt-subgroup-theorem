/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.LocalExpDeriv

/-!
# The invariant flow on Grant's P⁸ and uniqueness of its solutions (a4: (U))

* `flowW j X`: the quadratic vector fields of STAGE_A1 §4.2 (`flow_W.json`; A2's index `j = 0, 1` is A1's `1, 2`,
  i.e. `∂/∂z₀`, `∂/∂z₁`), homogeneous of degree 2, with zero `X₀`-component.
* `flowCLM W c X : (Fin 2 → ℂ) →L[ℂ] ℂ⁹`, `v ↦ c (v₀ W₀(X) + v₁ W₁(X))`: the differential of a solution.
* `IsFlowSol W c k V w`: `V` is a chart-`k` solution at `w` (`V w k = 1`, `DV(w) = flowCLM W c (V w)`).
* **`flow_unique`** (U): two solutions of `DV = flowCLM W c V` on a ball that agree at the centre agree on the ball,
  for any `C¹` fields `W` (restriction to real segments + Mathlib's `ODE_solution_unique_of_mem_Icc_right`).
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

/-- Points of `ℂ⁹` (Grant's `P⁸` coordinates `X₀ … X₈`). -/
abbrev P9 := Fin 9 → ℂ

/-- The invariant vector fields in the chart `X₀ = 1` (STAGE_A1 §4.2), as homogeneous quadratic maps. -/
def flowW (j : Fin 2) (X : P9) : P9 :=
  if j = 0 then
    ![0, X 0 * X 4, X 0 * X 5, X 0 * X 6, -3 * X 0 * X 3 + 6 * X 1 ^ 2, -X 0 ^ 2 + 6 * X 1 * X 2,
      4 * X 0 * X 8 + 6 * X 1 * X 3, -2 * X 0 * X 1 + 6 * X 2 * X 3, -3 * X 1 * X 6 + 3 * X 2 * X 5]
  else
    ![0, X 0 * X 5, X 0 * X 6, X 0 * X 7, -X 0 ^ 2 + 6 * X 1 * X 2, 4 * X 0 * X 8 + 6 * X 1 * X 3,
      -2 * X 0 * X 1 + 6 * X 2 * X 3, 4 * X 0 * X 2 + 6 * X 3 ^ 2,
      -(1 / 2) * X 0 * X 4 - (3 / 2) * X 1 * X 7 + (3 / 2) * X 2 * X 6]

/-- The differential of a flow solution: `v ↦ c (v₀ W₀(X) + v₁ W₁(X))`. -/
def flowCLM (W : Fin 2 → P9 → P9) (c : ℂ) (X : P9) : (Fin 2 → ℂ) →L[ℂ] P9 :=
  c • (pr0.smulRight (W 0 X) + pr1.smulRight (W 1 X))

lemma flowCLM_apply (W : Fin 2 → P9 → P9) (c : ℂ) (X : P9) (v : Fin 2 → ℂ) :
    flowCLM W c X v = c • (v 0 • W 0 X + v 1 • W 1 X) := by
  simp [flowCLM]

/-- `V` is a chart-`k` solution of the flow (with speed `c`) at `w`. -/
def IsFlowSol (W : Fin 2 → P9 → P9) (c : ℂ) (k : Fin 9) (V : (Fin 2 → ℂ) → P9) (w : Fin 2 → ℂ) : Prop :=
  V w k = 1 ∧ HasFDerivAt V (flowCLM W c (V w)) w

lemma contDiff_flowW (j : Fin 2) : ContDiff ℝ 1 (flowW j) := by
  rw [contDiff_pi]
  intro i
  unfold flowW
  split_ifs <;> fin_cases i <;> simp <;> fun_prop

/-- Uniqueness for an autonomous `C¹` ODE on `[0, 1]`. -/
lemma ode_unique_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → E} (hF : ContDiff ℝ 1 F) {g₁ g₂ : ℝ → E}
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g₁ (F (g₁ t)) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g₂ (F (g₂ t)) t) (h0 : g₁ 0 = g₂ 0) : g₁ 1 = g₂ 1 := by
  have hc₁ : ContinuousOn g₁ (Icc 0 1) := fun t ht => (h₁ t ht).continuousAt.continuousWithinAt
  have hc₂ : ContinuousOn g₂ (Icc 0 1) := fun t ht => (h₂ t ht).continuousAt.continuousWithinAt
  obtain ⟨R₁, hR₁⟩ := (isCompact_Icc.image_of_continuousOn hc₁).isBounded.subset_closedBall 0
  obtain ⟨R₂, hR₂⟩ := (isCompact_Icc.image_of_continuousOn hc₂).isBounded.subset_closedBall 0
  set R := max R₁ R₂
  obtain ⟨K, hK⟩ := (hF.contDiffOn (s := closedBall (0 : E) R)).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hs₁ : ∀ t ∈ Ico (0 : ℝ) 1, g₁ t ∈ closedBall (0 : E) R := fun t ht =>
    closedBall_subset_closedBall (le_max_left _ _) (hR₁ ⟨t, Ico_subset_Icc_self ht, rfl⟩)
  have hs₂ : ∀ t ∈ Ico (0 : ℝ) 1, g₂ t ∈ closedBall (0 : E) R := fun t ht =>
    closedBall_subset_closedBall (le_max_right _ _) (hR₂ ⟨t, Ico_subset_Icc_self ht, rfl⟩)
  have := ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => closedBall (0 : E) R)
    (fun _ _ => hK) hc₁ (fun t ht => (h₁ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hs₁ hc₂
    (fun t ht => (h₂ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hs₂ h0
  exact this ⟨zero_le_one, le_rfl⟩

/-- **(U) Uniqueness of flow solutions on a ball.** -/
theorem flow_unique (W : Fin 2 → P9 → P9) (hW : ∀ j, ContDiff ℝ 1 (W j)) (c : ℂ)
    {V₁ V₂ : (Fin 2 → ℂ) → P9} {w₀ : Fin 2 → ℂ} {r : ℝ}
    (h₁ : ∀ w ∈ ball w₀ r, HasFDerivAt V₁ (flowCLM W c (V₁ w)) w)
    (h₂ : ∀ w ∈ ball w₀ r, HasFDerivAt V₂ (flowCLM W c (V₂ w)) w) (h0 : V₁ w₀ = V₂ w₀) :
    ∀ w ∈ ball w₀ r, V₁ w = V₂ w := by
  intro w hw
  set ξ := w - w₀
  set ℓ : ℝ → (Fin 2 → ℂ) := fun t => w₀ + (t : ℂ) • ξ
  have hℓ : ∀ t : ℝ, HasDerivAt ℓ ξ t := fun t => by
    have := ((hasDerivAt_id t).ofReal_comp.smul_const ξ).const_add w₀
    exact this.congr_deriv (by simp)
  have hℓmem : ∀ t ∈ Icc (0 : ℝ) 1, ℓ t ∈ ball w₀ r := by
    intro t ht
    have : ℓ t = (1 - t) • w₀ + t • w := by
      simp only [ℓ, ξ]
      ext i; simp [Complex.real_smul]; ring
    rw [this]
    exact (convex_ball w₀ r) (mem_ball_self (pos_of_mem_ball hw)) hw (by linarith [ht.2]) ht.1
      (by ring)
  set F : P9 → P9 := fun X => c • (ξ 0 • W 0 X + ξ 1 • W 1 X)
  have hF : ContDiff ℝ 1 F := by
    have h0 := hW 0; have h1 := hW 1
    exact ((h0.const_smul (ξ 0)).add (h1.const_smul (ξ 1))).const_smul c
  have hg : ∀ {V : (Fin 2 → ℂ) → P9}, (∀ w ∈ ball w₀ r, HasFDerivAt V (flowCLM W c (V w)) w) →
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (V ∘ ℓ) (F ((V ∘ ℓ) t)) t := by
    intro V hV t ht
    have := ((hV (ℓ t) (hℓmem t ht)).restrictScalars ℝ).comp_hasDerivAt t (hℓ t)
    simpa [flowCLM_apply, F] using this
  have h := ode_unique_Icc hF (hg h₁) (hg h₂) (by simpa [ℓ] using h0)
  simpa [ℓ, ξ] using h

end LSG.JacAn
