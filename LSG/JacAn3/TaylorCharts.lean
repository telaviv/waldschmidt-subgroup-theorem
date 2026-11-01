/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.TaylorA

/-!
# A third chart, and the chart cover of the model (STAGE_A3 §3.2)

Charts `X₀ = 1` and `X₄ = 1` do not cover `V(Q)`: the points `(0, …, 0, ±2, 1)` lie on `V(Q)` with `X₀ = X₄ = 0`.
* **`quadA_cover`**: on the explicit model (`quadA`, a copy of A1's `LSG.Jac.quad`), every nonzero point has
  `X₀ ≠ 0`, `X₄ ≠ 0` or `X₈ ≠ 0` (pure algebra);
* **`ThetaData.theta_PF_of_rel`**: a chart `X_k = 1` with quadratics `W` satisfying the Wronskian relation
  `X_k flowW_j(X)_l = X₀ W_j(X)_l − X_l W_j(X)₀` on the model and `W_j(X)_k = 0` (as `W4rel`, `W4_four`) carries the
  projective flow equation of `θ` (identity theorem; needs a point with `θ_k ≠ 0`);
* **`ThetaData.ks_chart_rel`**: hence algebraic Taylor coefficients in that chart (to be used with `k = 8` once A1
  supplies the chart-8 quadratics `W8`).
-/

open Finset Filter Topology Metric Set

noncomputable section

namespace LSG.JacAn

open LSG.Aux

/-- **The charts `X₀`, `X₄`, `X₈` cover the model.** -/
theorem quadA_cover {X : P9} (hQ : ∀ j, quadA X j = 0) (hX : X ≠ 0) : X 0 ≠ 0 ∨ X 4 ≠ 0 ∨ X 8 ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h0, h4, h8⟩ := h
  have q0 := hQ 0; have q1 := hQ 1; have q2 := hQ 2; have q3 := hQ 3; have q4 := hQ 4
  have q5 := hQ 5; have q6 := hQ 6; have q7 := hQ 7; have q8 := hQ 8
  simp only [quadA, Matrix.cons_val, h0, h4, h8] at q0 q1 q2 q3 q4 q5 q6 q7 q8
  have x1 : X 1 = 0 := by
    have : X 1 ^ 3 = 0 := by linear_combination (-1 / 4 : ℂ) * X 1 * q6 + (-1 / 8 : ℂ) * X 6 * q1
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have x2 : X 2 = 0 := by
    have : X 2 ^ 2 = 0 := by linear_combination q0 + X 3 * x1
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have x7 : X 7 = 0 := by
    have : X 7 ^ 2 = 0 := by linear_combination -q8 + 4 * X 3 * x2
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have x6 : X 6 = 0 := by
    have : X 6 ^ 2 = 0 := by linear_combination q7 - 8 * X 2 * x1 + X 5 * x7
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have h35 : X 3 * X 5 = 0 := by linear_combination q3 / 2 + X 7 * x1 / 2 + X 6 * x2 / 2
  have x5 : X 5 = 0 := by
    have : X 5 ^ 3 = 0 := by linear_combination X 5 * q5 + 3 * X 3 * h35
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have x3 : X 3 = 0 := by
    have : X 3 ^ 2 = 0 := by linear_combination -q5 / 3 + X 5 * x5 / 3
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  apply hX
  funext i
  fin_cases i <;> simp [h0, x1, x2, x3, h4, x5, x6, x7, h8]

lemma analyticAt_finsum' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α : Type*} [Fintype α]
    {f : α → E → ℂ} {x : E} (hf : ∀ a, AnalyticAt ℂ (fun w => f a w) x) :
    AnalyticAt ℂ (fun w => ∑ a, f a w) x := by
  classical
  suffices h : ∀ s : Finset α, AnalyticAt ℂ (fun w => ∑ a ∈ s, f a w) x from h univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (analyticAt_const (v := (0 : ℂ)))
  | insert a s ha ih => simp only [sum_insert ha]; exact (hf a).add ih

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}
variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- **The projective flow in a chart `X_k = 1` from a Wronskian relation.** -/
theorem ThetaData.theta_PF_of_rel (W : Fin 2 → P9 → P9) (k : Fin 9)
    (Wc : Fin 2 → Fin 9 → Fin 9 → Fin 9 → ℂ) (hWc : ∀ j X l, W j X l = ∑ a, ∑ b, Wc j l a b * (X a * X b))
    (hrel : ∀ X : P9, A.OnQ X → ∀ (j : Fin 2) (l : Fin 9), X k * flowW j X l = X 0 * W j X l - X l * W j X 0)
    (hkk : ∀ j X, W j X k = 0) {w₂ : Fin 2 → ℂ} (hw₂ : D.theta w₂ k ≠ 0) (w : Fin 2 → ℂ) :
    PFAt W 1 k D.theta w := by
  obtain ⟨w₁, hw₁⟩ := D.exists_theta0_ne
  intro v l
  have hθ : ∀ m, ∀ x, AnalyticAt ℂ (fun w => D.theta w m) x := fun m x =>
    (analyticAt_pi_iff.mp (D.analyticAt_theta x)) m
  have hdθ : ∀ m, ∀ x, AnalyticAt ℂ (fun w => fderiv ℂ D.theta w v m) x := fun m x => by
    have h := (D.analyticAt_theta x).fderiv
    have h2 : AnalyticAt ℂ (fun w => fderiv ℂ D.theta w v) x :=
      (ContinuousLinearMap.apply ℂ P9 v).analyticAt _ |>.comp h
    exact (analyticAt_pi_iff.mp h2) m
  have hWan : ∀ j m, ∀ x, AnalyticAt ℂ (fun w => W j (D.theta w) m) x := fun j m x => by
    simp only [hWc]
    exact analyticAt_finsum' fun a => analyticAt_finsum' fun b =>
      analyticAt_const.mul ((hθ a x).mul (hθ b x))
  -- `θ₀ θ_k · (PF_k defect) ≡ 0`
  set Dk : (Fin 2 → ℂ) → ℂ := fun w => D.theta w k * fderiv ℂ D.theta w v l -
    D.theta w l * fderiv ℂ D.theta w v k - 1 * (v 0 * W 0 (D.theta w) l + v 1 * W 1 (D.theta w) l)
  have hmul : ∀ w, (D.theta w 0 * D.theta w k) * Dk w = 0 := by
    intro w
    have h0 := D.theta_PF0 w v
    have hl := h0 l
    have hk := h0 k
    have hQ := D.theta_onQ w
    have r0l := hrel _ hQ 0 l
    have r1l := hrel _ hQ 1 l
    have r0k := hrel _ hQ 0 k
    have r1k := hrel _ hQ 1 k
    rw [hkk] at r0k r1k
    simp only [Dk]
    linear_combination (D.theta w k) * (D.theta w k) * hl - (D.theta w k) * (D.theta w l) * hk
      + D.theta w k * v 0 * r0l + D.theta w k * v 1 * r1l - D.theta w l * v 0 * r0k - D.theta w l * v 1 * r1k
  -- `θ₀ θ_k ≢ 0`
  have hk0 : ∃ x, D.theta x 0 * D.theta x k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := eq_zero_of_mul_eq_zero_analytic (fun x => hθ 0 x) (fun x => hθ k x) hcon hw₁ w₂
    exact hw₂ this
  obtain ⟨x₀, hx₀⟩ := hk0
  have hDan : ∀ x, AnalyticAt ℂ Dk x := fun x =>
    (((hθ k x).mul (hdθ l x)).sub ((hθ l x).mul (hdθ k x))).sub
      (analyticAt_const.mul (((analyticAt_const.mul (hWan 0 l x))).add (analyticAt_const.mul (hWan 1 l x))))
  have := eq_zero_of_mul_eq_zero_analytic (fun x => (hθ 0 x).mul (hθ k x)) hDan hmul hx₀ w
  simp only [Dk] at this
  exact sub_eq_zero.mp this

/-- **Algebraic Taylor coefficients in a chart given by a Wronskian relation** (e.g. `X₈ = 1`). -/
theorem ThetaData.ks_chart_rel (W : Fin 2 → P9 → P9) (hWs : ∀ j (a : ℂ) X, W j (a • X) = a ^ 2 • W j X)
    (k : Fin 9) (Wc : Fin 2 → Fin 9 → Fin 9 → Fin 9 → ℂ)
    (hWc : ∀ j X l, W j X l = ∑ a, ∑ b, Wc j l a b * (X a * X b))
    (hrel : ∀ X : P9, A.OnQ X → ∀ (j : Fin 2) (l : Fin 9), X k * flowW j X l = X 0 * W j X l - X l * W j X 0)
    (hkk : ∀ j X, W j X k = 0) {HW : ℝ} {dW : ℕ} (hWsz : ∀ j l a b, Sz ι HW dW (Wc j l a b))
    {z₀ c : Fin 2 → ℂ} (hz : D.theta z₀ k ≠ 0) {Hc : ℝ} {dc : ℕ} (hc : ∀ j, Sz ι Hc dc (c j)) {A' B : ℝ}
    {E : ℕ} (h0 : ∀ l, Sz ι A' E (normalize k (D.theta z₀) l)) (hA : 1 ≤ A') (hB1 : 1 ≤ B)
    (hB : 81 * (Hc * HW + Hc * HW) * A' ≤ B) :
    ∀ l, KS ι A' B E (dc * dW * E) (fun s => normalize k (D.theta (z₀ + s • c)) l) :=
  D.ks_chart W hWs k (D.theta_PF_of_rel W k Wc hWc hrel hkk hz) Wc hWc hWsz hz hc h0 hA hB1 hB

end LSG.JacAn
