/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Exp

/-!
# The projective flow equation (PF)

For an analytic lift `G : ℂ² → ℂ⁹`, `PFAt W κ c G w` is the projective flow equation in the chart `X_c`:

  `G_c · DG(v)_l − G_l · DG(v)_c = κ (v₀ W₀(G)_l + v₁ W₁(G)_l)`  (all `v`, `l`).

* `PFAt.of_flowSol`: chart-`c` flow solutions satisfy PF;
* `PFAt.hasFDerivAt_normalize`: PF + `G_c ≠ 0` ⇒ `G / G_c` is a chart-`c` flow solution;
* `PFAt.smul`, `PFAt.congr`, `PFAt.of_eventually_smul`: PF only depends on the projective class (rescaling by any
  differentiable scalar);
* `PFAt.comp_add`: translation invariance;
* `A1Facts.PFAt_chart`: chart switch 4 → 0 (via `W4rel`, where `G₄ ≠ 0`);
* **`PFAt.of_eventually`**: identity theorem: PF near one point of a connected open set where `G` is analytic gives PF
  on the whole set;
* `A1Facts.PFAt_law0_40`, `A1Facts.PFAt_law0_44`: law 0 with a fixed second argument maps chart-4 flow solutions to
  PF⁰- and PF⁴-lifts (E1 with chart-4 input).
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

/-- **The projective flow equation** in the chart `X_c`. -/
def PFAt (W : Fin 2 → P9 → P9) (κ : ℂ) (c : Fin 9) (G : (Fin 2 → ℂ) → P9) (w : Fin 2 → ℂ) : Prop :=
  ∀ (v : Fin 2 → ℂ) (l : Fin 9), G w c * fderiv ℂ G w v l - G w l * fderiv ℂ G w v c =
    κ * (v 0 * W 0 (G w) l + v 1 * W 1 (G w) l)

variable {W : Fin 2 → P9 → P9} {κ : ℂ} {c : Fin 9} {G G' : (Fin 2 → ℂ) → P9} {w : Fin 2 → ℂ}

lemma PFAt.of_flowSol (hW0 : ∀ j X, W j X c = 0) (h : IsFlowSol W κ c G w) : PFAt W κ c G w := by
  intro v l
  rw [h.2.fderiv, h.1]
  simp [flowCLM_apply, hW0]

lemma PFAt.hasFDerivAt_normalize (hW : ∀ j (a : ℂ) X, W j (a • X) = a ^ 2 • W j X)
    (hG : DifferentiableAt ℂ G w) (hc : G w c ≠ 0) (h : PFAt W κ c G w) :
    HasFDerivAt (fun w => normalize c (G w)) (flowCLM W κ (normalize c (G w))) w :=
  LSG.JacAn.hasFDerivAt_normalize _ hW κ c hG.hasFDerivAt hc h

lemma PFAt.isFlowSol_normalize (hW : ∀ j (a : ℂ) X, W j (a • X) = a ^ 2 • W j X)
    (hG : DifferentiableAt ℂ G w) (hc : G w c ≠ 0) (h : PFAt W κ c G w) :
    IsFlowSol W κ c (fun w => normalize c (G w)) w :=
  ⟨normalize_self c hc, PFAt.hasFDerivAt_normalize hW hG hc h⟩

lemma PFAt.congr (h : PFAt W κ c G w) (he : G =ᶠ[𝓝 w] G') : PFAt W κ c G' w := by
  intro v l
  rw [← he.fderiv_eq, ← he.eq_of_nhds]
  exact h v l

/-- PF is invariant under rescaling by a differentiable scalar. -/
lemma PFAt.smul (hW : ∀ j (a : ℂ) X, W j (a • X) = a ^ 2 • W j X) {μ : (Fin 2 → ℂ) → ℂ}
    (hμ : DifferentiableAt ℂ μ w) (hG : DifferentiableAt ℂ G w) (h : PFAt W κ c G w) :
    PFAt W κ c (fun w => μ w • G w) w := by
  intro v l
  have hd : fderiv ℂ (fun w => μ w • G w) w = μ w • fderiv ℂ G w + (fderiv ℂ μ w).smulRight (G w) :=
    (hμ.hasFDerivAt.smul hG.hasFDerivAt).fderiv
  beta_reduce
  rw [hd]
  have e := h v l
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hW]
  linear_combination μ w ^ 2 * e

/-- PF transfers along an eventual rescaling `G' = λ • G` (with `G_m ≠ 0` at `w`). -/
lemma PFAt.of_eventually_smul (hW : ∀ j (a : ℂ) X, W j (a • X) = a ^ 2 • W j X)
    (hG : AnalyticAt ℂ G w) (hG' : AnalyticAt ℂ G' w) {m : Fin 9} (hm : G w m ≠ 0)
    (he : ∀ᶠ z in 𝓝 w, ∃ μ : ℂ, G' z = μ • G z) (h : PFAt W κ c G w) : PFAt W κ c G' w := by
  set μ : (Fin 2 → ℂ) → ℂ := fun z => G' z m / G z m
  have hGm : AnalyticAt ℂ (fun z => G z m) w := (analyticAt_pi_iff.mp hG) m
  have hG'm : AnalyticAt ℂ (fun z => G' z m) w := (analyticAt_pi_iff.mp hG') m
  have hμ : DifferentiableAt ℂ μ w := (hG'm.div hGm hm).differentiableAt
  have hne : ∀ᶠ z in 𝓝 w, G z m ≠ 0 := hGm.continuousAt.eventually_ne hm
  refine (h.smul hW hμ hG.differentiableAt).congr ?_
  filter_upwards [he, hne] with z ⟨a, ha⟩ hz
  show μ z • G z = G' z
  have : μ z = a := by
    simp only [μ, ha, Pi.smul_apply, smul_eq_mul]; field_simp
  rw [this, ha]

lemma PFAt.comp_add {G : (Fin 2 → ℂ) → P9} {w z : Fin 2 → ℂ} (hG : DifferentiableAt ℂ G (z + w))
    (h : PFAt W κ c G (z + w)) : PFAt W κ c (fun z => G (z + w)) z := by
  intro v l
  have hd : fderiv ℂ (fun z => G (z + w)) z = fderiv ℂ G (z + w) := by
    have h1 : HasFDerivAt (fun z => z + w) (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) z :=
      (hasFDerivAt_id z).add_const w
    have h2 := hG.hasFDerivAt.comp z h1
    rw [show (fun z => G (z + w)) = G ∘ (fun z => z + w) from rfl, h2.fderiv,
      ContinuousLinearMap.comp_id]
  rw [hd]
  exact h v l

/-- The analytic flow fields. -/
lemma analyticOnNhd_flowW (j : Fin 2) : AnalyticOnNhd ℂ (flowW j) univ := by
  intro X _
  rw [analyticAt_pi_iff]
  intro i
  have key : ∀ (f : P9 → ℂ), (∃ P : MvPolynomial (Fin 9) ℂ, ∀ x, f x = MvPolynomial.eval x P) →
      AnalyticAt ℂ f X := by
    rintro f ⟨P, hP⟩
    have := AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) P X (mem_univ _)
    rwa [show (fun x => MvPolynomial.eval x P) = f from funext fun x => (hP x).symm] at this
  apply key
  fin_cases j <;> fin_cases i
  · exact ⟨0, fun x => by simp [flowW]⟩
  · exact ⟨(MvPolynomial.X 0 * MvPolynomial.X 4), fun x => by simp [flowW]⟩
  · exact ⟨(MvPolynomial.X 0 * MvPolynomial.X 5), fun x => by simp [flowW]⟩
  · exact ⟨(MvPolynomial.X 0 * MvPolynomial.X 6), fun x => by simp [flowW]⟩
  · exact ⟨(-3 * MvPolynomial.X 0 * MvPolynomial.X 3 + 6 * MvPolynomial.X 1 ^ 2), fun x => by simp [flowW]⟩
  · exact ⟨(-MvPolynomial.X 0 ^ 2 + 6 * MvPolynomial.X 1 * MvPolynomial.X 2), fun x => by simp [flowW]⟩
  · exact ⟨(4 * MvPolynomial.X 0 * MvPolynomial.X 8 + 6 * MvPolynomial.X 1 * MvPolynomial.X 3), fun x => by simp [flowW]⟩
  · exact ⟨(-2 * MvPolynomial.X 0 * MvPolynomial.X 1 + 6 * MvPolynomial.X 2 * MvPolynomial.X 3), fun x => by simp [flowW]⟩
  · exact ⟨(-3 * MvPolynomial.X 1 * MvPolynomial.X 6 + 3 * MvPolynomial.X 2 * MvPolynomial.X 5), fun x => by simp [flowW]⟩
  · exact ⟨0, fun x => by simp [flowW]⟩
  · exact ⟨(MvPolynomial.X 0 * MvPolynomial.X 5), fun x => by simp [flowW]⟩
  · exact ⟨(MvPolynomial.X 0 * MvPolynomial.X 6), fun x => by simp [flowW]⟩
  · exact ⟨(MvPolynomial.X 0 * MvPolynomial.X 7), fun x => by simp [flowW]⟩
  · exact ⟨(-MvPolynomial.X 0 ^ 2 + 6 * MvPolynomial.X 1 * MvPolynomial.X 2), fun x => by simp [flowW]⟩
  · exact ⟨(4 * MvPolynomial.X 0 * MvPolynomial.X 8 + 6 * MvPolynomial.X 1 * MvPolynomial.X 3), fun x => by simp [flowW]⟩
  · exact ⟨(-2 * MvPolynomial.X 0 * MvPolynomial.X 1 + 6 * MvPolynomial.X 2 * MvPolynomial.X 3), fun x => by simp [flowW]⟩
  · exact ⟨(4 * MvPolynomial.X 0 * MvPolynomial.X 2 + 6 * MvPolynomial.X 3 ^ 2), fun x => by simp [flowW]⟩
  · exact ⟨-(MvPolynomial.C (1 / 2 : ℂ)) * MvPolynomial.X 0 * MvPolynomial.X 4 -
      MvPolynomial.C (3 / 2 : ℂ) * MvPolynomial.X 1 * MvPolynomial.X 7 +
      MvPolynomial.C (3 / 2 : ℂ) * MvPolynomial.X 2 * MvPolynomial.X 6, fun x => by simp [flowW]⟩

/-- **Identity theorem for PF.** -/
theorem PFAt.of_eventually (hWa : ∀ j, AnalyticOnNhd ℂ (W j) univ) {U : Set (Fin 2 → ℂ)}
    (_hU : IsOpen U) (hUc : IsPreconnected U) (hG : AnalyticOnNhd ℂ G U) {w₁ : Fin 2 → ℂ} (hw₁ : w₁ ∈ U)
    (h : ∀ᶠ w in 𝓝 w₁, PFAt W κ c G w) : ∀ w ∈ U, PFAt W κ c G w := by
  intro w hw v l
  set φ : (Fin 2 → ℂ) → ℂ := fun w => G w c * fderiv ℂ G w v l - G w l * fderiv ℂ G w v c -
    κ * (v 0 * W 0 (G w) l + v 1 * W 1 (G w) l)
  have hD : AnalyticOnNhd ℂ (fderiv ℂ G) U := hG.fderiv
  have hev : ∀ m, AnalyticOnNhd ℂ (fun w => fderiv ℂ G w v m) U := fun m z hz => by
    have hL : AnalyticAt ℂ (fun L : (Fin 2 → ℂ) →L[ℂ] P9 => L v m) (fderiv ℂ G z) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 9 => ℂ) m).comp
        (ContinuousLinearMap.apply ℂ P9 v)).analyticAt _
    exact hL.comp (hD z hz)
  have hco : ∀ m, AnalyticOnNhd ℂ (fun w => G w m) U := fun m z hz => (analyticAt_pi_iff.mp (hG z hz)) m
  have hWG : ∀ j m, AnalyticOnNhd ℂ (fun w => W j (G w) m) U := fun j m z hz =>
    (analyticAt_pi_iff.mp ((hWa j (G z) (mem_univ _)).comp (hG z hz))) m
  have hφ : AnalyticOnNhd ℂ φ U := fun z hz => by
    have := (hco c z hz).mul (hev l z hz)
    have := ((hco c z hz).mul (hev l z hz)).sub ((hco l z hz).mul (hev c z hz))
    exact this.sub (analyticAt_const.mul ((analyticAt_const.mul (hWG 0 l z hz)).add
      (analyticAt_const.mul (hWG 1 l z hz))))
  have h0 : φ =ᶠ[𝓝 w₁] 0 := by
    filter_upwards [h] with z hz
    simp only [φ, Pi.zero_apply]
    rw [hz v l]; ring
  have := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hw₁ h0 hw
  simp only [φ, Pi.zero_apply] at this
  linear_combination this

namespace A1Facts

variable (A : A1Facts)

/-- **Chart switch** `4 → 0`, where `G₄ ≠ 0` (via `W4rel`). -/
theorem PFAt_chart (hQ : A.OnQ (G w)) (h4 : G w 4 ≠ 0) (h : PFAt A.W4 κ 4 G w) : PFAt flowW κ 0 G w := by
  intro v l
  have hl := h v l
  have h0 := h v 0
  have r0 := A.W4rel (G w) hQ 0 l
  have r1 := A.W4rel (G w) hQ 1 l
  have key : G w 4 * (G w 0 * fderiv ℂ G w v l - G w l * fderiv ℂ G w v 0 -
      κ * (v 0 * flowW 0 (G w) l + v 1 * flowW 1 (G w) l)) = 0 := by
    linear_combination G w 0 * hl - G w l * h0 - κ * v 0 * r0 - κ * v 1 * r1
  have := (mul_eq_zero.mp key).resolve_left h4
  linear_combination this

/-- **Law 0 maps chart-4 flow solutions to PF⁰-lifts** (E1, input chart 4, output chart 0). -/
theorem PFAt_law0_40 {V : (Fin 2 → ℂ) → P9} {Y : P9} (hV : IsFlowSol A.W4 1 4 V w) (hVQ : A.OnQ (V w))
    (hY : A.OnQ Y) : PFAt flowW 1 0 (fun w => A.law0 (V w) Y) w := by
  obtain ⟨L, hL, hLv⟩ := A.hasFDerivAt_law0_comp Y hV.2
  intro v l
  rw [hL.fderiv]
  have e0 := A.E1_40 (V w) Y hVQ hY 0 l
  have e1 := A.E1_40 (V w) Y hVQ hY 1 l
  rw [hV.1] at e0 e1
  simp only [hLv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination v 0 * e0 + v 1 * e1

/-- **Law 0 maps chart-4 flow solutions to PF⁴-lifts** (E1, input chart 4, output chart 4). -/
theorem PFAt_law0_44 {V : (Fin 2 → ℂ) → P9} {Y : P9} (hV : IsFlowSol A.W4 1 4 V w) (hVQ : A.OnQ (V w))
    (hY : A.OnQ Y) : PFAt A.W4 1 4 (fun w => A.law0 (V w) Y) w := by
  obtain ⟨L, hL, hLv⟩ := A.hasFDerivAt_law0_comp Y hV.2
  intro v l
  rw [hL.fderiv]
  have e0 := A.E1_44 (V w) Y hVQ hY 0 l
  have e1 := A.E1_44 (V w) Y hVQ hY 1 l
  rw [hV.1] at e0 e1
  simp only [hLv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination v 0 * e0 + v 1 * e1

end A1Facts

end LSG.JacAn
