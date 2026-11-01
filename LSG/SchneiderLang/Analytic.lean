/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Analytic tools: zeros with multiplicity, Schwarz lemma, Cauchy estimate

* `exists_entire_factor_finset`: an entire function vanishing to order `≥ s` at every point of a
  finite set `Z` is `∏_{w ∈ Z} (z - w)^s` times an entire function.
* `norm_le_of_zeros_pow`: the Schwarz lemma with multiplicities
  `‖G z‖ ≤ B (2r/(R - r))^{s |Z|}` for `‖z‖ ≤ r`, if `‖G‖ ≤ B` on `‖z‖ = R`.
* `norm_iteratedDeriv_le_of_zeros`: combined with Cauchy's estimate on a unit circle.
* `iteratedDeriv_mul_eq_of_vanish`: Leibniz at a zero of order `≥ s`.

Adapted from `StrongSix/Analytic/Schwarz.lean` (same authors, Apache 2.0).
-/

open Complex Metric Set Finset

namespace LSG.SL

theorem dslope_differentiable {g : ℂ → ℂ} (hg : Differentiable ℂ g) (a : ℂ) :
    Differentiable ℂ (dslope g a) := by
  have := (differentiableOn_dslope (s := univ) (f := g) (c := a) Filter.univ_mem).mpr
    hg.differentiableOn
  exact fun w => (this w trivial).differentiableAt Filter.univ_mem

/-- Factor out a zero of order `≥ s`. -/
theorem exists_entire_factor_pow {G : ℂ → ℂ} (hG : Differentiable ℂ G) (a : ℂ) (s : ℕ)
    (hs : (s : ℕ∞) ≤ analyticOrderAt G a) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, G z = (z - a) ^ s * H z := by
  induction s generalizing G with
  | zero => exact ⟨G, hG, fun z => by simp⟩
  | succ s ih =>
    have hGa : G a = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero (by
      intro h
      rw [h] at hs
      simp at hs)
    have hG₁ := dslope_differentiable hG a
    have hfac : ∀ z, G z = (z - a) * dslope G a z := by
      intro z
      have := sub_smul_dslope G a z
      rw [hGa, sub_zero, smul_eq_mul] at this
      exact this.symm
    have hord : analyticOrderAt G a = 1 + analyticOrderAt (dslope G a) a := by
      have : analyticOrderAt G a = analyticOrderAt ((fun z => z - a) * dslope G a) a :=
        congrArg (analyticOrderAt · a) (funext hfac)
      rw [this, analyticOrderAt_mul (by fun_prop) (hG₁.analyticAt a),
        analyticOrderAt_id_sub_const_self]
    have hs' : (s : ℕ∞) ≤ analyticOrderAt (dslope G a) a := by
      rw [hord, Nat.cast_succ, add_comm (s : ℕ∞) 1] at hs
      exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp hs
    obtain ⟨H, hH, hGH⟩ := ih hG₁ hs'
    exact ⟨H, hH, fun z => by rw [hfac, hGH, pow_succ]; ring⟩

/-- Factor out zeros of order `≥ s` at the points of a finite set. -/
theorem exists_entire_factor_finset {G : ℂ → ℂ} (hG : Differentiable ℂ G) (Z : Finset ℂ) (s : ℕ)
    (hs : ∀ w ∈ Z, (s : ℕ∞) ≤ analyticOrderAt G w) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, G z = (∏ w ∈ Z, (z - w) ^ s) * H z := by
  classical
  induction Z using Finset.induction_on with
  | empty => exact ⟨G, hG, by simp⟩
  | insert a Z ha ih =>
    obtain ⟨H₁, hH₁, hGH₁⟩ := ih (fun w hw => hs w (mem_insert_of_mem hw))
    have hP : AnalyticAt ℂ (fun z => ∏ w ∈ Z, (z - w) ^ s) a :=
      Finset.analyticAt_fun_prod _ fun w _ => by fun_prop
    have hPa : (∏ w ∈ Z, (a - w) ^ s) ≠ 0 :=
      prod_ne_zero_iff.mpr fun w hw =>
        pow_ne_zero _ (sub_ne_zero.mpr (by rintro rfl; exact ha hw))
    have hord : analyticOrderAt G a = analyticOrderAt H₁ a := by
      have : analyticOrderAt G a = analyticOrderAt ((fun z => ∏ w ∈ Z, (z - w) ^ s) * H₁) a :=
        congrArg (analyticOrderAt · a) (funext hGH₁)
      rw [this, analyticOrderAt_mul hP (hH₁.analyticAt a),
        (analyticOrderAt_eq_zero (f := fun z => ∏ w ∈ Z, (z - w) ^ s) (z₀ := a)).mpr
          (Or.inr hPa), zero_add]
    obtain ⟨H, hH, hH₁H⟩ := exists_entire_factor_pow hH₁ a s (hord ▸ hs a (mem_insert_self a Z))
    exact ⟨H, hH, fun z => by rw [hGH₁, hH₁H, prod_insert ha]; ring⟩

/-- **Schwarz lemma with multiplicities.** -/
theorem norm_le_of_zeros_pow {G : ℂ → ℂ} (hG : Differentiable ℂ G) (Z : Finset ℂ) (s : ℕ)
    (hs : ∀ w ∈ Z, (s : ℕ∞) ≤ analyticOrderAt G w) {r R B : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hZr : ∀ w ∈ Z, ‖w‖ ≤ r) (hB : ∀ w : ℂ, ‖w‖ = R → ‖G w‖ ≤ B) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖G z‖ ≤ B * (2 * r / (R - r)) ^ (s * Z.card) := by
  obtain ⟨H, hH, hGH⟩ := exists_entire_factor_finset hG Z s hs
  have hR : 0 < R := hr.trans_lt hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hHR : ∀ w : ℂ, ‖w‖ = R → ‖H w‖ ≤ B / (R - r) ^ (s * Z.card) := by
    intro w hw
    have hlow : (R - r) ^ (s * Z.card) ≤ ‖∏ z ∈ Z, (w - z) ^ s‖ := by
      rw [norm_prod, pow_mul, ← Finset.prod_const (s := Z)]
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro z hz
      rw [norm_pow]
      refine pow_le_pow_left₀ hRr.le ?_ _
      have := norm_sub_norm_le w z
      linarith [hZr z hz]
    have hpos : 0 < ‖∏ z ∈ Z, (w - z) ^ s‖ := lt_of_lt_of_le (pow_pos hRr _) hlow
    rw [le_div_iff₀ (pow_pos hRr _)]
    calc ‖H w‖ * (R - r) ^ (s * Z.card) ≤ ‖H w‖ * ‖∏ z ∈ Z, (w - z) ^ s‖ :=
          mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = ‖G w‖ := by rw [hGH w, norm_mul, mul_comm]
      _ ≤ B := hB w hw
  have hHz : ‖H z‖ ≤ B / (R - r) ^ (s * Z.card) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) R)
      isBounded_ball hH.diffContOnCl
    · intro w hw
      rw [frontier_ball (0 : ℂ) hR.ne'] at hw
      exact hHR w (by simpa using hw)
    · rw [closure_ball (0 : ℂ) hR.ne']
      simpa using hz.trans hrR.le
  have hup : ‖∏ z' ∈ Z, (z - z') ^ s‖ ≤ (2 * r) ^ (s * Z.card) := by
    rw [norm_prod, pow_mul, ← Finset.prod_const (s := Z)]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro z' hz'
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have := norm_sub_le z z'
    linarith [hZr z' hz']
  have hB0 : 0 ≤ B / (R - r) ^ (s * Z.card) := (norm_nonneg _).trans hHz
  calc ‖G z‖ = ‖∏ z' ∈ Z, (z - z') ^ s‖ * ‖H z‖ := by rw [hGH z, norm_mul]
    _ ≤ (2 * r) ^ (s * Z.card) * (B / (R - r) ^ (s * Z.card)) :=
        mul_le_mul hup hHz (norm_nonneg _) (by positivity)
    _ = B * (2 * r / (R - r)) ^ (s * Z.card) := by rw [div_pow]; ring

/-- Cauchy's estimate on the unit circle around `w`, combined with the Schwarz lemma. -/
theorem norm_iteratedDeriv_le_of_zeros {G : ℂ → ℂ} (hG : Differentiable ℂ G) (Z : Finset ℂ)
    (s : ℕ) (hs : ∀ w ∈ Z, (s : ℕ∞) ≤ analyticOrderAt G w) {r R B : ℝ} (hrR : r < R)
    (hZr : ∀ w ∈ Z, ‖w‖ ≤ r) (hB : ∀ w : ℂ, ‖w‖ = R → ‖G w‖ ≤ B) {c : ℂ} (hc : ‖c‖ + 1 ≤ r) :
    ‖iteratedDeriv s G c‖ ≤ s.factorial * (B * (2 * r / (R - r)) ^ (s * Z.card)) := by
  have hr : 0 ≤ r := le_trans (by positivity) hc
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le s one_pos
    (c := c) (C := B * (2 * r / (R - r)) ^ (s * Z.card)) hG.diffContOnCl (fun z hz => by
      refine norm_le_of_zeros_pow hG Z s hs hr hrR hZr hB ?_
      have hz1 : ‖z - c‖ = 1 := by simpa [dist_eq_norm] using hz
      have := norm_le_norm_add_norm_sub' z c
      linarith)
  simpa using h

/-- Leibniz rule at a zero of order `≥ s`. -/
theorem iteratedDeriv_mul_eq_of_vanish {φ F : ℂ → ℂ} {w : ℂ} {s : ℕ}
    (hφ : ContDiffAt ℂ s φ w) (hF : ContDiffAt ℂ s F w)
    (hv : ∀ k < s, iteratedDeriv k F w = 0) :
    iteratedDeriv s (φ * F) w = φ w * iteratedDeriv s F w := by
  rw [iteratedDeriv_mul hφ hF, Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [hv (s - i) (by have := Finset.mem_range.mp hi; omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos s)) h

end LSG.SL
