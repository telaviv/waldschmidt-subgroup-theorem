/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Interface

/-!
# Order-two growth: closure properties

Elementary closure properties of `LSG.GrowthLE 2` (products, sums, scalar multiples, powers) and
the Cauchy estimate: the derivative of an entire function of order `≤ 2` has order `≤ 2`
(`‖f'(z)‖ ≤ max_{|w - z| = 1} ‖f(w)‖`).
-/

open Complex

noncomputable section

namespace LSG.Weierstrass

lemma one_add_norm_rpow_two (z : ℂ) : (1 + ‖z‖) ^ (2 : ℝ) = (1 + ‖z‖) ^ 2 := by
  exact_mod_cast Real.rpow_natCast (1 + ‖z‖) 2

lemma one_le_one_add_norm_sq (z : ℂ) : 1 ≤ (1 + ‖z‖) ^ 2 := by
  have : 1 ≤ 1 + ‖z‖ := by simp
  nlinarith

/-- Order-two growth with the natural-number exponent. -/
lemma growthLE_two_of {g : ℂ → ℂ} (C : ℝ) (h : ∀ z, ‖g z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2)) :
    GrowthLE 2 g :=
  ⟨C, fun z ↦ by rw [one_add_norm_rpow_two]; exact h z⟩

/-- Order-two growth with a nonnegative constant and the natural-number exponent. -/
lemma growthLE_exists_nonneg {g : ℂ → ℂ} (h : GrowthLE 2 g) :
    ∃ C, 0 ≤ C ∧ ∀ z, ‖g z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, le_max_right _ _, fun z ↦ (hC z).trans ?_⟩
  rw [one_add_norm_rpow_two]
  gcongr
  exact le_max_left _ _

lemma growthLE_mul {f g : ℂ → ℂ} (hf : GrowthLE 2 f) (hg : GrowthLE 2 g) :
    GrowthLE 2 (fun z ↦ f z * g z) := by
  obtain ⟨C₁, -, h₁⟩ := growthLE_exists_nonneg hf
  obtain ⟨C₂, -, h₂⟩ := growthLE_exists_nonneg hg
  refine growthLE_two_of (C₁ + C₂) fun z ↦ ?_
  rw [norm_mul, add_mul, Real.exp_add]
  exact mul_le_mul (h₁ z) (h₂ z) (norm_nonneg _) (Real.exp_pos _).le

lemma growthLE_add {f g : ℂ → ℂ} (hf : GrowthLE 2 f) (hg : GrowthLE 2 g) :
    GrowthLE 2 (fun z ↦ f z + g z) := by
  obtain ⟨C₁, hC₁, h₁⟩ := growthLE_exists_nonneg hf
  obtain ⟨C₂, hC₂, h₂⟩ := growthLE_exists_nonneg hg
  refine growthLE_two_of (C₁ + C₂ + 1) fun z ↦ ?_
  have hX := one_le_one_add_norm_sq z
  set X := (1 + ‖z‖) ^ 2
  have e1 : Real.exp (C₁ * X) ≤ Real.exp ((C₁ + C₂) * X) := by gcongr; linarith
  have e2 : Real.exp (C₂ * X) ≤ Real.exp ((C₁ + C₂) * X) := by gcongr; linarith
  have e3 : (2 : ℝ) ≤ Real.exp X := by
    have := Real.add_one_le_exp X
    linarith
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ Real.exp ((C₁ + C₂) * X) + Real.exp ((C₁ + C₂) * X) :=
        add_le_add ((h₁ z).trans e1) ((h₂ z).trans e2)
    _ = 2 * Real.exp ((C₁ + C₂) * X) := by ring
    _ ≤ Real.exp X * Real.exp ((C₁ + C₂) * X) := by gcongr
    _ = Real.exp ((C₁ + C₂ + 1) * X) := by rw [← Real.exp_add]; ring_nf

lemma growthLE_const_mul {f : ℂ → ℂ} (c : ℂ) (hf : GrowthLE 2 f) :
    GrowthLE 2 (fun z ↦ c * f z) := by
  obtain ⟨C, hC, h⟩ := growthLE_exists_nonneg hf
  refine growthLE_two_of (C + ‖c‖) fun z ↦ ?_
  have hX := one_le_one_add_norm_sq z
  set X := (1 + ‖z‖) ^ 2
  have e1 : ‖c‖ ≤ Real.exp (‖c‖ * X) := by
    have := Real.add_one_le_exp (‖c‖ * X)
    nlinarith [norm_nonneg c]
  rw [norm_mul, add_mul, Real.exp_add, mul_comm (Real.exp _)]
  exact mul_le_mul e1 (h z) (norm_nonneg _) (Real.exp_pos _).le

lemma growthLE_neg {f : ℂ → ℂ} (hf : GrowthLE 2 f) : GrowthLE 2 (fun z ↦ -f z) := by
  simpa using growthLE_const_mul (-1) hf

lemma growthLE_sub {f g : ℂ → ℂ} (hf : GrowthLE 2 f) (hg : GrowthLE 2 g) :
    GrowthLE 2 (fun z ↦ f z - g z) := by
  simpa [sub_eq_add_neg] using growthLE_add hf (growthLE_neg hg)

lemma growthLE_pow {f : ℂ → ℂ} (hf : GrowthLE 2 f) (n : ℕ) : GrowthLE 2 (fun z ↦ f z ^ n) := by
  induction n with
  | zero => exact growthLE_two_of 0 fun z ↦ by simp
  | succ n ih => simpa [pow_succ] using growthLE_mul ih hf

lemma growthLE_congr {f g : ℂ → ℂ} (hf : GrowthLE 2 f) (h : ∀ z, f z = g z) : GrowthLE 2 g := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun z ↦ h z ▸ hC z⟩

/-- **Cauchy estimate.** The derivative of an entire function of order `≤ 2` has order `≤ 2`. -/
lemma growthLE_deriv {f : ℂ → ℂ} (hd : Differentiable ℂ f) (hf : GrowthLE 2 f) :
    GrowthLE 2 (deriv f) := by
  obtain ⟨C, hC, h⟩ := growthLE_exists_nonneg hf
  refine growthLE_two_of (4 * C) fun z ↦ ?_
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1)
    (C := Real.exp (C * (2 + ‖z‖) ^ 2)) one_pos hd.diffContOnCl ?_
  · rw [div_one] at this
    refine this.trans (Real.exp_le_exp.mpr ?_)
    have : 0 ≤ ‖z‖ := norm_nonneg z
    have : (2 + ‖z‖) ^ 2 ≤ 4 * (1 + ‖z‖) ^ 2 := by nlinarith
    nlinarith
  · intro w hw
    rw [mem_sphere_iff_norm] at hw
    refine (h w).trans ?_
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have := norm_le_norm_add_norm_sub' w z  -- ‖w‖ ≤ ‖z‖ + ‖w - z‖
      linarith
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) 2) hC)

/-- Iterated Cauchy estimates for the first three derivatives. -/
lemma growthLE_deriv_deriv {f : ℂ → ℂ} (hd : Differentiable ℂ f) (hf : GrowthLE 2 f) :
    GrowthLE 2 (deriv (deriv f)) :=
  growthLE_deriv hd.deriv (growthLE_deriv hd hf)

lemma growthLE_deriv_deriv_deriv {f : ℂ → ℂ} (hd : Differentiable ℂ f) (hf : GrowthLE 2 f) :
    GrowthLE 2 (deriv (deriv (deriv f))) :=
  growthLE_deriv hd.deriv.deriv (growthLE_deriv_deriv hd hf)

end LSG.Weierstrass
