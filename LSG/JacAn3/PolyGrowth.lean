/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.Growth

/-!
# A3.4: real-part growth `o(R³)` forces degree `≤ 2` (STAGE_A3 §1.4, Lemma RP)

* `quad_of_re_dyadic` (one variable): an entire `ψ` with `Re ψ ≤ K (k + 1) 4ᵏ` on `‖t‖ ≤ 2ᵏ` is a polynomial of
  degree `≤ 2` (Borel–Carathéodory + Cauchy estimates + Taylor series);
* **`quadExp_of_growth`** (two variables, no several-variable logarithm needed): an entire nowhere-zero
  `g : ℂ² → ℂ` with `|log ‖g z‖| ≤ K (k + 1) 4ᵏ` on `‖z‖ ≤ 2ᵏ` is `g z = g 0 · exp (L z + M z z)` with
  `L = g(0)⁻¹ Dg(0)` and `M = ½ (g(0)⁻¹ D²g(0) − L ⊗ L)` (one-variable logarithms along the lines `t ↦ t z`).
-/

noncomputable section

open Metric Set Filter Topology Nat

namespace LSG.JacAn

/-- The Cauchy bound for the `n`-th Taylor coefficient, `n ≥ 3`, at radius `2ʲ`. -/
lemma iteratedDeriv_bound {ψ : ℂ → ℂ} (hψ : Differentiable ℂ ψ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ k : ℕ, ∀ t : ℂ, ‖t‖ ≤ 2 ^ k → (ψ t).re ≤ K * (k + 1) * 4 ^ k) {n : ℕ} (hn : 3 ≤ n) (j : ℕ) :
    ‖iteratedDeriv n ψ 0‖ ≤ n ! * (8 * K * (j + 2) + 2 + 3 * ‖ψ 0‖) / 2 ^ j := by
  set R : ℝ := 2 * 2 ^ j
  set M : ℝ := K * ((j + 1 : ℕ) + 1) * 4 ^ (j + 1) + 1
  have hR : 0 < R := by positivity
  have hM : 0 < M := by positivity
  have hmaps : MapsTo ψ (ball 0 R) {z | z.re ≤ M} := fun t ht => by
    have ht' : ‖t‖ ≤ 2 ^ (j + 1) := by
      rw [mem_ball_zero_iff] at ht; rw [pow_succ]; linarith
    have := h (j + 1) t ht'
    simp only [mem_setOf_eq]; linarith
  have hsph : ∀ t ∈ sphere (0 : ℂ) (2 ^ j), ‖ψ t‖ ≤ 2 * M + 3 * ‖ψ 0‖ := by
    intro t ht
    rw [mem_sphere_zero_iff_norm] at ht
    have hbc := Complex.borelCaratheodory hM hψ.differentiableOn hmaps hR
      (by rw [mem_ball_zero_iff, ht]; simp only [R]; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) j])
    rw [ht] at hbc
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have e1 : 2 * M * 2 ^ j / (R - 2 ^ j) = 2 * M := by
      simp only [R]; field_simp; ring
    have e2 : ‖ψ 0‖ * (R + 2 ^ j) / (R - 2 ^ j) = 3 * ‖ψ 0‖ := by
      simp only [R]; field_simp; ring
    linarith
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by positivity : (0 : ℝ) < 2 ^ j) hψ.diffContOnCl hsph
  have h8 : (8 : ℝ) ^ j ≤ (2 ^ j) ^ n := by
    calc (8 : ℝ) ^ j = (2 ^ j) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (2 ^ j) ^ n := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hn
  have hnum : 2 * M + 3 * ‖ψ 0‖ ≤ (8 * K * (j + 2) + 2 + 3 * ‖ψ 0‖) * 4 ^ j := by
    have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
    simp only [M]; push_cast; rw [pow_succ]
    nlinarith [norm_nonneg (ψ 0), mul_nonneg hK (by positivity : (0 : ℝ) ≤ (j + 2) * 4 ^ j)]
  have h84 : (8 : ℝ) ^ j = 4 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
  calc ‖iteratedDeriv n ψ 0‖ ≤ n ! * (2 * M + 3 * ‖ψ 0‖) / (2 ^ j) ^ n := hc
    _ ≤ n ! * ((8 * K * (j + 2) + 2 + 3 * ‖ψ 0‖) * 4 ^ j) / 8 ^ j := by
        gcongr
    _ = n ! * (8 * K * (j + 2) + 2 + 3 * ‖ψ 0‖) / 2 ^ j := by
        rw [h84]; field_simp

/-- **One-variable Lemma RP.** -/
theorem quad_of_re_dyadic {ψ : ℂ → ℂ} (hψ : Differentiable ℂ ψ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ k : ℕ, ∀ t : ℂ, ‖t‖ ≤ 2 ^ k → (ψ t).re ≤ K * (k + 1) * 4 ^ k) (t : ℂ) :
    ψ t = ψ 0 + deriv ψ 0 * t + iteratedDeriv 2 ψ 0 / 2 * t ^ 2 := by
  have hzero : ∀ n, 3 ≤ n → iteratedDeriv n ψ 0 = 0 := by
    intro n hn
    set a : ℝ := n ! * (8 * K)
    set b : ℝ := n ! * (16 * K + 2 + 3 * ‖ψ 0‖)
    have hlim : Tendsto (fun j : ℕ => a * ((j : ℝ) ^ 1 / 2 ^ j) + b * ((j : ℝ) ^ 0 / 2 ^ j)) atTop (𝓝 0) := by
      have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
      have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 2)
      simpa using (h1.const_mul a).add (h0.const_mul b)
    have hle : ∀ j : ℕ, ‖iteratedDeriv n ψ 0‖ ≤
        a * ((j : ℝ) ^ 1 / 2 ^ j) + b * ((j : ℝ) ^ 0 / 2 ^ j) := fun j => by
      have := iteratedDeriv_bound hψ hK h hn j
      convert this using 1
      simp only [a, b, pow_one, pow_zero]; field_simp; ring
    exact norm_le_zero_iff.mp (ge_of_tendsto' hlim hle)
  have hs := Complex.hasSum_taylorSeries_of_entire hψ 0 t
  have hf : HasSum (fun n : ℕ => (n ! : ℂ)⁻¹ • (t - 0) ^ n • iteratedDeriv n ψ 0)
      (∑ n ∈ Finset.range 3, (n ! : ℂ)⁻¹ • (t - 0) ^ n • iteratedDeriv n ψ 0) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      rw [hzero n hn, smul_zero, smul_zero]
  rw [hs.unique hf]
  simp [Finset.sum_range_succ, iteratedDeriv_one]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A one-variable logarithm of a nowhere-zero entire function, normalised at `0`. -/
lemma exists_log_one_var {ϕ : ℂ → ℂ} (hϕ : Differentiable ℂ ϕ) (h0 : ∀ t, ϕ t ≠ 0) :
    ∃ ψ : ℂ → ℂ, Differentiable ℂ ψ ∧ ψ 0 = 0 ∧ (∀ t, HasDerivAt ψ (deriv ϕ t / ϕ t) t) ∧
      ∀ t, ϕ t = ϕ 0 * Complex.exp (ψ t) := by
  have hd : Differentiable ℂ (fun t => deriv ϕ t / ϕ t) := fun t =>
    (((hϕ.analyticAt t).deriv).differentiableAt).div (hϕ t) (h0 t)
  obtain ⟨F, hF⟩ := hd.isExactOn_univ
  have hF' : ∀ t, HasDerivAt F (deriv ϕ t / ϕ t) t := fun t => hF t (mem_univ t)
  refine ⟨fun t => F t - F 0, fun t => ((hF' t).sub_const _).differentiableAt, by simp,
    fun t => (hF' t).sub_const _, ?_⟩
  have hconst : ∀ t, ϕ t * Complex.exp (-(F t - F 0)) = ϕ 0 * Complex.exp (-(F 0 - F 0)) := by
    have hdiff : Differentiable ℂ (fun t => ϕ t * Complex.exp (-(F t - F 0))) := fun t =>
      (hϕ t).mul (((hF' t).sub_const _).differentiableAt.neg.cexp)
    refine fun t => is_const_of_deriv_eq_zero hdiff (fun s => ?_) t 0
    have h1 : HasDerivAt (fun t => ϕ t * Complex.exp (-(F t - F 0))) _ s :=
      ((hϕ s).hasDerivAt).mul (((hF' s).sub_const (F 0)).neg.cexp)
    rw [h1.deriv]
    simp only [Pi.neg_apply]
    field_simp [h0 s]
    ring
  intro t
  have := hconst t
  rw [sub_self, neg_zero, Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- **Two-variable Lemma RP** (for nowhere-zero entire functions). -/
theorem quadExp_of_growth {g : E → ℂ} (hg : ∀ z, AnalyticAt ℂ g z) (hg0 : ∀ z, g z ≠ 0) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ k : ℕ, ∀ z, ‖z‖ ≤ 2 ^ k → |Real.log ‖g z‖| ≤ K * (k + 1) * 4 ^ k) (z : E) :
    g z = g 0 * Complex.exp ((g 0)⁻¹ * fderiv ℂ g 0 z +
      (1 / 2) * ((g 0)⁻¹ * fderiv ℂ (fderiv ℂ g) 0 z z - ((g 0)⁻¹ * fderiv ℂ g 0 z) ^ 2)) := by
  set ϕ : ℂ → ℂ := fun t => g (t • z)
  have hline : ∀ t : ℂ, HasDerivAt (fun s : ℂ => s • z) z t := fun t => by
    simpa using (hasDerivAt_id t).smul_const z
  have hϕd : ∀ t, HasDerivAt ϕ (fderiv ℂ g (t • z) z) t := fun t =>
    ((hg (t • z)).differentiableAt.hasFDerivAt).comp_hasDerivAt t (hline t)
  have hϕ : Differentiable ℂ ϕ := fun t => (hϕd t).differentiableAt
  have hϕ0 : ∀ t, ϕ t ≠ 0 := fun t => hg0 _
  have hderϕ : deriv ϕ = fun t => fderiv ℂ g (t • z) z := funext fun t => (hϕd t).deriv
  have hϕdd : HasDerivAt (fun t : ℂ => fderiv ℂ g (t • z) z) (fderiv ℂ (fderiv ℂ g) 0 z z) 0 := by
    have hc : HasDerivAt (fun t : ℂ => fderiv ℂ g (t • z)) (fderiv ℂ (fderiv ℂ g) ((0 : ℂ) • z) z) 0 :=
      (((hg _).fderiv).differentiableAt.hasFDerivAt).comp_hasDerivAt 0 (hline 0)
    rw [zero_smul] at hc
    simpa using hc.clm_apply (hasDerivAt_const (0 : ℂ) z)
  obtain ⟨ψ, hψ, hψ0, hψd, hψe⟩ := exists_log_one_var hϕ hϕ0
  -- growth of `Re ψ`
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖z‖ (by norm_num : (1 : ℝ) < 2)
  set B0 := |Real.log ‖g 0‖|
  have hre : ∀ t, (ψ t).re = Real.log ‖ϕ t‖ - Real.log ‖ϕ 0‖ := fun t => by
    have h1 := congrArg norm (hψe t)
    rw [norm_mul, Complex.norm_exp] at h1
    rw [h1, Real.log_mul (norm_ne_zero_iff.mpr (hϕ0 0)) (Real.exp_pos _).ne', Real.log_exp]; ring
  have hgrow : ∀ k : ℕ, ∀ t : ℂ, ‖t‖ ≤ 2 ^ k → (ψ t).re ≤ (K * ((m + 1) * 4 ^ m) + B0) * (k + 1) * 4 ^ k := by
    intro k t ht
    have htz : ‖t • z‖ ≤ 2 ^ (k + m) := by
      rw [norm_smul, pow_add]; exact mul_le_mul ht hm.le (norm_nonneg _) (by positivity)
    have h1 := hb (k + m) _ htz
    have hϕ0' : ϕ 0 = g 0 := by simp [ϕ]
    rw [hre t, hϕ0']
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h4k : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have h4m : (0 : ℝ) ≤ 4 ^ m := by positivity
    have hkm : ((k + m : ℕ) : ℝ) + 1 ≤ (m + 1) * (k + 1) := by push_cast; nlinarith
    have e : (4 : ℝ) ^ (k + m) = 4 ^ k * 4 ^ m := pow_add _ _ _
    have hB0 : 0 ≤ B0 := abs_nonneg _
    have h2 : K * (((k + m : ℕ) : ℝ) + 1) * 4 ^ (k + m) ≤ K * ((m + 1) * 4 ^ m) * (k + 1) * 4 ^ k := by
      rw [e]
      have := mul_le_mul_of_nonneg_right hkm (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ k) h4m)
      have hh : (((k + m : ℕ) : ℝ) + 1) * (4 ^ k * 4 ^ m) ≤ ((m + 1) * 4 ^ m) * (k + 1) * 4 ^ k := by
        calc _ ≤ _ := this
          _ = _ := by ring
      calc K * (((k + m : ℕ) : ℝ) + 1) * (4 ^ k * 4 ^ m)
          = K * ((((k + m : ℕ) : ℝ) + 1) * (4 ^ k * 4 ^ m)) := by ring
        _ ≤ K * (((m + 1) * 4 ^ m) * (k + 1) * 4 ^ k) := mul_le_mul_of_nonneg_left hh hK
        _ = _ := by ring
    have h1k : (1 : ℝ) ≤ (k + 1) * 4 ^ k := by nlinarith
    have h3 : B0 ≤ B0 * (k + 1) * 4 ^ k := by
      calc B0 = B0 * 1 := by ring
        _ ≤ B0 * ((k + 1) * 4 ^ k) := mul_le_mul_of_nonneg_left h1k hB0
        _ = _ := by ring
    have hl1 := (le_abs_self (Real.log ‖g (t • z)‖)).trans h1
    have hl2 := neg_abs_le (Real.log ‖g 0‖)
    show Real.log ‖g (t • z)‖ - Real.log ‖g 0‖ ≤ _
    nlinarith
  have hq := quad_of_re_dyadic hψ (by positivity) hgrow 1
  -- the coefficients
  have hd1 : deriv ψ 0 = (g 0)⁻¹ * fderiv ℂ g 0 z := by
    rw [(hψd 0).deriv, hderϕ]; simp [ϕ, div_eq_inv_mul]
  have hderψ : deriv ψ = fun t => deriv ϕ t / ϕ t := funext fun t => (hψd t).deriv
  have hd2 : iteratedDeriv 2 ψ 0 = (g 0)⁻¹ * fderiv ℂ (fderiv ℂ g) 0 z z - ((g 0)⁻¹ * fderiv ℂ g 0 z) ^ 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderψ]
    have hq' : HasDerivAt (fun t => deriv ϕ t / ϕ t)
        ((fderiv ℂ (fderiv ℂ g) 0 z z * ϕ 0 - fderiv ℂ g ((0 : ℂ) • z) z * fderiv ℂ g ((0 : ℂ) • z) z) /
          ϕ 0 ^ 2) 0 := by
      rw [hderϕ]; exact hϕdd.div (hϕd 0) (hϕ0 0)
    rw [hq'.deriv]
    simp only [ϕ, zero_smul]
    field_simp [hg0 0]
  have hz1 : ϕ 1 = g z := by simp [ϕ]
  rw [← hz1, hψe 1, hq, hψ0, hd1, hd2]
  have h00 : ϕ 0 = g 0 := by simp [ϕ]
  rw [h00]
  congr 2
  ring

end LSG.JacAn
