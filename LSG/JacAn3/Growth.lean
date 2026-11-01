/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.Factor

/-!
# A3.3: two-sided growth of `log ‖θ‖` (STAGE_A3 §1.3)

* `A1Facts.dup_bounds`: `δ‖X‖⁴ ≤ ‖dup X‖ ≤ C‖X‖⁴` on `V(Q)` (P2 + `onQ_closed` + compactness);
* `dyadic_bound`, `dyadic_bound₀`: `|h(2z) − 4h(z)| ≤ C₀ + a‖z‖²` and `|h| ≤ B` on the unit ball give
  `|h z| ≤ (B + (C₀ + a)(k + 1)) 4ᵏ` for `‖z‖ ≤ 2ᵏ` (resp. `(B + C₀) 4ᵏ` when `a = 0`);
* **`ThetaData.growth_dyadic`**: `|log ‖θ z‖| ≤ K (k + 1) 4ᵏ` for `‖z‖ ≤ 2ᵏ` (two-sided);
* **`ThetaData.fac_growth_dyadic`**: the same for `log ‖fac c z‖ = log ‖θ(z + c)‖ − log ‖θ z‖`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

lemma A1Facts.dup_zero (A : A1Facts) : A.dup 0 = 0 := by
  have := A.dup_smul 0 0
  simpa using this

/-- **`dup` is two-sided homogeneous of degree 4 on the model** (uses P2). -/
theorem A1Facts.dup_bounds (A : A1Facts) : ∃ δ > 0, ∃ C > 0, ∀ X : P9, A.OnQ X →
    δ * ‖X‖ ^ 4 ≤ ‖A.dup X‖ ∧ ‖A.dup X‖ ≤ C * ‖X‖ ^ 4 := by
  have hcont : Continuous A.dup := A.dup_analytic.continuous
  obtain ⟨C₁, hC₁⟩ := (isCompact_sphere (0 : P9) 1).exists_bound_of_continuousOn hcont.continuousOn
  set S := {X : P9 | A.OnQ X} ∩ sphere (0 : P9) 1
  have hS : IsCompact S := (isCompact_sphere (0 : P9) 1).inter_left A.onQ_closed
  obtain ⟨δ, hδ, hδS⟩ : ∃ δ > 0, ∀ u ∈ S, δ ≤ ‖A.dup u‖ := by
    rcases S.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun u hu => by rw [he] at hu; exact absurd hu (Set.notMem_empty u)⟩
    · obtain ⟨u₀, hu₀, hmin⟩ := hS.exists_isMinOn hne (continuous_norm.comp hcont).continuousOn
      have hne0 : u₀ ≠ 0 := by
        intro h; have := hu₀.2; rw [h, mem_sphere_zero_iff_norm, norm_zero] at this; norm_num at this
      exact ⟨‖A.dup u₀‖, norm_pos_iff.mpr (A.dup_ne_zero u₀ hu₀.1 hne0), fun u hu => hmin hu⟩
  refine ⟨δ, hδ, max C₁ 1, by positivity, fun X hX => ?_⟩
  by_cases hX0 : X = 0
  · subst hX0; simp [A.dup_zero]
  set r := ‖X‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr hX0
  set u : P9 := ((r : ℂ)⁻¹) • X
  have hu1 : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    rw [← hr, inv_mul_cancel₀ hr0.ne']
  have huS : u ∈ S := ⟨A.onQ_smul _ _ hX, by rw [mem_sphere_zero_iff_norm]; exact hu1⟩
  have hXu : X = (r : ℂ) • u := by
    simp only [u, smul_smul]; rw [mul_inv_cancel₀ (by exact_mod_cast hr0.ne'), one_smul]
  have hdX : ‖A.dup X‖ = r ^ 4 * ‖A.dup u‖ := by
    rw [hXu, A.dup_smul, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  rw [hdX]
  constructor
  · have := hδS u huS
    nlinarith [pow_pos hr0 4]
  · have h1 : ‖A.dup u‖ ≤ max C₁ 1 := (hC₁ u (by rw [mem_sphere_zero_iff_norm]; exact hu1)).trans
      (le_max_left _ _)
    nlinarith [pow_pos hr0 4]

/-- **Dyadic iteration.** -/
theorem dyadic_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {h : E → ℝ} {B C₀ a : ℝ}
    (hB : ∀ z, ‖z‖ ≤ 1 → |h z| ≤ B) (hd : ∀ z, |h ((2 : ℂ) • z) - 4 * h z| ≤ C₀ + a * ‖z‖ ^ 2)
    (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a) :
    ∀ k : ℕ, ∀ z, ‖z‖ ≤ 2 ^ k → |h z| ≤ (B + (C₀ + a) * (k + 1)) * 4 ^ k := by
  intro k
  induction k with
  | zero => intro z hz; have := hB z (by simpa using hz); simp; nlinarith
  | succ k ih =>
    intro z hz
    set w : E := (2 : ℂ)⁻¹ • z
    have hzw : z = (2 : ℂ) • w := by simp only [w, smul_smul]; norm_num
    have hw : ‖w‖ ≤ 2 ^ k := by
      simp only [w, norm_smul, norm_inv]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2, pow_succ] at *
      rw [inv_mul_le_iff₀ (by norm_num)]; linarith
    have h1 := ih w hw
    have h2 := hd w
    rw [← hzw] at h2
    have hw2 : ‖w‖ ^ 2 ≤ 4 ^ k := by
      calc ‖w‖ ^ 2 ≤ (2 ^ k) ^ 2 := by gcongr
        _ = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (by simp))
    have habs : |h z| ≤ 4 * |h w| + (C₀ + a * ‖w‖ ^ 2) := by
      have := abs_sub_abs_le_abs_sub (h z) (4 * h w)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at this
      linarith
    push_cast
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hw2 ha]

/-- **Dyadic iteration without the quadratic term.** -/
theorem dyadic_bound₀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {h : E → ℝ} {B C₀ : ℝ}
    (hB : ∀ z, ‖z‖ ≤ 1 → |h z| ≤ B) (hd : ∀ z, |h ((2 : ℂ) • z) - 4 * h z| ≤ C₀) (hC₀ : 0 ≤ C₀) :
    ∀ k : ℕ, ∀ z, ‖z‖ ≤ 2 ^ k → |h z| ≤ (B + C₀) * 4 ^ k := by
  have key : ∀ k : ℕ, ∀ z, ‖z‖ ≤ 2 ^ k → |h z| ≤ (B + C₀ / 3) * 4 ^ k - C₀ / 3 := by
    intro k
    induction k with
    | zero => intro z hz; have := hB z (by simpa using hz); simp; linarith
    | succ k ih =>
      intro z hz
      set w : E := (2 : ℂ)⁻¹ • z
      have hzw : z = (2 : ℂ) • w := by simp only [w, smul_smul]; norm_num
      have hw : ‖w‖ ≤ 2 ^ k := by
        simp only [w, norm_smul, norm_inv]
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2, pow_succ] at *
        rw [inv_mul_le_iff₀ (by norm_num)]; linarith
      have h1 := ih w hw
      have h2 := hd w
      rw [← hzw] at h2
      have habs : |h z| ≤ 4 * |h w| + C₀ := by
        have := abs_sub_abs_le_abs_sub (h z) (4 * h w)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at this
        linarith
      rw [pow_succ]; nlinarith
  intro k z hz
  have := key k z hz
  have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  nlinarith

/-- A shift keeps the dyadic bound (with a new constant). -/
theorem shift_bound {E : Type*} [NormedAddCommGroup E] {h : E → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ k : ℕ, ∀ z, ‖z‖ ≤ 2 ^ k → |h z| ≤ K * (k + 1) * 4 ^ k) (c : E) :
    ∃ K' ≥ 0, ∀ k : ℕ, ∀ z, ‖z‖ ≤ 2 ^ k → |h (z + c)| ≤ K' * (k + 1) * 4 ^ k := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖c‖ (by norm_num : (1 : ℝ) < 2)
  refine ⟨K * ((m + 2) * 4 ^ (m + 1)), by positivity, fun k z hz => ?_⟩
  have h2m : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hzc : ‖z + c‖ ≤ 2 ^ (k + m + 1) := by
    calc ‖z + c‖ ≤ ‖z‖ + ‖c‖ := norm_add_le _ _
      _ ≤ 2 ^ k + 2 ^ m := by linarith
      _ ≤ 2 ^ (k + m + 1) := by
        rw [pow_succ, pow_add]; nlinarith
  have h1 := hb (k + m + 1) (z + c) hzc
  calc |h (z + c)| ≤ K * ((k + m + 1 : ℕ) + 1) * 4 ^ (k + m + 1) := h1
    _ ≤ K * ((m + 2) * 4 ^ (m + 1)) * (k + 1) * 4 ^ k := by
        rw [show k + m + 1 = k + (m + 1) by ring, pow_add]
        push_cast
        have h4k : (0 : ℝ) ≤ 4 ^ k := by positivity
        have h4m : (0 : ℝ) ≤ 4 ^ (m + 1) := by positivity
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have : ((k : ℝ) + (m + 1) + 1) ≤ (m + 2) * (k + 1) := by nlinarith
        have := mul_le_mul_of_nonneg_right this (mul_nonneg h4k h4m)
        nlinarith [mul_nonneg hK (mul_nonneg h4k h4m)]

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

lemma ThetaData.continuous_theta : Continuous D.theta :=
  continuous_iff_continuousAt.mpr fun z => (D.analyticAt_theta z).continuousAt

lemma ThetaData.continuous_logNorm : Continuous fun z => Real.log ‖D.theta z‖ :=
  continuous_iff_continuousAt.mpr fun z =>
    (D.continuous_theta.norm.continuousAt).log (norm_ne_zero_iff.mpr (D.theta_ne_zero z))

lemma ThetaData.norm_p2_le (z : Fin 2 → ℂ) : ‖D.p2 z‖ ≤ ‖D.P 2‖ * ‖z‖ ^ 2 := by
  have := (D.P 2).le_opNorm (fun _ => z)
  change ‖D.P 2 (fun _ => z)‖ ≤ _
  simpa [Finset.prod_const] using this

/-- The one-step relation `|h(2z) − 4h(z) + Re p₂(z)| ≤ C₀`. -/
theorem ThetaData.doubling_log : ∃ C₀ ≥ 0, ∀ z,
    |Real.log ‖D.theta ((2 : ℂ) • z)‖ - 4 * Real.log ‖D.theta z‖ + (D.p2 z).re| ≤ C₀ := by
  obtain ⟨δ, hδ, C, hC, hb⟩ := A.dup_bounds
  refine ⟨|Real.log δ| + |Real.log C|, by positivity, fun z => ?_⟩
  have hθ := norm_pos_iff.mpr (D.theta_ne_zero z)
  obtain ⟨h1, h2⟩ := hb _ (D.theta_onQ z)
  have hd0 : 0 < ‖A.dup (D.theta z)‖ := lt_of_lt_of_le (by positivity) h1
  have heq : Real.log ‖D.theta ((2 : ℂ) • z)‖ = -(D.p2 z).re + Real.log ‖A.dup (D.theta z)‖ := by
    rw [D.theta_two_smul, norm_smul, Complex.norm_exp, Real.log_mul (Real.exp_pos _).ne' hd0.ne',
      Real.log_exp, Complex.neg_re]
  have hp4 : Real.log (‖D.theta z‖ ^ 4) = 4 * Real.log ‖D.theta z‖ := by
    rw [Real.log_pow]; norm_num
  have hl1 : Real.log δ + 4 * Real.log ‖D.theta z‖ ≤ Real.log ‖A.dup (D.theta z)‖ := by
    rw [← hp4, ← Real.log_mul hδ.ne' (by positivity)]
    exact Real.log_le_log (by positivity) h1
  have hl2 : Real.log ‖A.dup (D.theta z)‖ ≤ Real.log C + 4 * Real.log ‖D.theta z‖ := by
    rw [← hp4, ← Real.log_mul hC.ne' (by positivity)]
    exact Real.log_le_log hd0 h2
  rw [heq, abs_le]
  constructor <;> linarith [neg_abs_le (Real.log δ), le_abs_self (Real.log C),
    le_abs_self (Real.log δ), neg_abs_le (Real.log C)]

/-- **Two-sided growth of `log ‖θ‖`.** -/
theorem ThetaData.growth_dyadic : ∃ K ≥ 0, ∀ k : ℕ, ∀ z, ‖z‖ ≤ 2 ^ k →
    |Real.log ‖D.theta z‖| ≤ K * (k + 1) * 4 ^ k := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin 2 → ℂ) 1).exists_bound_of_continuousOn
    D.continuous_logNorm.continuousOn
  obtain ⟨C₀, hC₀, hd⟩ := D.doubling_log
  set a := ‖D.P 2‖
  have hB' : ∀ z : Fin 2 → ℂ, ‖z‖ ≤ 1 → |Real.log ‖D.theta z‖| ≤ B := fun z hz => by
    have := hB z (by rw [mem_closedBall_zero_iff]; exact hz)
    rwa [Real.norm_eq_abs] at this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 0 (by simp))
  have hd' : ∀ z, |Real.log ‖D.theta ((2 : ℂ) • z)‖ - 4 * Real.log ‖D.theta z‖| ≤ C₀ + a * ‖z‖ ^ 2 := by
    intro z
    have h1 := hd z
    have h2 : |(D.p2 z).re| ≤ a * ‖z‖ ^ 2 := (Complex.abs_re_le_norm _).trans (D.norm_p2_le z)
    have := abs_sub (Real.log ‖D.theta ((2 : ℂ) • z)‖ - 4 * Real.log ‖D.theta z‖ + (D.p2 z).re)
      (D.p2 z).re
    rw [add_sub_cancel_right] at this
    linarith
  have ha : 0 ≤ a := norm_nonneg _
  refine ⟨B + C₀ + a, by positivity, fun k z hz => ?_⟩
  have := dyadic_bound hB' hd' hC₀ ha k z hz
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h4 : (0 : ℝ) ≤ 4 ^ k := by positivity
  calc |Real.log ‖D.theta z‖| ≤ (B + (C₀ + a) * (k + 1)) * 4 ^ k := this
    _ ≤ (B + C₀ + a) * (k + 1) * 4 ^ k := by
        apply mul_le_mul_of_nonneg_right _ h4; nlinarith

/-- **Two-sided growth of `log ‖fac c‖`.** -/
theorem ThetaData.fac_growth_dyadic {c : Fin 2 → ℂ} (hc : IsPer G c) : ∃ K ≥ 0, ∀ k : ℕ, ∀ z,
    ‖z‖ ≤ 2 ^ k → |Real.log ‖D.fac c z‖| ≤ K * (k + 1) * 4 ^ k := by
  obtain ⟨K, hK, hb⟩ := D.growth_dyadic
  obtain ⟨K', hK', hb'⟩ := shift_bound hK hb c
  refine ⟨K' + K, by positivity, fun k z hz => ?_⟩
  have hθ := norm_pos_iff.mpr (D.theta_ne_zero z)
  have hf := norm_pos_iff.mpr (D.fac_ne_zero hc z)
  have heq : Real.log ‖D.fac c z‖ = Real.log ‖D.theta (z + c)‖ - Real.log ‖D.theta z‖ := by
    rw [D.norm_theta_add hc, Real.log_mul hf.ne' hθ.ne']; ring
  rw [heq]
  have h1 := hb' k z hz
  have h2 := hb k z hz
  calc _ ≤ |Real.log ‖D.theta (z + c)‖| + |Real.log ‖D.theta z‖| := abs_sub _ _
    _ ≤ _ := by nlinarith

end LSG.JacAn
