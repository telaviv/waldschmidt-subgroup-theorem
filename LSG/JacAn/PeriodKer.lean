/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.ExpFollow2
import LSG.JacAn.WCross
import LSG.JacAn.Rank4

/-!
# The period lattice lies in the kernel of `E` (STAGE_A2 §8, route (e′), and the Weierstrass crossing)

* `exists_pert_lift`: the lift `[ζ^e]ℓ` (which crosses the Weierstrass point `y = 0` at `t = 1/2`) is replaced by a
  path with `y ≠ 0` throughout, the same endpoints `(0, −1) → (0, 1)`, `|x| < 1`, and the same Abel integral at
  `t = 1` (`abelAlong_perturb_eq`);
* `exists_special_base`: the base divisor `(0, −1) + (α, 3)`, `α⁵ = 2`, has a germ radius (field `special_hP₀`);
* **`expP_periodic_special`**: at that base, `E (z + z([ζᵉ]γ)) = E z` for all `z` and `e`
  (`expP_periodic_of_paths` applied to the divisor paths `D(t) = (x_e(t), y_e(t)) + (α, 3)`; no `hT`, no `hXn`);
* **`expP_base_indep`**: `E` does not depend on the base (both germs solve the same chart-4 flow with value `e₄`);
* **`lattice_le_ker`**: for every base, `Λ = ⟨z([ζᵉ]γ) : e < 4⟩ ⊆ ker E`, `ker E` is discrete, and the four periods
  are `ℝ`-linearly independent. From standard axioms plus `A1Facts`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology Complex
open scoped LinearAlgebra.Projectivization

namespace LSG.JacAn

open Beta

/-- `|x| ≤ 4/5` along the lifts. -/
lemma norm_liftFun_fst_le (e : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖(liftFun e t).1‖ ≤ 4 / 5 := by
  have hz : ‖zetaN 5‖ = 1 := (zetaN_prim 5 (by norm_num)).norm'_eq_one (by norm_num)
  have hr0 : 0 ≤ rho t := Real.rpow_nonneg (mul_nonneg ht.1 (by linarith [ht.2])) _
  have h5 := rho_pow_five ht.1 ht.2
  have hn : ‖(liftFun e t).1‖ = rho t := by
    simp only [liftFun, norm_mul, norm_neg, norm_pow, hz, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
  rw [hn]
  by_contra hlt
  push Not at hlt
  have h45 : (4 / 5 : ℝ) ^ 5 < rho t ^ 5 := pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  rw [h5] at h45
  nlinarith [sq_nonneg (t - 1 / 2)]

/-- **The perturbed lift of `[ζ^e]ℓ`**: `y ≠ 0` throughout, same endpoints, `|x| < 1`, same Abel integral at
`t = 1`. -/
theorem exists_pert_lift (e : ℕ) :
    ∃ u Y : ℝ → ℂ, ∃ A : ℝ → (Fin 2 → ℂ), IsAbelAlong f₅ 2 u Y A ∧ A 0 = 0 ∧
      ContinuousOn u (Icc 0 1) ∧ u 0 = 0 ∧ Y 0 = -1 ∧ u 1 = 0 ∧ Y 1 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖u t‖ < 1) ∧
      ∀ j : Fin 2, A 1 j = cst e j * Complex.betaIntegral (((j : ℕ) + 1 : ℂ) / 5) (((j : ℕ) + 1 : ℂ) / 5) := by
  obtain ⟨A₀, hA₀0, hA₀W, hA₀1⟩ := abelAlong_liftPath e
  set u₀ : ℝ → ℂ := fun t => (liftFun e t).1 with hu₀def
  have hA₀W' : IsAbelAlongW f₅ 2 u₀ (fun t => 2 * (t : ℂ) - 1) A₀ := hA₀W
  have hu : ContinuousOn u₀ (Icc 0 1) := (continuous_fst.comp (continuous_liftFun e)).continuousOn
  have hYc : Continuous (fun t : ℝ => 2 * (t : ℂ) - 1) :=
    (continuous_const.mul Complex.continuous_ofReal).sub continuous_const
  have hsq : ∀ t ∈ Icc (0 : ℝ) 1, (2 * (t : ℂ) - 1) ^ 2 = f₅.eval (u₀ t) := by
    intro t ht
    rw [f₅_eval]
    exact liftPath_mem_curve e ⟨t, ht⟩
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hY0 : (2 * ((1 / 2 : ℝ) : ℂ) - 1) = 0 := by push_cast; ring
  have hd : (derivative f₅).eval (u₀ (1 / 2)) ≠ 0 := by
    rw [f₅_deriv_eval]
    have h4 : (4 : ℂ) * u₀ (1 / 2) ^ 5 + 1 = 0 := by rw [← f₅_eval, ← hsq _ hhalf, hY0]; ring
    intro h20
    have : u₀ (1 / 2) = 0 := by
      have : u₀ (1 / 2) ^ 4 = 0 := by linear_combination h20 / 20
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    rw [this] at h4; norm_num at h4
  obtain ⟨W, ε, hε, hW⟩ := exists_weier_along (g := 2) (Yp := fun t : ℝ => 2 * (t : ℂ) - 1) hu
    hYc.continuousOn hsq hhalf hY0 hd
  -- continuity of `X_W` at `0`
  obtain ⟨ρ, hρ, hX⟩ := Metric.continuousAt_iff.mp (W.X_an 0 (mem_ball_self W.r_pos)).continuousAt
    (1 / 10) (by norm_num)
  set η : ℝ := min (min (1 / 4) (ε / 4)) (min (W.r / 6) (ρ / 4)) with hη
  have hr := W.r_pos
  have h1 : 0 < η := lt_min (lt_min (by norm_num) (by linarith)) (lt_min (by linarith) (by linarith))
  have hηa : η ≤ 1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hηb : η ≤ ε / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hηc : η ≤ W.r / 6 := (min_le_right _ _).trans (min_le_left _ _)
  have hηd : η ≤ ρ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have h2 : η < 1 / 2 := by linarith
  have h3 : 2 * η < ε := by linarith
  have h4 : 5 * η < W.r := by linarith
  have hdiff := continuous_pertU_diff W hW h1 h2 h3 h4
  have hueq : pertU W u₀ η = fun t => u₀ t + (W.X (pertY η t) - W.X (2 * (t : ℂ) - 1)) := rfl
  have hu' : ContinuousOn (pertU W u₀ η) (Icc 0 1) := by
    rw [hueq]; exact hu.add hdiff.continuousOn
  have hsq' : ∀ t ∈ Icc (0 : ℝ) 1, pertY η t ^ 2 = f₅.eval (pertU W u₀ η t) := fun t ht =>
    pert_sq W hW h1 h2 h3 h4 ht (hsq t ht)
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, pertY η t ≠ 0 := fun t _ => pertY_ne_zero h1
  obtain ⟨A, hA0, hA⟩ := exists_abelAlong (g := 2) hu' (continuous_pertY η).continuousOn hsq' hne
  have hAA : IsAbelAlong f₅ 2 (pertU W u₀ η) (pertY η) A := hA
  have hA1 : A 1 = A₀ 1 := abelAlong_perturb_eq W hW h1 h2 h3 h4 hA₀W' hA₀0 hAA.toW hA0
  -- endpoints
  have far0 : η ≤ |(0 : ℝ) - 1 / 2| := by rw [abs_of_neg (by norm_num)]; linarith
  have far1 : η ≤ |(1 : ℝ) - 1 / 2| := by rw [abs_of_pos (by norm_num)]; linarith
  refine ⟨pertU W u₀ η, pertY η, A, hAA, hA0, hu', ?_, ?_, ?_, ?_, ?_, fun j => by rw [hA1]; exact hA₀1 j⟩
  · rw [pertU_eq_of_far W u₀ far0]; simp [hu₀def, liftFun, rho]
  · rw [pertY_eq_of_far far0]; norm_num
  · rw [pertU_eq_of_far W u₀ far1]; norm_num [hu₀def, liftFun, rho]
  · rw [pertY_eq_of_far far1]; norm_num
  · intro t ht
    have hb : ‖u₀ t‖ ≤ 4 / 5 := norm_liftFun_fst_le e ht
    have hdf : ‖W.X (pertY η t) - W.X (2 * (t : ℂ) - 1)‖ < 1 / 5 := by
      by_cases hfar : η ≤ |t - 1 / 2|
      · rw [pertY_eq_of_far hfar, sub_self, norm_zero]; norm_num
      · push Not at hfar
        have hy1 : dist (pertY η t) 0 < ρ := by
          rw [dist_zero_right]; linarith [norm_pertY_le η t h1.le]
        have hy2 : dist (2 * (t : ℂ) - 1) 0 < ρ := by
          rw [dist_zero_right, norm_two_t_sub_one]; linarith
        have e1 := hX hy1
        have e2 := hX hy2
        rw [dist_eq_norm] at e1 e2
        calc ‖W.X (pertY η t) - W.X (2 * (t : ℂ) - 1)‖
            = ‖(W.X (pertY η t) - W.X 0) - (W.X (2 * (t : ℂ) - 1) - W.X 0)‖ := by congr 1; ring
          _ ≤ ‖W.X (pertY η t) - W.X 0‖ + ‖W.X (2 * (t : ℂ) - 1) - W.X 0‖ := norm_sub_le _ _
          _ < 1 / 5 := by linarith
    rw [hueq]
    calc ‖u₀ t + (W.X (pertY η t) - W.X (2 * (t : ℂ) - 1))‖
        ≤ ‖u₀ t‖ + ‖W.X (pertY η t) - W.X (2 * (t : ℂ) - 1)‖ := norm_add_le _ _
      _ < 1 := by linarith

/-- A constant path on a branch, with Abel integral `0`. -/
lemma abelAlong_const {f : ℂ[X]} {g : ℕ} (B : LocalBranch f g) {x y : ℂ} (hx : x ∈ ball B.x₀ B.r)
    (hy : B.Y x = y) : IsAbelAlong f g (fun _ => x) (fun _ => y) (fun _ => 0) :=
  fun _ _ => ⟨B, 1, one_pos, fun _ _ => ⟨hx, hy, fun _ _ => by simp⟩⟩

/-- Real version of `exists_k_mem`. -/
lemma exists_k_real (C R : ℝ) (hR : 0 < R) : ∃ k : ℕ, ∀ k' ≥ k, C < 2 ^ k' * R := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / R) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, fun k' hk' => ?_⟩
  have : (2 : ℝ) ^ k ≤ 2 ^ k' := pow_le_pow_right₀ (by norm_num) hk'
  rw [div_lt_iff₀ hR] at hk
  nlinarith

variable (A : A1Facts)

/-- **The special base** `(0, −1) + (α, 3)`, `α⁵ = 2`, has a germ radius (from `special_hP₀`). -/
theorem exists_special_base : ∃ α : ℂ, α ^ 5 = 2 ∧ ∃ B₁ B₂ : LocalBranch f₅ 2, B₁.x₀ = 0 ∧ B₁.Y 0 = -1 ∧
    B₂.x₀ = α ∧ B₂.Y α = 3 ∧ ∃ (hp : ((0 : ℂ), α) ∈ dom2 B₁ B₂) (hx : ((0 : ℂ), α).1 ≠ ((0 : ℂ), α).2),
      Nonempty (GermRad A hp hx) := by
  obtain ⟨α, hα, hspec⟩ := A.special_hP₀
  obtain ⟨B₁, h1x, h1y⟩ := LocalBranch.exists_of_mem (f := f₅) (g := 2) (x₀ := 0) (y₀ := -1)
    (by rw [f₅_eval]; norm_num) (by norm_num)
  obtain ⟨B₂, h2x, h2y⟩ := LocalBranch.exists_of_mem (f := f₅) (g := 2) (x₀ := α) (y₀ := 3)
    (by rw [f₅_eval, hα]; norm_num) (by norm_num)
  have hp : ((0 : ℂ), α) ∈ dom2 B₁ B₂ := by
    refine ⟨?_, ?_⟩
    · show (0 : ℂ) ∈ ball B₁.x₀ B₁.r
      rw [h1x]; exact mem_ball_self B₁.r_pos
    · show α ∈ ball B₂.x₀ B₂.r
      rw [h2x]; exact mem_ball_self B₂.r_pos
  have hα0 : α ≠ 0 := by rintro rfl; norm_num at hα
  have hx : ((0 : ℂ), α).1 ≠ ((0 : ℂ), α).2 := fun h => hα0 h.symm
  have hbase : baseP hp hx = grantJ (mumfordPts' 0 (-1) α 3) := by
    simp only [baseP, psiJ, localExp_abel2_self, mumford, mumfordPts', h1y, h2y]
  have hP₀ : A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 ≠ 0 := by
    rw [hbase]; exact hspec
  exact ⟨α, hα, B₁, B₂, h1x, h1y, h2x, h2y, hp, hx, exists_germRad hP₀⟩

variable {A}

/-- **The periods `z([ζᵉ]γ)` are periods of `E` at the special base** (no `hT`, no `hXn`). -/
theorem expP_periodic_special {α : ℂ} (hα : α ^ 5 = 2) {B₁ B₂ : LocalBranch f₅ 2} (h1y : B₁.Y 0 = -1)
    (h2x : B₂.x₀ = α) (h2y : B₂.Y α = 3) {hp : ((0 : ℂ), α) ∈ dom2 B₁ B₂}
    {hx : ((0 : ℂ), α).1 ≠ ((0 : ℂ), α).2} (G : GermRad A hp hx) (e : ℕ) (z : Fin 2 → ℂ) :
    expP G (z + perVec e) = expP G z := by
  obtain ⟨u, Y, A₁, hA, hA0, hu, hu0, hY0, hu1, hY1, hub, hA1⟩ := exists_pert_lift e
  obtain ⟨v, Z, A₁', hA', hA'0, hv, hv0, hZ0, hv1, hZ1, hvb, hA'1⟩ := exists_pert_lift (e + 1)
  have hαB : α ∈ ball B₂.x₀ B₂.r := by rw [h2x]; exact mem_ball_self B₂.r_pos
  have hc := abelAlong_const B₂ hαB h2y
  have hαn : 1 ≤ ‖α‖ := by
    by_contra h
    push Not at h
    have h' : ‖α‖ ^ 5 < 1 := pow_lt_one₀ (norm_nonneg _) h (by norm_num)
    rw [← norm_pow, hα] at h'; norm_num at h'
  have hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u t ≠ (fun _ : ℝ => α) t := fun t ht h => by
    have := hub t ht; rw [h] at this; linarith
  have hdiag' : ∀ t ∈ Icc (0 : ℝ) 1, v t ≠ (fun _ : ℝ => α) t := fun t ht h => by
    have := hvb t ht; rw [h] at this; linarith
  have hstart : mumfordPts (u 0) (Y 0) α 3 = mumford B₁ B₂ ((0 : ℂ), α) := by
    rw [mumford_eq_mumfordPts, hu0, hY0]; simp only; rw [h1y, h2y]
  have hstart' : mumfordPts (v 0) (Z 0) α 3 = mumford B₁ B₂ ((0 : ℂ), α) := by
    rw [mumford_eq_mumfordPts, hv0, hZ0]; simp only; rw [h1y, h2y]
  have hend : mumfordPts (u 1) (Y 1) α 3 = mumfordPts (v 1) (Z 1) α 3 := by rw [hu1, hY1, hv1, hZ1]
  have hper : perVec e = A₁ 1 - A₁' 1 := funext fun j => by
    rw [Pi.sub_apply]; exact period_eq_abelAlong e j hA1 hA'1
  -- a common admissible ball
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn hu)
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA'.continuousOn hv)
  obtain ⟨k₁, hk₁⟩ := exists_k_real C₁ G.ε G.pos
  obtain ⟨k₂, hk₂⟩ := exists_k_real C₂ G.ε G.pos
  obtain ⟨k₃, hk₃⟩ := exists_k_real ‖perVec e‖ G.ε G.pos
  obtain ⟨k₄, hk₄⟩ := exists_k_real ‖z‖ G.ε G.pos
  obtain ⟨k₅, hk₅⟩ := exists_k_real ‖z + perVec e‖ G.ε G.pos
  set k := k₁ + k₂ + k₃ + k₄ + k₅
  have hU : ∀ t ∈ Icc (0 : ℝ) 1, A₁ t + (fun _ : ℝ => (0 : Fin 2 → ℂ)) t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) :=
    fun t ht => by
      change A₁ t + 0 ∈ _
      rw [add_zero, mem_ball_zero_iff]; exact (hC₁ t ht).trans_lt (hk₁ k (by omega))
  have hU' : ∀ t ∈ Icc (0 : ℝ) 1, A₁' t + (fun _ : ℝ => (0 : Fin 2 → ℂ)) t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) :=
    fun t ht => by
      change A₁' t + 0 ∈ _
      rw [add_zero, mem_ball_zero_iff]; exact (hC₂ t ht).trans_lt (hk₂ k (by omega))
  have hcU : (A₁ 1 + (fun _ : ℝ => (0 : Fin 2 → ℂ)) 1) - (A₁' 1 + (fun _ : ℝ => (0 : Fin 2 → ℂ)) 1) ∈
      ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := by
    change (A₁ 1 + 0) - (A₁' 1 + 0) ∈ _
    rw [add_zero, add_zero, ← hper, mem_ball_zero_iff]; exact hk₃ k (by omega)
  have hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := by
    rw [mem_ball_zero_iff]; exact hk₄ k (by omega)
  have hzc : z + ((A₁ 1 + (fun _ : ℝ => (0 : Fin 2 → ℂ)) 1) - (A₁' 1 + (fun _ : ℝ => (0 : Fin 2 → ℂ)) 1)) ∈
      ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := by
    change z + ((A₁ 1 + 0) - (A₁' 1 + 0)) ∈ _
    rw [add_zero, add_zero, ← hper, mem_ball_zero_iff]; exact hk₅ k (by omega)
  have key := expP_periodic_of_paths G k hA hc hA0 rfl hu continuousOn_const hdiag hstart hU hA' hc hA'0 rfl
    hv continuousOn_const hdiag' hstart' hU' hend hcU hz hzc
  simpa only [add_zero, ← hper] using key

/-- **Canonicity**: `E` does not depend on the base divisor. -/
theorem expP_base_indep {B₁ B₂ B₁' B₂' : LocalBranch f₅ 2} {p p' : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂}
    {hx : p.1 ≠ p.2} {hp' : p' ∈ dom2 B₁' B₂'} {hx' : p'.1 ≠ p'.2} (G : GermRad A hp hx)
    (G' : GermRad A hp' hx') : expP G = expP G' := by
  set ρ := min G.ε G'.ε
  have hρ : 0 < ρ := lt_min G.pos G'.pos
  have hgerm : ∀ v ∈ ball (0 : Fin 2 → ℂ) ρ, germ A hp hx v = germ A hp' hx' v :=
    flow_unique A.W4 A.W4_contDiff 1
      (fun v hv => (G.good v (ball_subset_ball (min_le_left _ _) hv)).1.2)
      (fun v hv => (G'.good v (ball_subset_ball (min_le_right _ _) hv)).1.2)
      (G.germ_zero.trans G'.germ_zero.symm)
  funext z
  obtain ⟨k, hk⟩ := exists_k_real ‖z‖ ρ hρ
  have h : ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) ρ := by
    rw [mem_ball_zero_iff, norm_smul, norm_inv, norm_pow]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, inv_mul_lt_iff₀ (by positivity)]
    exact hk k le_rfl
  have hG := ball_subset_ball (min_le_left _ _) h
  have hG' := ball_subset_ball (min_le_right _ _) h
  rw [expP_eq G hG, expP_eq G' hG']
  have heq : expLift A hp hx k z = expLift A hp' hx' k z := by simp only [expLift, hgerm _ h]
  exact (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr ⟨1, by rw [one_smul]; exact heq.symm⟩

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}

/-- **The periods `z([ζᵉ]γ)` are periods of `E`, for every base.** -/
theorem expP_periodic_perVec (G : GermRad A hp hx) (e : ℕ) (z : Fin 2 → ℂ) :
    expP G (z + perVec e) = expP G z := by
  obtain ⟨α, hα, B₁', B₂', -, h1y, h2x, h2y, hp', hx', ⟨G₀⟩⟩ := exists_special_base A
  rw [expP_base_indep G G₀]
  exact expP_periodic_special hα h1y h2x h2y G₀ e z

/-- The kernel of `E` as an additive subgroup. -/
def kerE (G : GermRad A hp hx) : AddSubgroup (Fin 2 → ℂ) where
  carrier := {c | expP G c = expP G 0}
  zero_mem' := rfl
  add_mem' := fun {c c'} hc hc' => by
    change expP G (c + c') = expP G 0
    rw [add_comm, expP_periodic_of_ker G hc c']; exact hc'
  neg_mem' := fun {c} hc => by
    change expP G (-c) = expP G 0
    have := expP_periodic_of_ker G hc (-c)
    rw [neg_add_cancel] at this; exact this.symm

/-- **`Λ ⊆ ker E`, discrete, of rank 4** (standard axioms plus `A1Facts`). For every base: the subgroup generated by
the four periods `z([ζᵉ]γ)`, `e < 4`, lies in `ker E`; `ker E` is discrete; the four periods are `ℝ`-linearly
independent. -/
theorem lattice_le_ker (G : GermRad A hp hx) :
    (∀ e : ℕ, perVec e ∈ kerE G) ∧
    AddSubgroup.closure (Set.range fun e : Fin 4 => perVec (e : ℕ)) ≤ kerE G ∧
    (∃ r > 0, ∀ c c' : Fin 2 → ℂ, c ∈ kerE G → c' ∈ kerE G → dist c c' < r → c = c') ∧
    LinearIndependent ℝ (fun e : Fin 4 => perVec (e : ℕ)) := by
  have hmem : ∀ e : ℕ, perVec e ∈ kerE G := fun e => by
    change expP G (perVec e) = expP G 0
    simpa using expP_periodic_perVec G e 0
  refine ⟨hmem, ?_, expP_ker_discrete G, linearIndependent_perVec⟩
  rw [AddSubgroup.closure_le]
  rintro _ ⟨e, rfl⟩
  exact hmem e

end LSG.JacAn
