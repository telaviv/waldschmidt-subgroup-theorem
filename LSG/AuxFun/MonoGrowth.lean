/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.ExpCoords

/-!
# Growth of the coordinate monomials of `exp_G` (bridge item (c))

For a monomial `M` of degree `≤ D₀` in the `G_a` coordinates, `≤ D₁` in the `G_m` coordinates and
of degree `D` in each elliptic block,

  `|M(p)| ≤ (1 + |p|)^{D₀} · e^{D₁ |p|} · e^{m D c_W (1 + |p|)²}`,

with `c_W` depending only on the lattices (order-two growth of `σ, σ', σ'', σ'''`, `GrowthLE`).
Hence W83's hypothesis `Σ_λ |ψ_λ|_R ≤ e^U` holds as soon as
`log L + D₀ log(1 + R) + D₁ R + m D c_W (1 + R)² ≤ U`.

* `LSG.Aux.exists_ellW_growth`, `LSG.Aux.exists_mono_growth`, `LSG.Aux.exists_sum_mono_le_exp`.
-/

open Complex Finset LSG.Weierstrass LSG.W88

noncomputable section

namespace LSG.Aux

lemma growthLE_ellW (L : PeriodPair) (t : Fin 3) : LSG.GrowthLE 2 (ellW L t) := by
  have g0 : LSG.GrowthLE 2 (sigma L) := growthLE_sigma L
  have g1 : LSG.GrowthLE 2 (deriv (sigma L)) := growthLE_deriv_sigma L
  have g2 : LSG.GrowthLE 2 (deriv (deriv (sigma L))) := growthLE_deriv_deriv_sigma L
  have g3 : LSG.GrowthLE 2 (deriv (deriv (deriv (sigma L)))) :=
    growthLE_deriv_deriv_deriv_sigma L
  fin_cases t
  · exact growthLE_pow g0 3
  · exact growthLE_mul g0 (growthLE_sub (growthLE_pow g1 2) (growthLE_mul g0 g2))
  · refine growthLE_neg (growthLE_add (growthLE_sub (growthLE_const_mul 2 (growthLE_pow g1 3)) ?_)
      (growthLE_mul (growthLE_pow g0 2) g3))
    exact growthLE_congr (growthLE_const_mul 3 (growthLE_mul (growthLE_mul g0 g1) g2))
      fun z ↦ by ring

/-- Order-two growth of the elliptic coordinates, uniformly in `t`. -/
lemma exists_ellW_growth (L : PeriodPair) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t z, ‖ellW L t z‖ ≤ Real.exp (c * (1 + ‖z‖) ^ 2) := by
  choose C hC0 hC using fun t => growthLE_exists_nonneg (growthLE_ellW L t)
  refine ⟨∑ t, C t, sum_nonneg fun t _ => hC0 t, fun t z => (hC t z).trans ?_⟩
  gcongr
  exact single_le_sum (f := C) (fun t _ => hC0 t) (mem_univ t)

variable {d0 d1 m : ℕ}

/-- **Growth of a monomial.** -/
theorem exists_mono_growth (Ls : Fin m → PeriodPair) :
    ∃ cW : ℝ, 0 ≤ cW ∧ ∀ (D D₀ D₁ : ℕ) (μ : Mono d0 d1 m D), ∑ i, μ.α i ≤ D₀ →
      ∑ i, μ.β i ≤ D₁ → ∀ p : Tan d0 d1 m,
      ‖μ.eval Ls p‖ ≤ (1 + ‖p‖) ^ D₀ * Real.exp (D₁ * ‖p‖) *
        Real.exp (m * D * cW * (1 + ‖p‖) ^ 2) := by
  choose c hc0 hc using fun j => exists_ellW_growth (Ls j)
  refine ⟨∑ j, c j, sum_nonneg fun j _ => hc0 j, fun D D₀ D₁ μ hα hβ p => ?_⟩
  set cW := ∑ j, c j
  have hcW : ∀ j, c j ≤ cW := fun j => single_le_sum (f := c) (fun j _ => hc0 j) (mem_univ j)
  have hp1 : 1 ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
  have hpa : ∀ i, ‖p.1 i‖ ≤ 1 + ‖p‖ := fun i => by
    have := (norm_le_pi_norm p.1 i).trans (norm_fst_le p); linarith
  have hpb : ∀ i, ‖p.2.1 i‖ ≤ ‖p‖ := fun i =>
    (norm_le_pi_norm p.2.1 i).trans ((norm_fst_le p.2).trans (norm_snd_le p))
  have hpz : ∀ j, ‖p.2.2 j‖ ≤ ‖p‖ := fun j =>
    (norm_le_pi_norm p.2.2 j).trans ((norm_snd_le p.2).trans (norm_snd_le p))
  -- the three factors
  have hA : ‖∏ i, p.1 i ^ μ.α i‖ ≤ (1 + ‖p‖) ^ D₀ := by
    rw [norm_prod]
    calc ∏ i, ‖p.1 i ^ μ.α i‖ ≤ ∏ i, (1 + ‖p‖) ^ μ.α i := by
          refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]; gcongr; exact hpa i
      _ = (1 + ‖p‖) ^ (∑ i, μ.α i) := prod_pow_eq_pow_sum _ _ _
      _ ≤ (1 + ‖p‖) ^ D₀ := pow_le_pow_right₀ hp1 hα
  have hB : ‖∏ i, exp (p.2.1 i) ^ μ.β i‖ ≤ Real.exp (D₁ * ‖p‖) := by
    rw [norm_prod]
    calc ∏ i, ‖exp (p.2.1 i) ^ μ.β i‖ ≤ ∏ i, Real.exp ‖p‖ ^ μ.β i := by
          refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]; gcongr
          exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hpb i))
      _ = Real.exp ‖p‖ ^ (∑ i, μ.β i) := prod_pow_eq_pow_sum _ _ _
      _ ≤ Real.exp ‖p‖ ^ D₁ := pow_le_pow_right₀ (Real.one_le_exp (norm_nonneg p)) hβ
      _ = Real.exp (D₁ * ‖p‖) := by rw [← Real.exp_nat_mul]
  have hC : ‖∏ j, ∏ t, ellW (Ls j) t (p.2.2 j) ^ μ.γ j t‖ ≤
      Real.exp (m * D * cW * (1 + ‖p‖) ^ 2) := by
    rw [norm_prod]
    have hj : ∀ j, ‖∏ t, ellW (Ls j) t (p.2.2 j) ^ μ.γ j t‖ ≤
        Real.exp (cW * (1 + ‖p‖) ^ 2) ^ D := by
      intro j
      rw [norm_prod]
      calc ∏ t, ‖ellW (Ls j) t (p.2.2 j) ^ μ.γ j t‖
          ≤ ∏ t, Real.exp (cW * (1 + ‖p‖) ^ 2) ^ μ.γ j t := by
            refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun t _ => ?_
            rw [norm_pow]; gcongr
            refine (hc j t _).trans (Real.exp_le_exp.mpr ?_)
            have : (1 + ‖p.2.2 j‖) ^ 2 ≤ (1 + ‖p‖) ^ 2 := by gcongr; exact hpz j
            exact mul_le_mul (hcW j) this (by positivity) (sum_nonneg fun j _ => hc0 j)
        _ = Real.exp (cW * (1 + ‖p‖) ^ 2) ^ D := by
            rw [prod_pow_eq_pow_sum, μ.hγ j]
    calc ∏ j, ‖∏ t, ellW (Ls j) t (p.2.2 j) ^ μ.γ j t‖
        ≤ ∏ _j : Fin m, Real.exp (cW * (1 + ‖p‖) ^ 2) ^ D :=
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => hj j
      _ = Real.exp (m * D * cW * (1 + ‖p‖) ^ 2) := by
          rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, ← Real.exp_nat_mul]
          push_cast; ring_nf
  unfold Mono.eval
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by positivity)) hC (norm_nonneg _)
    (by positivity)

/-- **W83's growth hypothesis for a family of monomials.** -/
theorem exists_sum_mono_le_exp (Ls : Fin m → PeriodPair) :
    ∃ cW : ℝ, 0 ≤ cW ∧ ∀ (L D D₀ D₁ : ℕ) (μs : Fin L → Mono d0 d1 m D) (R U : ℝ),
      (∀ l, ∑ i, (μs l).α i ≤ D₀) → (∀ l, ∑ i, (μs l).β i ≤ D₁) → 0 ≤ R → 1 ≤ L →
      Real.log L + D₀ * Real.log (1 + R) + D₁ * R + m * D * cW * (1 + R) ^ 2 ≤ U →
      ∀ p : Tan d0 d1 m, ‖p‖ ≤ R → ∑ l, ‖(μs l).eval Ls p‖ ≤ Real.exp U := by
  obtain ⟨cW, hcW0, hcW⟩ := exists_mono_growth (d0 := d0) (d1 := d1) Ls
  refine ⟨cW, hcW0, fun L D D₀ D₁ μs R U hα hβ hR hL hU p hp => ?_⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hR1 : 0 < 1 + R := by linarith
  have hterm : ∀ l, ‖(μs l).eval Ls p‖ ≤
      (1 + R) ^ D₀ * Real.exp (D₁ * R) * Real.exp (m * D * cW * (1 + R) ^ 2) := by
    intro l
    refine (hcW D D₀ D₁ (μs l) (hα l) (hβ l) p).trans ?_
    have h1 : 1 + ‖p‖ ≤ 1 + R := by linarith
    gcongr
  calc ∑ l, ‖(μs l).eval Ls p‖
      ≤ ∑ _l : Fin L, (1 + R) ^ D₀ * Real.exp (D₁ * R) * Real.exp (m * D * cW * (1 + R) ^ 2) :=
        sum_le_sum fun l _ => hterm l
    _ = Real.exp (Real.log L + D₀ * Real.log (1 + R) + D₁ * R + m * D * cW * (1 + R) ^ 2) := by
        have e1 : Real.exp (D₀ * Real.log (1 + R)) = (1 + R) ^ D₀ := by
          rw [Real.exp_nat_mul, Real.exp_log hR1]
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Real.exp_add, Real.exp_add,
          Real.exp_add, Real.exp_log hL0, e1]
        ring
    _ ≤ Real.exp U := Real.exp_le_exp.mpr hU

end LSG.Aux
