/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.FibreFTC
import LSG.JacAn4.Surj

/-!
# M2.3 (N5): the fibre period formula `η̄([ζ^e]γ) = (3/5) ζ^{4e} perB5`

**`ThetaData.etaB_perVec`**: for every `θ`-datum (any base) and `e < 4`,

  `η̄(perVec e) = (3/5) (ζ₅^e)⁴ · perB5`.

Proof: the two perturbed period paths `[ζ^e]ℓ`, `[ζ^{e+1}]ℓ` (`exists_pert_lift24`) from the special base
`(0, −1) + (α, 3)` to `(0, 1) + (α, 3)`; `Φ(1) = Φ(0)` on both (`phiP_one`); `ζ̄(z₀ + A(1)) − ζ̄(z₀ + A′(1)) = η̄(perVec e)`
(`zetaB_add`); the exact term `R` has the same endpoints on both paths; and `∫_{[ζ^e]γ} x³dx/y` from
`curveIntegral_cycleE`. The point `z₀` over the base comes from surjectivity (`SurjFacts`).
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

open LSG.JacAnV Beta

variable {A : A1Facts} {B₁' B₂' : LocalBranch f₅ 2} {p' : ℂ × ℂ} {hp' : p' ∈ dom2 B₁' B₂'} {hx' : p'.1 ≠ p'.2}
  {G : GermRad A hp' hx'} (D : ThetaData G)

/-- **The fibre period formula.** -/
theorem ThetaData.etaB_perVec (SF : SurjFacts A) (e : Fin 4) :
    D.etaB (perVec (e : ℕ)) = 3 / 5 * (zetaN 5 ^ (e : ℕ)) ^ 4 * perB5 := by
  obtain ⟨α, hα, B₁, B₂, -, h1y, h2x, h2y, hp, hx, ⟨G₀⟩⟩ := exists_special_base A
  have hP0 : baseP hp hx ≠ 0 := fun h => by
    have := congrFun h 0; rw [baseP_zero] at this; exact one_ne_zero this
  obtain ⟨z₀, c, hz₀⟩ := ThetaData.surjA SF D (baseP hp hx) hP0 baseP_onQ
  obtain ⟨u, Y, Ap, A4, hA, hA4, hA0, hA40, hu, hu0, hY0, hu1, hY1, hub, hAp1, hA41⟩ :=
    exists_pert_lift24 (e : ℕ)
  obtain ⟨v, Z, Ap', A4', hA', hA4', hA0', hA40', hv, hv0, hZ0, hv1, hZ1, hvb, hAp1', hA41'⟩ :=
    exists_pert_lift24 ((e : ℕ) + 1)
  have hαB : α ∈ ball B₂.x₀ B₂.r := by rw [h2x]; exact mem_ball_self B₂.r_pos
  have hαn : 1 ≤ ‖α‖ := by
    by_contra h
    push Not at h
    have h' : ‖α‖ ^ 5 < 1 := pow_lt_one₀ (norm_nonneg _) h (by norm_num)
    rw [← norm_pow, hα] at h'; norm_num at h'
  have hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u t ≠ α := fun t ht h => by
    have := hub t ht; rw [h] at this; linarith
  have hdiag' : ∀ t ∈ Icc (0 : ℝ) 1, v t ≠ α := fun t ht h => by
    have := hvb t ht; rw [h] at this; linarith
  have hstart : mumfordPts (u 0) (Y 0) α 3 = mumford B₁ B₂ ((0 : ℂ), α) := by
    rw [mumford_eq_mumfordPts, hu0, hY0]; simp only; rw [h1y, h2y]
  have hstart' : mumfordPts (v 0) (Z 0) α 3 = mumford B₁ B₂ ((0 : ℂ), α) := by
    rw [mumford_eq_mumfordPts, hv0, hZ0]; simp only; rw [h1y, h2y]
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn hu)
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA'.continuousOn hv)
  obtain ⟨k₁, hk₁⟩ := exists_k_real C₁ G₀.ε G₀.pos
  obtain ⟨k₂, hk₂⟩ := exists_k_real C₂ G₀.ε G₀.pos
  have hU : ∀ t ∈ Icc (0 : ℝ) 1, Ap t ∈ ball (0 : Fin 2 → ℂ) (2 ^ (k₁ + k₂) * G₀.ε) := fun t ht => by
    rw [mem_ball_zero_iff]; exact (hC₁ t ht).trans_lt (hk₁ _ (by omega))
  have hU' : ∀ t ∈ Icc (0 : ℝ) 1, Ap' t ∈ ball (0 : Fin 2 → ℂ) (2 ^ (k₁ + k₂) * G₀.ε) := fun t ht => by
    rw [mem_ball_zero_iff]; exact (hC₂ t ht).trans_lt (hk₂ _ (by omega))
  have hy₀sq : (3 : ℂ) ^ 2 = 4 * α ^ 5 + 1 := by rw [hα]; norm_num
  have Φ1 := D.phiP_one G₀ hz₀ (k₁ + k₂) hαB h2y hy₀sq hA hA0 hA4 hu hdiag hstart hU
  have Φ1' := D.phiP_one G₀ hz₀ (k₁ + k₂) hαB h2y hy₀sq hA' hA0' hA4' hv hdiag' hstart' hU'
  unfold ThetaData.phiP at Φ1 Φ1'
  rw [hA0, hA40, hu0, hY0, hu1, hY1] at Φ1
  rw [hA0', hA40', hv0, hZ0, hv1, hZ1] at Φ1'
  -- the period and the endpoint
  have hper : perVec (e : ℕ) = Ap 1 - Ap' 1 := funext fun j => by
    rw [Pi.sub_apply]; exact period_eq_abelAlong (e : ℕ) j hAp1 hAp1'
  have hlatt : perVec (e : ℕ) ∈ latt := AddSubgroup.subset_closure ⟨e, rfl⟩
  have hθ : D.thetaN (z₀ + Ap' 1) 0 ≠ 0 :=
    D.thetaN_zero_ne_path G₀ hz₀ (k₁ + k₂) hαB h2y hA' hA0' hv hdiag' hstart' hU' ⟨zero_le_one, le_rfl⟩
  have hz := D.zetaB_add hlatt hθ
  rw [show z₀ + Ap' 1 + perVec (e : ℕ) = z₀ + Ap 1 by rw [hper]; abel] at hz
  -- the `x³ dx/y` period
  have h3 := period3_eq_abelAlong (e : ℕ) hA41 hA41'
  rw [curveIntegral_cycleE] at h3
  have hB := betaG_eq 3
  have h45 : (((3 : ℕ) : ℂ) + 1) / 5 = 4 / 5 := by norm_num
  simp only [h45] at hB h3
  rw [perB5, hB]
  have e4 : zetaN 5 ^ ((e : ℕ) + 1) = zetaN 5 ^ (e : ℕ) * zetaN 5 := pow_succ _ _
  rw [e4] at h3
  simp only [add_zero] at Φ1 Φ1'
  linear_combination -hz + Φ1 - Φ1' + 3 * h3

end LSG.JacAn
