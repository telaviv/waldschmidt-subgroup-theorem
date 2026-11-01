/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn4.Generic
import LSG.JacAn4.ExitTaylor
import LSG.JacAn3.TaylorFields

/-!
# A4.1b (S-c): boundary points by flow exit

For a quadratic chart field `W` (smooth), generators `gens` of the model tangent to `W` in ideal form, a closed set `S`
containing every affine model point, and a model point `X` with `X₀ = 0` and an exit word `D_v^k X₀ (X) ≠ 0`:
* the real-time integral curve `α` of `F = v₀ W₀ + v₁ W₁` from `X` (`ContDiffAt.exists_…_hasDerivAt₀`);
* stays on the model for `t ≥ 0` (`gens ∘ α` solves a linear ODE with zero initial value, `ODE_solution_unique…`);
* leaves `X₀ = 0` for small `t ≠ 0` (`taylor_exit` applied to `D_v^j X₀ ∘ α`);
* so `X = lim_{t→0⁺} α(t) ∈ S` (**`flow_exit_mem`**).

**`ThetaData.boundary_mem`**: with `SurjFacts` (charts 4 and 8, `quadA_cover`), every boundary model point is in the
cone, provided every affine model point is.
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

lemma contDiff_exitWord {W : Fin 2 → P9 → P9} (hW : ∀ j, ContDiff ℂ ⊤ (W j)) (v : Fin 2 → ℂ) (k : ℕ) :
    ContDiff ℂ ⊤ (exitWord W v k) := by
  have hF : ContDiff ℂ ⊤ (fun X => v 0 • W 0 X + v 1 • W 1 X) :=
    ((hW 0).const_smul (v 0)).add ((hW 1).const_smul (v 1))
  induction k with
  | zero =>
    change ContDiff ℂ ⊤ (fun X : P9 => X 0)
    exact (prj 0).contDiff
  | succ k ih =>
    rw [exitWord, Function.iterate_succ_apply']
    change ContDiff ℂ ⊤ (fun X => fderiv ℂ (exitWord W v k) X (v 0 • W 0 X + v 1 • W 1 X))
    exact (ih.fderiv_right (m := ⊤) (by simp)).clm_apply hF

/-- **Flow exit.** -/
theorem flow_exit_mem {W : Fin 2 → P9 → P9} (hW : ∀ j, ContDiff ℂ ⊤ (W j)) {gens : Fin 12 → P9 → ℂ}
    (hgd : ∀ i, Differentiable ℂ (gens i)) {tan : Fin 2 → Fin 12 → Fin 12 → P9 → ℂ}
    (htc : ∀ j i k, Continuous (tan j i k))
    (htan : ∀ j i X, fderiv ℂ (gens i) X (W j X) = ∑ k, tan j i k X * gens k X)
    {S : Set P9} (hS : IsClosed S) (haff : ∀ Y, (∀ i, gens i Y = 0) → Y 0 ≠ 0 → Y ∈ S)
    {X : P9} (hX : ∀ i, gens i X = 0) (hX0 : X 0 = 0) {v : Fin 2 → ℂ} {k : ℕ}
    (hword : exitWord W v k X ≠ 0) : X ∈ S := by
  set F : P9 → P9 := fun Y => v 0 • W 0 Y + v 1 • W 1 Y
  have hFc : ContDiff ℂ ⊤ F := ((hW 0).const_smul (v 0)).add ((hW 1).const_smul (v 1))
  have hF1 : ContDiffAt ℝ 1 F X := ((hFc.restrict_scalars ℝ).of_le le_top).contDiffAt
  obtain ⟨α, hα0, ε, hε, hαd⟩ := hF1.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  simp only [zero_sub, zero_add] at hαd
  have hαc : ContinuousOn α (Icc 0 (ε / 2)) := fun t ht =>
    (hαd t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  -- (1) invariance for `t ∈ [0, ε/2]`
  set M : ℝ → Fin 12 → Fin 12 → ℂ := fun t i k => v 0 * tan 0 i k (α t) + v 1 * tan 1 i k (α t)
  have hMc : ∀ i k, ContinuousOn (fun t => M t i k) (Icc 0 (ε / 2)) := fun i k =>
    (continuousOn_const.mul ((htc 0 i k).comp_continuousOn hαc)).add
      (continuousOn_const.mul ((htc 1 i k).comp_continuousOn hαc))
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ t ∈ Icc 0 (ε / 2), ∀ i k, ‖M t i k‖ ≤ C := by
    have : ∀ i k, ∃ C, ∀ t ∈ Icc 0 (ε / 2), ‖M t i k‖ ≤ C := fun i k =>
      isCompact_Icc.exists_bound_of_continuousOn (hMc i k)
    choose Cik hCik using this
    exact ⟨∑ i, ∑ k, |Cik i k|, fun t ht i k => (hCik i k t ht).trans ((le_abs_self _).trans
      (le_trans (Finset.single_le_sum (f := fun k => |Cik i k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k))
        (Finset.single_le_sum (f := fun i => ∑ k, |Cik i k|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))))⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, by linarith⟩ 0 0)
  set Vf : ℝ → (Fin 12 → ℂ) → (Fin 12 → ℂ) := fun t y i => ∑ k, M t i k * y k
  have hLip : ∀ t ∈ Ico 0 (ε / 2), LipschitzOnWith ⟨12 * C, mul_nonneg (by norm_num) hC0⟩ (Vf t) univ := by
    intro t ht
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun y z => ?_)
    rw [dist_eq_norm, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) (norm_nonneg _))).mpr
      fun i => ?_
    simp only [Vf, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ k, (M t i k * y k - M t i k * z k)‖ ≤ ∑ k, ‖M t i k * y k - M t i k * z k‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin 12, C * ‖y - z‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [← mul_sub, norm_mul]
          exact mul_le_mul (hC t (Ico_subset_Icc_self ht) i k) (norm_le_pi_norm (y - z) k)
            (norm_nonneg _) hC0
      _ = 12 * C * ‖y - z‖ := by simp; ring
  set Gv : ℝ → Fin 12 → ℂ := fun t i => gens i (α t)
  have hGd : ∀ t ∈ Ioo (-ε) ε, HasDerivAt Gv (Vf t (Gv t)) t := by
    intro t ht
    refine hasDerivAt_pi.mpr fun i => ?_
    have h1 : HasDerivAt (fun s => gens i (α s)) _ t :=
      ((hgd i (α t)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hαd t ht)
    convert h1 using 1
    simp only [Vf, M, ContinuousLinearMap.coe_restrictScalars', F, map_add, map_smul, htan, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib, Gv]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hGc : ContinuousOn Gv (Icc 0 (ε / 2)) := continuousOn_pi.mpr fun i =>
    ((hgd i).continuous.comp_continuousOn hαc)
  have hinv := ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ) hLip hGc
    (fun t ht => (hGd t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivWithinAt)
    (fun _ _ => mem_univ _) (continuousOn_const (c := (0 : Fin 12 → ℂ)))
    (fun t _ => by
      have := hasDerivWithinAt_const t (Ici t) (0 : Fin 12 → ℂ)
      convert this using 1
      funext i; simp [Vf])
    (fun _ _ => mem_univ _) (by funext i; simp [Gv, hα0, hX])
  have honQ : ∀ t ∈ Icc 0 (ε / 2), ∀ i, gens i (α t) = 0 := fun t ht i => congrFun (hinv ht) i
  -- (2) exit
  classical
  have hex : ∃ j, exitWord W v j X ≠ 0 := ⟨k, hword⟩
  set K := Nat.find hex
  have hKne : exitWord W v K X ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j < K, exitWord W v j X = 0 := fun j hj => by
    have := Nat.find_min hex hj; push Not at this; exact this
  have hcd := contDiff_exitWord hW v
  set h : ℕ → ℝ → ℂ := fun j t => exitWord W v j (α t)
  have hhd : ∀ j < K, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (h j) (h (j + 1) t) t := by
    intro j _ t ht
    have h1 : HasDerivAt (fun s => exitWord W v j (α s)) _ t :=
      (((hcd j).differentiable (by simp) (α t)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hαd t ht)
    convert h1 using 1
    simp only [h, exitWord, Function.iterate_succ_apply', ContinuousLinearMap.coe_restrictScalars']
    rfl
  have hhc : ContinuousAt (h K) 0 :=
    (hcd K).continuous.continuousAt.comp (hαd 0 ⟨by linarith, hε⟩).continuousAt
  obtain ⟨δ, hδ, hexit⟩ := taylor_exit hε hhd hhc (fun j hj => by simp [h, hα0, hlt j hj])
    (by simpa [h, hα0] using hKne)
  -- (3) the limit
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), α t ∈ S := by
    have hmem : Ioo 0 (min δ (ε / 2)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (lt_min hδ (by linarith))
    filter_upwards [hmem] with t ht
    have ht1 : t ∈ Icc 0 (ε / 2) := ⟨ht.1.le, (ht.2.trans_le (min_le_right _ _)).le⟩
    refine haff _ (honQ t ht1) ?_
    have := hexit t ht.1.ne' (by rw [abs_of_pos ht.1]; exact ht.2.trans_le (min_le_left _ _))
    simpa [h, exitWord] using this
  have htend : Tendsto α (𝓝[>] (0 : ℝ)) (𝓝 X) := by
    have := (hαd 0 ⟨by linarith, hε⟩).continuousAt.tendsto
    rw [hα0] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact hS.mem_of_tendsto htend hev

variable {A : A1Facts}

lemma A1Facts.contDiff_W4 (A : A1Facts) (j : Fin 2) : ContDiff ℂ ⊤ (A.W4 j) := (A.W4_analytic j).contDiff

lemma A1Facts.contDiff_W8 (A : A1Facts) (j : Fin 2) : ContDiff ℂ ⊤ (A.W8 j) := by
  rw [contDiff_pi]
  intro l
  have : (fun X => A.W8 j X l) = fun X => ∑ a, ∑ b, ((A.W8num j l a b : ℂ) / A.W8den) * (X a * X b) :=
    funext fun X => A.W8_table j X l
  rw [this]
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    contDiff_const.mul ((prj a).contDiff.mul (prj b).contDiff)

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- **Boundary model points are in the cone**, provided every affine model point is. -/
theorem ThetaData.boundary_mem (SF : SurjFacts A) (haff : ∀ Y, A.OnQ Y → Y 0 ≠ 0 → Y ∈ D.imgCone)
    {X : P9} (hX : A.OnQ X) (hX0 : X 0 = 0) : X ∈ D.imgCone := by
  by_cases hXz : X = 0
  · left; exact hXz
  have hgX : ∀ i, SF.gensI i X = 0 := (SF.gensI_iff X).mp hX
  have haff' : ∀ Y, (∀ i, SF.gensI i Y = 0) → Y 0 ≠ 0 → Y ∈ D.imgCone := fun Y hY hY0 =>
    haff Y ((SF.gensI_iff Y).mpr hY) hY0
  rcases quadA_cover (A.onQ_quad X hX) hXz with h0 | h4 | h8
  · exact absurd hX0 h0
  · obtain ⟨v, k, -, -, hw⟩ := SF.exit4 X hX hX0 h4
    exact flow_exit_mem A.contDiff_W4 SF.gensI_diff SF.tanC4_cont SF.gensI_tan4 D.isClosed_imgCone haff'
      hgX hX0 hw
  · obtain ⟨v, k, -, -, hw⟩ := SF.exit8 X hX hX0 h8
    exact flow_exit_mem A.contDiff_W8 SF.gensI_diff SF.tanC8_cont SF.gensI_tan8 D.isClosed_imgCone haff'
      hgX hX0 hw

end LSG.JacAn
