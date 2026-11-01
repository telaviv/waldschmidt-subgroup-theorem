/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn4.Closed
import LSG.JacAn4.CurveConn
import LSG.JacAn4.SurjFacts

/-!
# A4.1b (S-b): every generic divisor is a point of `E(ℂ²)`

For a base `G` (generic pair `p`, branches `B₁, B₂`):
* **`exists_follow`**: for every generic target `D = (x₁,y₁) + (x₂,y₂)` there are `k`, `c` and a local exponential
  `Ψ` at `D` with `Par (T(c + w)) (Ψ w)` near `0` (`T = transP k`): a path in `GenPairs` (`isPathConnected_genPairs`),
  `exists_abelAlong`, and `follow_par` at `t = 1`.
* cone calculus: `cone_smul`, `expLift_mem_cone`, `law0_mem_cone`, `par_mem_cone`, `transP_mem_cone`,
  `frequently_transP_ne` (identity theorem);
* **`generic_mem`**: if `P₀ ∈` cone, every generic Grant point is in the cone (closedness);
* **`anchor_mem`**: at the special base, `P₀ ∈` cone, from `SurjFacts.anchor` (`law0(2D₀, −P₀) = λ P₀`) and the inversion
  `inv_trans`.
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}

lemma mem_genPairs_of {x₁ y₁ x₂ y₂ : ℂ} (h1 : y₁ ^ 2 = fc x₁) (h2 : y₂ ^ 2 = fc x₂) (hx12 : x₁ ≠ x₂)
    (hy1 : y₁ ≠ 0) (hy2 : y₂ ≠ 0) : ((x₁, y₁), (x₂, y₂)) ∈ GenPairs := by
  refine ⟨⟨h1, fun h => hy1 ?_⟩, ⟨h2, fun h => hy2 ?_⟩, hx12⟩
  · have : y₁ ^ 2 = 0 := by rw [h1]; exact h
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  · have : y₂ ^ 2 = 0 := by rw [h2]; exact h
    exact pow_eq_zero_iff (by norm_num) |>.mp this

/-- **Following a generic path to a generic target.** -/
theorem exists_follow (G : GermRad A hp hx) {x₁ y₁ x₂ y₂ : ℂ} (h1 : y₁ ^ 2 = fc x₁) (h2 : y₂ ^ 2 = fc x₂)
    (hx12 : x₁ ≠ x₂) (hy1 : y₁ ≠ 0) (hy2 : y₂ ≠ 0) :
    ∃ k : ℕ, ∃ c ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε), ∃ Ψ : (Fin 2 → ℂ) → P9, ContinuousAt Ψ 0 ∧
      Ψ 0 = grantJ (mumfordPts x₁ y₁ x₂ y₂) ∧ (∀ w, Ψ w 0 = 1) ∧
      ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), Par (transP (A := A) (hp := hp) (hx := hx) k (c + w)) (Ψ w) := by
  have hp1 := hp.1
  have hp2 := hp.2
  have hb1 : B₁.Y p.1 ^ 2 = fc p.1 := by rw [fc_eq]; exact B₁.Y_sq _ hp1
  have hb2 : B₂.Y p.2 ^ 2 = fc p.2 := by rw [fc_eq]; exact B₂.Y_sq _ hp2
  have hq₀ := mem_genPairs_of hb1 hb2 hx (B₁.Y_ne _ hp1) (B₂.Y_ne _ hp2)
  have hq₁ := mem_genPairs_of h1 h2 hx12 hy1 hy2
  have hJ := isPathConnected_genPairs.joinedIn _ hq₀ _ hq₁
  set γ := hJ.somePath
  have hγ : ∀ t, γ t ∈ GenPairs := hJ.somePath_mem
  set F : ℝ → (ℂ × ℂ) × (ℂ × ℂ) := fun t => γ.extend t
  have hFc : Continuous F := γ.extend.continuous
  have hFI : ∀ t ∈ Icc (0 : ℝ) 1, F t ∈ GenPairs := fun t ht => by
    rw [show F t = γ ⟨t, ht⟩ from γ.extend_apply ht]; exact hγ _
  have hF0 : F 0 = ((p.1, B₁.Y p.1), (p.2, B₂.Y p.2)) := γ.extend_zero
  have hF1 : F 1 = ((x₁, y₁), (x₂, y₂)) := γ.extend_one
  set u₁ : ℝ → ℂ := fun t => (F t).1.1
  set Y₁ : ℝ → ℂ := fun t => (F t).1.2
  set u₂ : ℝ → ℂ := fun t => (F t).2.1
  set Y₂ : ℝ → ℂ := fun t => (F t).2.2
  have hu₁ : ContinuousOn u₁ (Icc 0 1) := (continuous_fst.comp (continuous_fst.comp hFc)).continuousOn
  have hY₁ : ContinuousOn Y₁ (Icc 0 1) := (continuous_snd.comp (continuous_fst.comp hFc)).continuousOn
  have hu₂ : ContinuousOn u₂ (Icc 0 1) := (continuous_fst.comp (continuous_snd.comp hFc)).continuousOn
  have hY₂ : ContinuousOn Y₂ (Icc 0 1) := (continuous_snd.comp (continuous_snd.comp hFc)).continuousOn
  have hsq₁ : ∀ t ∈ Icc (0 : ℝ) 1, Y₁ t ^ 2 = f₅.eval (u₁ t) := fun t ht => by
    rw [← fc_eq]; exact (hFI t ht).1.1
  have hsq₂ : ∀ t ∈ Icc (0 : ℝ) 1, Y₂ t ^ 2 = f₅.eval (u₂ t) := fun t ht => by
    rw [← fc_eq]; exact (hFI t ht).2.1.1
  have hne₁ : ∀ t ∈ Icc (0 : ℝ) 1, Y₁ t ≠ 0 := fun t ht =>
    ne_zero_of_mem_covB (hFI t ht).1 subset_rfl
  have hne₂ : ∀ t ∈ Icc (0 : ℝ) 1, Y₂ t ≠ 0 := fun t ht =>
    ne_zero_of_mem_covB (hFI t ht).2.1 subset_rfl
  have hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u₁ t ≠ u₂ t := fun t ht => (hFI t ht).2.2
  obtain ⟨A₁, hA₁0, hA₁⟩ := exists_abelAlong (g := 2) hu₁ hY₁ hsq₁ hne₁
  obtain ⟨A₂, hA₂0, hA₂⟩ := exists_abelAlong (g := 2) hu₂ hY₂ hsq₂ hne₂
  have hA₁' : IsAbelAlong f₅ 2 u₁ Y₁ A₁ := hA₁
  have hA₂' : IsAbelAlong f₅ 2 u₂ Y₂ A₂ := hA₂
  have hstart : mumfordPts (u₁ 0) (Y₁ 0) (u₂ 0) (Y₂ 0) = mumford B₁ B₂ p := by
    rw [mumford_eq_mumfordPts]; simp only [u₁, Y₁, u₂, Y₂, hF0]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hA₁'.continuousOn hu₁).add (hA₂'.continuousOn hu₂))
  obtain ⟨k, hk⟩ := exists_k_real C G.ε G.pos
  have hU : ∀ t ∈ Icc (0 : ℝ) 1, A₁ t + A₂ t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := fun t ht => by
    rw [mem_ball_zero_iff]; exact (hC t ht).trans_lt (hk k le_rfl)
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hfol := follow_par G k hA₁' hA₂' hA₁0 hA₂0 hu₁ hu₂ hdiag hstart hU 1 h1I
  obtain ⟨B₁'', B₂'', hp'', hYe1, hYe2, -⟩ := localExp_follow hA₁' hA₂' hu₁ hu₂ hdiag h1I
  have hx'' : (u₁ 1, u₂ 1).1 ≠ (u₁ 1, u₂ 1).2 := hdiag 1 h1I
  set Ψ : (Fin 2 → ℂ) → P9 := fun w => psiJ hp'' hx'' (abel2 B₁'' B₂'' (u₁ 1, u₂ 1) + w)
  have hΨf : FlowNear Ψ := by filter_upwards [psi_flowNear hp'' hx''] with w hw using hw.1
  have hΨ0 : Ψ 0 = grantJ (mumfordPts (u₁ 1) (Y₁ 1) (u₂ 1) (Y₂ 1)) := by
    simp only [Ψ, add_zero, psiJ, localExp_abel2_self, mumford_eq_mumfordPts]
    change grantJ (mumfordPts (u₁ 1) (B₁''.Y (u₁ 1)) (u₂ 1) (B₂''.Y (u₂ 1))) =
      grantJ (mumfordPts (u₁ 1) (Y₁ 1) (u₂ 1) (Y₂ 1))
    rw [hYe1, hYe2]
  refine ⟨k, A₁ 1 + A₂ 1, hU 1 h1I, Ψ, (psi_flowNear hp'' hx'').self_of_nhds.1.continuousAt, ?_,
    fun w => psiJ_zero _, hfol Ψ hΨf hΨ0⟩
  rw [hΨ0]; simp only [u₁, Y₁, u₂, Y₂, hF1]

variable {G : GermRad A hp hx} (D : ThetaData G)

lemma ThetaData.cone_smul {X : P9} (hX : X ∈ D.imgCone) (a : ℂ) : a • X ∈ D.imgCone := by
  rcases hX with h | ⟨z, c, rfl⟩
  · left; rw [h, smul_zero]
  · right; exact ⟨z, a * c, by rw [smul_smul]⟩

lemma ThetaData.expLift_eq_smul (k : ℕ) {z : Fin 2 → ℂ} (hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    ∃ s : ℂ, expLift A hp hx k z = s • D.thetaN z := by
  have h := (expP_eq G (G.mem_small hz)).symm.trans (D.expP_eq_thetaN z)
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.symm⟩

lemma ThetaData.law0_mem_cone (u v : Fin 2 → ℂ) (s t : ℂ) :
    A.law0 (s • D.thetaN u) (t • D.thetaN v) ∈ D.imgCone := by
  obtain ⟨a, ha⟩ := D.law_correct u v 0
  have h : A.law0 (D.thetaN u) (D.thetaN v) = a • D.thetaN (u + v) := by
    rw [← ha]; funext k; exact A.law0_lawK _ _ k
  rw [A.law0_smul_left, A.law0_smul_right, h, smul_smul, smul_smul]
  right; exact ⟨u + v, _, rfl⟩

lemma ThetaData.par_mem_cone {X Y : P9} (h : Par X Y) (hY : Y ≠ 0) (hYc : Y ∈ D.imgCone) : X ∈ D.imgCone := by
  obtain ⟨a, rfl⟩ := par_exists_smul h hY
  exact D.cone_smul hYc a

lemma ThetaData.baseP_eq_smul (hP₀ : baseP hp hx ∈ D.imgCone) :
    ∃ z₀ : Fin 2 → ℂ, ∃ b : ℂ, baseP hp hx = b • D.thetaN z₀ := by
  rcases hP₀ with h | h
  · exfalso; have := congrFun h 0; rw [baseP_zero] at this; exact one_ne_zero this
  · exact h

lemma ThetaData.transP_mem_cone (hP₀ : baseP hp hx ∈ D.imgCone) (k : ℕ) {z : Fin 2 → ℂ}
    (hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) : transP (A := A) (hp := hp) (hx := hx) k z ∈ D.imgCone := by
  obtain ⟨s, hs⟩ := D.expLift_eq_smul k hz
  obtain ⟨z₀, b, hb⟩ := D.baseP_eq_smul hP₀
  rw [transP, hs, hb]
  exact D.law0_mem_cone z z₀ s b

include G in
lemma frequently_transP_ne (k : ℕ) {c : Fin 2 → ℂ} (hc : c ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    ∃ᶠ w in 𝓝 (0 : Fin 2 → ℂ), transP (A := A) (hp := hp) (hx := hx) k (c + w) ≠ 0 := by
  rw [Filter.Frequently]
  intro hcon
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  have hev : transP (A := A) (hp := hp) (hx := hx) k =ᶠ[𝓝 c] 0 := by
    have ht : Tendsto (fun u : Fin 2 → ℂ => u - c) (𝓝 c) (𝓝 0) := by
      have h := (tendsto_id (x := 𝓝 c)).sub (tendsto_const_nhds (x := c))
      rwa [sub_self] at h
    filter_upwards [ht.eventually hcon] with u hu
    push Not at hu
    simpa using hu
  have h0 := (analyticOn_transP G k).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hc hev (mem_ball_self hpos)
  obtain ⟨a, ha, hT0⟩ := transP_zero G k
  rw [hT0] at h0
  have := congrFun h0 0
  simp [baseP_zero, ha] at this

/-- **Generic divisors are points of `E(ℂ²)`** (given the anchor `P₀ ∈` cone). -/
theorem ThetaData.generic_mem (hP₀ : baseP hp hx ∈ D.imgCone) {x₁ y₁ x₂ y₂ : ℂ} (h1 : y₁ ^ 2 = fc x₁)
    (h2 : y₂ ^ 2 = fc x₂) (hx12 : x₁ ≠ x₂) (hy1 : y₁ ≠ 0) (hy2 : y₂ ≠ 0) :
    grantJ (mumfordPts x₁ y₁ x₂ y₂) ∈ D.imgCone := by
  obtain ⟨k, c, hc, Ψ, hΨc, hΨ0, hΨ1, hev⟩ := exists_follow G h1 h2 hx12 hy1 hy2
  have hball : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), c + w ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := by
    have hcont : ContinuousAt (fun w : Fin 2 → ℂ => c + w) 0 := (continuous_const.add continuous_id).continuousAt
    exact hcont.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hc)
  have hfreq : ∃ᶠ w in 𝓝 (0 : Fin 2 → ℂ), Ψ w ∈ D.imgCone := by
    refine (frequently_transP_ne (G := G) k hc).mp ?_
    filter_upwards [hev, hball] with w hw hwb hT
    exact D.par_mem_cone hw.symm hT (D.transP_mem_cone hP₀ k hwb)
  have hcl := mem_closure_iff_frequently.mpr (hΨc.tendsto.frequently hfreq)
  rw [D.isClosed_imgCone.closure_eq, hΨ0] at hcl
  exact hcl

/-- **The anchor**: at the special base, `P₀ ∈` cone. -/
theorem ThetaData.anchor_mem {x₁ y₁ x₂ y₂ lam : ℂ} (h1 : y₁ ^ 2 = fc x₁) (h2 : y₂ ^ 2 = fc x₂)
    (hx12 : x₁ ≠ x₂) (hy1 : y₁ ≠ 0) (hy2 : y₂ ≠ 0) (hlam : lam ≠ 0)
    (hD₂ : A.law0 (grantJ (mumfordPts x₁ y₁ x₂ y₂)) (A.negP (baseP hp hx)) = lam • baseP hp hx) :
    baseP hp hx ∈ D.imgCone := by
  obtain ⟨k, c, hc, Ψ, hΨc, hΨ0, hΨ1, hev⟩ := exists_follow G h1 h2 hx12 hy1 hy2
  set P₀ := baseP hp hx
  have hball : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), c + w ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := by
    have hcont : ContinuousAt (fun w : Fin 2 → ℂ => c + w) 0 := (continuous_const.add continuous_id).continuousAt
    exact hcont.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hc)
  -- `law0 (Ψ w) (−P₀)` is frequently in the cone
  have hfreq : ∃ᶠ w in 𝓝 (0 : Fin 2 → ℂ), A.law0 (Ψ w) (A.negP P₀) ∈ D.imgCone := by
    refine (frequently_transP_ne (G := G) k hc).mp ?_
    filter_upwards [hev, hball] with w hw hwb hT
    -- `T = μ • Ψ w`, `μ ≠ 0`
    have hTe := hw.symm.eq_smul (m := 0) (by rw [hΨ1]; exact one_ne_zero)
    rw [hΨ1, div_one] at hTe
    set μ := transP (A := A) (hp := hp) (hx := hx) k (c + w) 0
    have hμ : μ ≠ 0 := by intro h0; apply hT; rw [hTe, h0, zero_smul]
    have hinv := inv_trans G k hwb
    rw [hTe, A.law0_smul_left] at hinv
    obtain ⟨s, hs⟩ := D.expLift_eq_smul k hwb
    have hne : expLift A hp hx k (c + w) ≠ 0 := expLift_ne_zero G (G.mem_small hwb)
    have hEc : expLift A hp hx k (c + w) ∈ D.imgCone := by rw [hs]; right; exact ⟨_, s, rfl⟩
    have hmem := D.par_mem_cone hinv.symm hne hEc
    have := D.cone_smul hmem (μ ^ 2)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hμ), one_smul] at this
  -- the limit `law0 (D₂) (−P₀) = λ P₀`
  have hL : ContinuousAt (fun w => A.law0 (Ψ w) (A.negP P₀)) 0 := by
    have hlaw : ContinuousAt (fun X => A.law0 X (A.negP P₀)) (Ψ 0) :=
      ((A.hasFDerivAt_law0 _ _).continuousAt)
    exact hlaw.comp hΨc
  have hcl := mem_closure_iff_frequently.mpr (hL.tendsto.frequently hfreq)
  rw [D.isClosed_imgCone.closure_eq] at hcl
  simp only [hΨ0, hD₂] at hcl
  have := D.cone_smul hcl lam⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hlam, one_smul] at this

end LSG.JacAn
