/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.AuxQP

/-!
# A3.6 (part 1): preparations for ψ-Liouville (STAGE_A3 §2.1, §6.1)

* `exists_theta0_ne`: `θ₀ ≢ 0` (else `flowW` forces `germ₁ ≡ 0`, contradicting `W4_origin_indep`);
* `theta_zero`: `θ 0 = a • e₄`;
* `germ_neg`, **`theta_neg_par`**: `[−1]` compatibility `negP (θ v) ∥ θ (−v)` (`W4_negP`);
* `theta_PF0`: `θ` satisfies the chart-0 projective flow equation everywhere;
* **`hom_untrans`**: the untranslated homomorphism `law0 (θ u) (θ v) ∥ θ (u + v)` for all `u, v`.
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

/-- A locally vanishing component has vanishing derivative. -/
lemma comp_deriv_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : E → P9}
    {F' : E →L[ℂ] P9} {x : E} (hF : HasFDerivAt F F' x) {m : Fin 9} (h0 : ∀ᶠ y in 𝓝 x, F y m = 0)
    (w : E) : F' w m = 0 := by
  have h1 : HasFDerivAt (fun y => F y m) ((prj m).comp F') x := (prj m).hasFDerivAt.comp x hF
  have h2 : HasFDerivAt (fun y => F y m) (0 : E →L[ℂ] ℂ) x :=
    (hasFDerivAt_const (0 : ℂ) x).congr_of_eventuallyEq h0
  have := congrArg (fun L : E →L[ℂ] ℂ => L w) (h1.unique h2)
  simpa using this

lemma normalize_smul_one {Y : P9} (hY : Y 0 = 1) {a : ℂ} (ha : a ≠ 0) : normalize 0 (a • Y) = Y := by
  simp only [normalize, Pi.smul_apply, smul_eq_mul, hY, mul_one, smul_smul, inv_mul_cancel₀ ha, one_smul]

lemma eq_smul_normalize {X : P9} (hX : X 0 ≠ 0) : X = X 0 • normalize 0 X := by
  rw [normalize, smul_smul, mul_inv_cancel₀ hX, one_smul]

lemma par_smul_smul (a b : ℂ) (X : P9) : Par (a • X) (b • X) := ((par_self X).smul_left a).smul_right b

/-- `[−1]` as a continuous linear map. -/
def negL : P9 →L[ℂ] P9 := LinearMap.toContinuousLinearMap
  { toFun := fun X => ![X 0, X 1, X 2, X 3, -X 4, -X 5, -X 6, -X 7, X 8]
    map_add' := fun X Y => by ext i; fin_cases i <;> simp <;> ring
    map_smul' := fun a X => by ext i; fin_cases i <;> simp }

lemma negL_apply (A : A1Facts) (X : P9) : negL X = A.negP X := by rw [A.negP_eq]; rfl

lemma negL_origin : -negL origin9 = origin9 := by
  ext i; fin_cases i <;> simp [negL, origin9]

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

lemma ThetaData.adm_zero {v : Fin 2 → ℂ} (hv : v ∈ ball (0 : Fin 2 → ℂ) D.ρ) : D.Adm 0 v := by
  unfold ThetaData.Adm; simpa using hv

lemma ThetaData.theta_eq_germ {v : Fin 2 → ℂ} (hv : v ∈ ball (0 : Fin 2 → ℂ) D.ρ) :
    D.theta v = Complex.exp (-D.Phi 0 v) • germ A hp hx v := by
  rw [D.theta_eq (D.adm_zero hv), ThetaData.thetaK]; simp [expLift]

lemma ThetaData.theta_zero : ∃ a : ℂ, a ≠ 0 ∧ D.theta 0 = a • origin9 :=
  ⟨_, Complex.exp_ne_zero _, by rw [D.theta_eq_germ (mem_ball_self D.pos), G.germ_zero]⟩

/-- **`θ₀ ≢ 0`.** -/
theorem ThetaData.exists_theta0_ne : ∃ w, D.theta w 0 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hρ := D.pos
  have hg0 : ∀ v ∈ ball (0 : Fin 2 → ℂ) D.ρ, germ A hp hx v 0 = 0 := fun v hv => by
    have := hcon v
    rw [D.theta_eq_germ hv, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left (Complex.exp_ne_zero _)
  have hEeq : expLift A hp hx 0 = germ A hp hx := funext fun z => by simp [expLift]
  have hg1 : ∀ v ∈ ball (0 : Fin 2 → ℂ) D.ρ, germ A hp hx v 1 = 0 := by
    intro v hv
    have hvε : v ∈ ball (0 : Fin 2 → ℂ) G.ε := ball_subset_ball D.le_ε hv
    have hPF := PF0_expLift G 0 v (by simpa using hvε)
    rw [hEeq] at hPF
    have hd : HasFDerivAt (germ A hp hx) (fderiv ℂ (germ A hp hx) v) v :=
      (G.good v hvε).2.2.1.differentiableAt.hasFDerivAt
    have hev : ∀ᶠ y in 𝓝 v, germ A hp hx y 0 = 0 := by
      filter_upwards [isOpen_ball.mem_nhds hv] with y hy using hg0 y hy
    have hz := comp_deriv_zero hd hev (Pi.single 0 1)
    have h := hPF (Pi.single 0 1) 4
    rw [hg0 v hv, hz] at h
    have hf : flowW 0 (germ A hp hx v) 4 = -3 * germ A hp hx v 0 * germ A hp hx v 3 +
        6 * germ A hp hx v 1 ^ 2 := by simp [flowW]
    simp only [zero_mul, mul_zero, sub_zero, one_mul, Pi.single_eq_same] at h
    rw [Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_mul, add_zero, hf, hg0 v hv] at h
    have : germ A hp hx v 1 ^ 2 = 0 := by linear_combination -h / 6
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hflow := (G.good 0 (mem_ball_self G.pos)).1.2
  have hev1 : ∀ᶠ y in 𝓝 (0 : Fin 2 → ℂ), germ A hp hx y 1 = 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with y hy using hg1 y hy
  have h0 := comp_deriv_zero hflow hev1 (Pi.single 0 1)
  have h1 := comp_deriv_zero hflow hev1 (Pi.single 1 1)
  rw [G.germ_zero, flowCLM_apply] at h0 h1
  simp at h0 h1
  have := A.W4_origin_indep
  rw [h0, h1] at this
  simp at this

/-- **`[−1]` on the germ**: `germ v = −negP (germ (−v))`. -/
theorem germ_neg (G : GermRad A hp hx) :
    ∀ v ∈ ball (0 : Fin 2 → ℂ) G.ε, germ A hp hx v = -negL (germ A hp hx (-v)) := by
  refine flow_unique A.W4 A.W4_contDiff 1 (V₂ := fun v => -negL (germ A hp hx (-v)))
    (fun v hv => (G.good v hv).1.2) (fun v hv => ?_) ?_
  · have hmv : -v ∈ ball (0 : Fin 2 → ℂ) G.ε := by rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
    obtain ⟨⟨-, hd⟩, hQ, -⟩ := G.good (-v) hmv
    have h := ((-negL).hasFDerivAt).comp v (hd.comp v (-ContinuousLinearMap.id ℂ (Fin 2 → ℂ)).hasFDerivAt)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
    set X := germ A hp hx (-v)
    have hW : ∀ j, A.W4 j (-negL X) = negL (A.W4 j X) := fun j => by
      rw [show -negL X = (-1 : ℂ) • negL X by simp, A.W4_smul, negL_apply A, negL_apply A, A.W4_negP j X hQ]
      simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, flowCLM_apply, hW,
      ContinuousLinearMap.id_apply, Pi.neg_apply, one_smul, map_add, map_smul, neg_smul, smul_neg,
      neg_add_rev, neg_neg]
    simp [ContinuousLinearMap.map_smul, smul_smul]
  · simp [G.germ_zero, negL_origin]

/-- **`[−1]`**: `negP (θ v) ∥ θ (−v)` for all `v`. -/
theorem ThetaData.theta_neg_par (v : Fin 2 → ℂ) : Par (A.negP (D.theta v)) (D.theta (-v)) := by
  have hF₁ : AnalyticOnNhd ℂ (fun v => A.negP (D.theta v)) univ := fun v _ => by
    have := (negL.analyticAt (D.theta v)).comp (D.analyticAt_theta v)
    simpa [Function.comp_def, negL_apply A] using this
  have hF₂ : AnalyticOnNhd ℂ (fun v => D.theta (-v)) univ := fun v _ =>
    AnalyticAt.comp (g := D.theta) (f := fun v => -v) (D.analyticAt_theta (-v)) analyticAt_id.neg
  refine par_of_eventually isPreconnected_univ hF₁ hF₂ (mem_univ 0) ?_ v (mem_univ v)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self D.pos)] with v hv
  have hmv : -v ∈ ball (0 : Fin 2 → ℂ) D.ρ := by rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
  have hvε : v ∈ ball (0 : Fin 2 → ℂ) G.ε := ball_subset_ball D.le_ε hv
  have hg := germ_neg G v hvε
  have hg' : germ A hp hx (-v) = (-1 : ℂ) • negL (germ A hp hx v) := by
    have hmvε : -v ∈ ball (0 : Fin 2 → ℂ) G.ε := ball_subset_ball D.le_ε hmv
    have := germ_neg G (-v) hmvε
    rw [neg_neg] at this; rw [this]; simp
  change Par (A.negP (D.theta v)) (D.theta (-v))
  rw [D.theta_eq_germ hv, D.theta_eq_germ hmv, ← negL_apply A, map_smul, hg', smul_smul]
  exact par_smul_smul _ _ _

/-- `θ` satisfies the chart-0 projective flow equation everywhere. -/
theorem ThetaData.theta_PF0 (w : Fin 2 → ℂ) : PFAt flowW 1 0 D.theta w := by
  obtain ⟨k, hk⟩ := D.exists_adm w
  have hU : w ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := by
    have h := hk.memε
    rw [mem_ball_zero_iff, norm_smul, norm_inv, norm_pow] at h
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, inv_mul_lt_iff₀ (by positivity)] at h
    rwa [mem_ball_zero_iff]
  have hne := expLift_ne_zero G hk.memε
  refine (PF0_expLift G k w hU).of_eventually_smul flowW_smul (analyticAt_expLift G hk.memε)
    (D.analyticAt_theta w) (nzIdx_spec hne) ?_
  have hopen : IsOpen {z' : Fin 2 → ℂ | D.Adm k z'} := isOpen_ball.preimage (continuous_const_smul _)
  filter_upwards [hopen.mem_nhds hk] with z hz
  exact ⟨_, by rw [D.theta_eq hz, ThetaData.thetaK]⟩

/-- **The untranslated homomorphism**: `law0 (θ u) (θ v) ∥ θ (u + v)`. -/
theorem ThetaData.hom_untrans (u v : Fin 2 → ℂ) :
    Par (A.law0 (D.theta u) (D.theta v)) (D.theta (u + v)) := by
  obtain ⟨w₁, hw₁⟩ := D.exists_theta0_ne
  set Y : (Fin 2 → ℂ) → P9 := fun v => normalize 0 (D.theta v)
  have hθc : Continuous D.theta := D.continuous_theta
  have hθ0c : Continuous fun v => D.theta v 0 := (continuous_apply 0).comp hθc
  -- `θ₀ ≠ 0` near `w₁`
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.mp (hθ0c.continuousAt.eventually_ne hw₁)
  -- `Y` is a chart-0 flow solution near `w₁`
  have hYd : ∀ y ∈ ball w₁ r₂, HasFDerivAt Y (flowCLM flowW 1 (Y y)) y := fun y hy =>
    (D.theta_PF0 y).hasFDerivAt_normalize flowW_smul (D.analyticAt_theta y).differentiableAt (hb₂ y hy)
  have hY0 : ∀ y ∈ ball w₁ r₂, Y y 0 = 1 := fun y hy => normalize_self 0 (hb₂ y hy)
  have hYQ : ∀ y, A.OnQ (Y y) := fun y => A.onQ_smul _ _ (D.theta_onQ y)
  -- joint nonvanishing of `Φ (z, v) = law0 (germ z) (Y v) 0` near `(0, w₁)`
  set Φ : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ := fun zv => A.law0 (germ A hp hx zv.1) (Y zv.2) 0
  have hYc : ContinuousAt Y w₁ := (hYd w₁ (mem_ball_self hr₂)).continuousAt
  have hgc : ContinuousAt (germ A hp hx) 0 := (G.good 0 (mem_ball_self G.pos)).2.2.1.continuousAt
  have hΦc : ContinuousAt Φ (0, w₁) := by
    have hL : ContinuousAt (fun XY : P9 × P9 => A.law0 XY.1 XY.2) (germ A hp hx 0, Y w₁) :=
      (A.law0_analytic _ (mem_univ _)).continuousAt
    have hpair : ContinuousAt (fun zv : (Fin 2 → ℂ) × (Fin 2 → ℂ) => (germ A hp hx zv.1, Y zv.2)) (0, w₁) :=
      (hgc.comp_of_eq continuousAt_fst rfl).prodMk (hYc.comp_of_eq continuousAt_snd rfl)
    exact (continuous_apply 0).continuousAt.comp
      (ContinuousAt.comp_of_eq (g := fun XY : P9 × P9 => A.law0 XY.1 XY.2) hL hpair rfl)
  have hΦ0 : Φ (0, w₁) ≠ 0 := by
    simp only [Φ, G.germ_zero, A.law0_origin_left, Pi.smul_apply, smul_eq_mul, hY0 w₁ (mem_ball_self hr₂)]
    simp [A.swapSign_ne]
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.mp (hΦc.eventually_ne hΦ0)
  set r := min (min r₁ (r₂ / 2)) D.ρ
  have hr : 0 < r := lt_min (lt_min hr₁ (half_pos hr₂)) D.pos
  have hr1 : r ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ r₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ D.ρ := min_le_right _ _
  have hΦne : ∀ z ∈ ball (0 : Fin 2 → ℂ) r, ∀ v ∈ ball w₁ r, Φ (z, v) ≠ 0 := fun z hz v hv => by
    apply hb₁
    rw [mem_ball, Prod.dist_eq]
    exact max_lt ((mem_ball.mp hz).trans_le hr1) ((mem_ball.mp hv).trans_le hr1)
  have hsum : ∀ z ∈ ball (0 : Fin 2 → ℂ) r, ∀ v ∈ ball w₁ r, z + v ∈ ball w₁ r₂ := fun z hz v hv => by
    rw [mem_ball] at hv ⊢; rw [mem_ball_zero_iff] at hz
    calc dist (z + v) w₁ ≤ ‖z‖ + dist v w₁ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_assoc]; exact norm_add_le _ _
      _ < r₂ := by linarith
  have hvr₂ : ∀ v ∈ ball w₁ r, v ∈ ball w₁ r₂ := fun v hv =>
    ball_subset_ball (hr2.trans (half_le_self hr₂.le)) hv
  have hzε : ∀ z ∈ ball (0 : Fin 2 → ℂ) r, z ∈ ball (0 : Fin 2 → ℂ) G.ε := fun z hz =>
    ball_subset_ball (hr3.trans D.le_ε) hz
  have hEeq : expLift A hp hx 0 = germ A hp hx := funext fun z => by simp [expLift]
  -- the local identity `normalize 0 (law0 (germ z) (Y v)) = Y (z + v)`
  have key : ∀ v ∈ ball w₁ r, ∀ z ∈ ball (0 : Fin 2 → ℂ) r,
      normalize 0 (A.law0 (germ A hp hx z) (Y v)) = Y (z + v) := by
    intro v hv
    have hYv0 := hY0 v (hvr₂ v hv)
    refine flow_unique flowW contDiff_flowW 1 (fun z hz => ?_) (fun z hz => ?_) ?_
    · have hPF := PF0_law0_expLift G 0 (hYQ v) (by rw [hYv0]; exact one_ne_zero) z (by simpa using hzε z hz)
      rw [hEeq] at hPF
      exact hPF.hasFDerivAt_normalize flowW_smul
        (analyticAt_law0_comp (G.good z (hzε z hz)).2.2.1).differentiableAt (hΦne z hz v hv)
    · have := (hYd (z + v) (hsum z hz v hv)).comp z ((hasFDerivAt_id z).add_const v)
      simpa using this
    · rw [G.germ_zero, A.law0_origin_left, hYv0, zero_add]
      exact normalize_smul_one hYv0 (by simp [A.swapSign_ne])
  -- local parallelism near `(0, w₁)`
  have hloc : ∀ᶠ zv in 𝓝 ((0 : Fin 2 → ℂ), w₁),
      Par (A.law0 (D.theta zv.1) (D.theta zv.2)) (D.theta (zv.1 + zv.2)) := by
    filter_upwards [prod_mem_nhds (ball_mem_nhds (0 : Fin 2 → ℂ) hr) (ball_mem_nhds w₁ hr)] with zv hzv
    obtain ⟨hz, hv⟩ := hzv
    set z := zv.1; set v := zv.2
    have hzρ : z ∈ ball (0 : Fin 2 → ℂ) D.ρ := ball_subset_ball hr3 hz
    have hk := key v hv z hz
    have h1 : D.theta v = D.theta v 0 • Y v := eq_smul_normalize (hb₂ v (hvr₂ v hv))
    have h2 : D.theta (z + v) = D.theta (z + v) 0 • Y (z + v) :=
      eq_smul_normalize (hb₂ _ (hsum z hz v hv))
    have h3 : A.law0 (germ A hp hx z) (Y v) = Φ (z, v) • Y (z + v) := by
      rw [← hk]; exact eq_smul_normalize (hΦne z hz v hv)
    rw [D.theta_eq_germ hzρ, h1, A.law0_smul_left, A.law0_smul_right, h3, smul_smul, smul_smul, h2]
    exact par_smul_smul _ _ _
  have hF₁ : AnalyticOnNhd ℂ (fun zv : (Fin 2 → ℂ) × (Fin 2 → ℂ) =>
      A.law0 (D.theta zv.1) (D.theta zv.2)) univ := fun zv _ => by
    have hpr : AnalyticAt ℂ (fun zv : (Fin 2 → ℂ) × (Fin 2 → ℂ) => (D.theta zv.1, D.theta zv.2)) zv :=
      ((D.analyticAt_theta zv.1).comp analyticAt_fst).prod ((D.analyticAt_theta zv.2).comp analyticAt_snd)
    exact AnalyticAt.comp (g := fun XY : P9 × P9 => A.law0 XY.1 XY.2) (A.law0_analytic _ (mem_univ _)) hpr
  have hF₂ : AnalyticOnNhd ℂ (fun zv : (Fin 2 → ℂ) × (Fin 2 → ℂ) => D.theta (zv.1 + zv.2)) univ :=
    fun zv _ => AnalyticAt.comp (g := D.theta) (f := fun zv : (Fin 2 → ℂ) × (Fin 2 → ℂ) => zv.1 + zv.2)
      (D.analyticAt_theta _) (analyticAt_fst.add analyticAt_snd)
  exact par_of_eventually isPreconnected_univ hF₁ hF₂ (mem_univ _) hloc (u, v) (mem_univ _)

end LSG.JacAn
