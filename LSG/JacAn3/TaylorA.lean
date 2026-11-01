/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.PsiLiouville
import LSG.JacAn3.QuadODE

/-!
# Algebraic Taylor coefficients of the A-block coordinates (STAGE_A3 §3.2)

The A-block analogue of `ks_wpSeries`. Fix a point `z₀` and a direction `c ∈ ℂ²`. In a chart `X_{ci} = 1` in which
`θ` satisfies a projective flow `W` with quadratic, algebraic coefficients, the affine coordinates
`V_l(s) = θ(z₀ + s c)_l / θ(z₀ + s c)_{ci}` solve `V' = c₀ W₀(V) + c₁ W₁(V)`, so `ks_quadODE` applies:

* **`ThetaData.ks_chart`** (general chart);
* **`ThetaData.ks_chart0`**: chart `X₀ = 1` with the explicit `flowW` (coefficients in `½ℤ`, `|·| ≤ 10`): if the
  `c_j` have size `(H_c, d_c)` and the affine coordinates of `E(z₀)` have size `(A, E)`, then every
  `s ↦ V_l(s)` is `KS ι A B E (2 d_c E)` for `1 ≤ A`, `1 ≤ B`, `81 · 20 H_c A ≤ B`;
* **`ThetaData.ks_chart4`**: chart `X₄ = 1` with `A.W4`, given its quadratic coefficients and their sizes (A1 data).

The coordinates are those of `E = [θ] = [θ_N]` (`normalize_thetaN`).
-/

open Finset Filter Topology Metric Set

noncomputable section

namespace LSG.JacAn

open LSG.Aux

/-! ### The quadratic coefficients of `flowW` -/

/-- The monomial `(k/2) X_a X_b` as a coefficient table. -/
def qm (a b : Fin 9) (k : ℤ) : Fin 9 → Fin 9 → ℂ := fun a' b' => if a' = a ∧ b' = b then (k : ℂ) / 2 else 0

lemma sum_qm (a b : Fin 9) (k : ℤ) (X : P9) :
    ∑ a', ∑ b', qm a b k a' b' * (X a' * X b') = (k : ℂ) / 2 * (X a * X b) := by
  rw [Finset.sum_eq_single a (fun a' _ ha' => by simp [qm, ha']) (by simp),
    Finset.sum_eq_single b (fun b' _ hb' => by simp [qm, hb']) (by simp)]
  simp [qm]

/-- The coefficient tables of `flowW 0` and `flowW 1`. -/
def flowC : Fin 2 → Fin 9 → Fin 9 → Fin 9 → ℂ :=
  ![![qm 0 0 0, qm 0 4 2, qm 0 5 2, qm 0 6 2, qm 0 3 (-6) + qm 1 1 12, qm 0 0 (-2) + qm 1 2 12,
      qm 0 8 8 + qm 1 3 12, qm 0 1 (-4) + qm 2 3 12, qm 1 6 (-6) + qm 2 5 6],
    ![qm 0 0 0, qm 0 5 2, qm 0 6 2, qm 0 7 2, qm 0 0 (-2) + qm 1 2 12, qm 0 8 8 + qm 1 3 12,
      qm 0 1 (-4) + qm 2 3 12, qm 0 2 8 + qm 3 3 12, qm 0 4 (-1) + qm 1 7 (-3) + qm 2 6 3]]

lemma flowW_quad (j : Fin 2) (X : P9) (l : Fin 9) :
    flowW j X l = ∑ a, ∑ b, flowC j l a b * (X a * X b) := by
  fin_cases j <;> fin_cases l <;>
    simp only [flowC, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Pi.add_apply,
      add_mul, Finset.sum_add_distrib, sum_qm, flowW] <;> simp <;> ring

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

lemma sz_qm (a b : Fin 9) (k : ℤ) (a' b' : Fin 9) : Sz ι (|(k : ℝ)| / 2) 2 (qm a b k a' b') := by
  unfold qm
  split_ifs
  · have := (Sz.intCast (ι := ι) k).div_nat (n := 2) (by norm_num)
    simpa using this
  · exact (Sz.zero 2).mono_le (by positivity)

lemma sz_flowC (j : Fin 2) (l a b : Fin 9) : Sz ι 10 2 (flowC j l a b) := by
  fin_cases j <;> fin_cases l <;>
    simp only [flowC, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Pi.add_apply] <;>
    first
    | exact (sz_qm _ _ _ a b).mono_le (by norm_num)
    | exact ((sz_qm _ _ _ a b).add (sz_qm _ _ _ a b)).mono_le (by norm_num)
    | exact (((sz_qm _ _ _ a b).add (sz_qm _ _ _ a b)).add (sz_qm _ _ _ a b)).mono_le (by norm_num)

/-! ### The general chart -/

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

lemma normalize_smul_inv {c : Fin 9} {X : P9} {a : ℂ} (ha : a ≠ 0) : normalize c (a • X) = normalize c X := by
  by_cases hX : X c = 0
  · simp [normalize, hX]
  · simp only [normalize, Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv]
    congr 1; field_simp

/-- The affine coordinates of `E` are those of `θ` and of `θ_N`. -/
lemma ThetaData.normalize_thetaN (c : Fin 9) (z : Fin 2 → ℂ) :
    normalize c (D.thetaN z) = normalize c (D.theta z) :=
  normalize_smul_inv (Complex.exp_ne_zero _)

/-- **Algebraic Taylor coefficients in a chart with a quadratic algebraic flow.** -/
theorem ThetaData.ks_chart (W : Fin 2 → P9 → P9) (hWs : ∀ j (a : ℂ) X, W j (a • X) = a ^ 2 • W j X)
    (ci : Fin 9) (hPF : ∀ w, PFAt W 1 ci D.theta w) (Wc : Fin 2 → Fin 9 → Fin 9 → Fin 9 → ℂ)
    (hWc : ∀ j X l, W j X l = ∑ a, ∑ b, Wc j l a b * (X a * X b)) {HW : ℝ} {dW : ℕ}
    (hWsz : ∀ j l a b, Sz ι HW dW (Wc j l a b)) {z₀ c : Fin 2 → ℂ} (hz : D.theta z₀ ci ≠ 0) {Hc : ℝ}
    {dc : ℕ} (hc : ∀ j, Sz ι Hc dc (c j)) {A' B : ℝ} {E : ℕ}
    (h0 : ∀ l, Sz ι A' E (normalize ci (D.theta z₀) l)) (hA : 1 ≤ A') (hB1 : 1 ≤ B)
    (hB : 81 * (Hc * HW + Hc * HW) * A' ≤ B) :
    ∀ l, KS ι A' B E (dc * dW * E) (fun s => normalize ci (D.theta (z₀ + s • c)) l) := by
  set Y : (Fin 2 → ℂ) → P9 := fun w => normalize ci (D.theta w)
  set line : ℂ → (Fin 2 → ℂ) := fun s => z₀ + s • c
  have hline : ∀ s, HasDerivAt line c s := fun s => by
    simpa [line] using ((hasDerivAt_id s).smul_const c).const_add z₀
  have hcont : Continuous fun s => D.theta (line s) ci :=
    (continuous_apply ci).comp (D.continuous_theta.comp (continuous_const.add (continuous_id.smul continuous_const)))
  have hne : ∀ᶠ s in 𝓝 (0 : ℂ), D.theta (line s) ci ≠ 0 :=
    hcont.continuousAt.eventually_ne (by simpa [line] using hz)
  have hYan : ∀ w, D.theta w ci ≠ 0 → AnalyticAt ℂ Y w := fun w hw => by
    have h1 : AnalyticAt ℂ (fun w => D.theta w ci) w := (analyticAt_pi_iff.mp (D.analyticAt_theta w)) ci
    exact (h1.inv hw).smul (D.analyticAt_theta w)
  have hlinean : ∀ s, AnalyticAt ℂ line s := fun s => by fun_prop
  set q : Fin 9 → Fin 9 → Fin 9 → ℂ := fun l a b => c 0 * Wc 0 l a b + c 1 * Wc 1 l a b
  have hq : ∀ l a b, Sz ι (Hc * HW + Hc * HW) (dc * dW) (q l a b) := fun l a b =>
    ((hc 0).mul (hWsz 0 l a b)).add ((hc 1).mul (hWsz 1 l a b))
  have hV : ∀ l, AnalyticAt ℂ (fun s => Y (line s) l) 0 := fun l =>
    (analyticAt_pi_iff.mp ((hYan (line 0) (by simpa [line] using hz)).comp (hlinean 0))) l
  have hODE : ∀ l, deriv (fun s => Y (line s) l) =ᶠ[𝓝 0]
      fun s => ∑ a, ∑ b, q l a b * (Y (line s) a * Y (line s) b) := by
    intro l
    filter_upwards [hne] with s hs
    have hYd := (hPF (line s)).hasFDerivAt_normalize hWs (D.analyticAt_theta _).differentiableAt hs
    have h1 : HasDerivAt (fun s => Y (line s) l) _ s :=
      ((prj l).hasFDerivAt.comp (line s) hYd).comp_hasDerivAt s (hline s)
    rw [h1.deriv]
    simp only [ContinuousLinearMap.comp_apply, flowCLM_apply, one_smul, prj,
      ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hWc, mul_sum, q, add_mul,
      sum_add_distrib]
    refine congrArg₂ _ (sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring)
      (sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring)
  have h0' : ∀ l, Sz ι A' E (Y (line 0) l) := fun l => by simpa [line, Y] using h0 l
  have := ks_quadODE (n := 9) hV hODE hq h0' hA hB1 (by norm_num; linarith)
  intro l
  exact this l

/-- `θ` satisfies the chart-4 projective flow equation everywhere. -/
theorem ThetaData.theta_PF4 (w : Fin 2 → ℂ) : PFAt A.W4 1 4 D.theta w := by
  obtain ⟨k, hk⟩ := D.exists_adm w
  have hU : w ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := by
    have h := hk.memε
    rw [mem_ball_zero_iff, norm_smul, norm_inv, norm_pow] at h
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, inv_mul_lt_iff₀ (by positivity)] at h
    rwa [mem_ball_zero_iff]
  have hne := expLift_ne_zero G hk.memε
  refine (PF4_expLift G k w hU).of_eventually_smul A.W4_smul (analyticAt_expLift G hk.memε)
    (D.analyticAt_theta w) (nzIdx_spec hne) ?_
  have hopen : IsOpen {z' : Fin 2 → ℂ | D.Adm k z'} := isOpen_ball.preimage (continuous_const_smul _)
  filter_upwards [hopen.mem_nhds hk] with z hz
  exact ⟨_, by rw [D.theta_eq hz, ThetaData.thetaK]⟩

/-- **Chart `X₀ = 1`** (explicit `flowW`). -/
theorem ThetaData.ks_chart0 {z₀ c : Fin 2 → ℂ} (hz : D.theta z₀ 0 ≠ 0) {Hc : ℝ} {dc : ℕ}
    (hc : ∀ j, Sz ι Hc dc (c j)) {A' B : ℝ} {E : ℕ} (h0 : ∀ l, Sz ι A' E (normalize 0 (D.theta z₀) l))
    (hA : 1 ≤ A') (hB1 : 1 ≤ B) (hB : 81 * (20 * Hc) * A' ≤ B) :
    ∀ l, KS ι A' B E (dc * 2 * E) (fun s => normalize 0 (D.theta (z₀ + s • c)) l) :=
  D.ks_chart flowW flowW_smul 0 D.theta_PF0 flowC flowW_quad sz_flowC hz hc h0 hA hB1 (by linarith)

/-- **Chart `X₄ = 1`** (`A.W4`, given its quadratic coefficients and their sizes). -/
theorem ThetaData.ks_chart4 (W4c : Fin 2 → Fin 9 → Fin 9 → Fin 9 → ℂ)
    (hW4c : ∀ j X l, A.W4 j X l = ∑ a, ∑ b, W4c j l a b * (X a * X b)) {HW : ℝ} {dW : ℕ}
    (hWsz : ∀ j l a b, Sz ι HW dW (W4c j l a b)) {z₀ c : Fin 2 → ℂ} (hz : D.theta z₀ 4 ≠ 0) {Hc : ℝ}
    {dc : ℕ} (hc : ∀ j, Sz ι Hc dc (c j)) {A' B : ℝ} {E : ℕ}
    (h0 : ∀ l, Sz ι A' E (normalize 4 (D.theta z₀) l)) (hA : 1 ≤ A') (hB1 : 1 ≤ B)
    (hB : 81 * (Hc * HW + Hc * HW) * A' ≤ B) :
    ∀ l, KS ι A' B E (dc * dW * E) (fun s => normalize 4 (D.theta (z₀ + s • c)) l) :=
  D.ks_chart A.W4 A.W4_smul 4 D.theta_PF4 W4c hW4c hWsz hz hc h0 hA hB1 hB

end LSG.JacAn
