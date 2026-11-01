/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlockV.An
import LSG.AuxFunAV.Taylor
import LSG.JacAnV.Tau0

/-!
# M2.6 input: the Taylor package `aBlockVTay : VBlockTay aBlockV ι`

Along a line `s ↦ s • v` with `v` of size `(H_c, d_c)`, the ten functions
`V = (θ_l/θ₄ (l < 9), τ = T₁/θ₄)` solve a quadratic ODE with algebraic coefficients:
* `θ_l/θ₄` by the chart-4 flow (`A.W4_table`, as in `ThetaData.ks_chart`);
* **`τ′ = Σ_j v_j WT_{1j}(θ/θ₄)`** (`hasDerivAt_tau`) by the chart-4 fibre flow `ThetaData.fibT_flow`, with the
  `WT_{1j}` coefficients `wtNum j a b / 4` (`eval_WTV1`, `|wtNum| ≤ 32 = W4H`).

The initial values are `θ(0)/θ₄(0) = e₄` and **`τ(0) = 0`** (`ThetaData.fibT_four_origin`). `ks_quadODE` with
`n = 10` then gives `KS ι 1 (1600 H_c) 1 (4 d_c)` for `τ` (`ksT`). The base part reuses `aBlockTayD` with `c_B`
raised from `1296` to `1600 = 10² · 16` (`KS.mono`).
-/

noncomputable section

open MvPolynomial Filter Topology Finset LSG.JacAn LSG.Jac LSG.JacAnV LSG.AuxAV LSG.AuxA LSG.Aux

namespace LSG.JacBlockV

open LSG.JacBlock

/-! ### The chart-4 fibre flow quadrics as a table -/

/-- Numerators of `WT_{1j} = Σ (wtNum j a b / 4) X_a X_b`. -/
def wtNum (j : Fin 2) (a b : Fin 9) : ℤ :=
  if j = 0 then
    (if a = 0 ∧ b = 2 then -3 else if a = 1 ∧ b = 8 then -6 else if a = 3 ∧ b = 3 then 6
      else if a = 4 ∧ b = 6 then 1 else 0)
  else
    (if a = 0 ∧ b = 3 then 4 else if a = 1 ∧ b = 1 then 4 else if a = 2 ∧ b = 8 then -6
      else if a = 4 ∧ b = 7 then -1 else 0)

lemma wtNum_bound (j : Fin 2) (a b : Fin 9) : |wtNum j a b| ≤ 32 := by
  unfold wtNum; split_ifs <;> norm_num

/-- The coefficient `wtNum j a b / 4`. -/
def wtc (j : Fin 2) (a b : Fin 9) : ℂ := (wtNum j a b : ℂ) / ((4 : ℕ) : ℂ)

lemma eval_WTV1 (j : Fin 2) (Y : Fin 9 → ℂ) : eval Y (WTV 1 j) = ∑ a, ∑ b, wtc j a b * (Y a * Y b) := by
  fin_cases j <;> simp [WTV, wtc, wtNum, Fin.sum_univ_succ] <;> ring

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ)

lemma sz_wtc (j : Fin 2) (a b : Fin 9) : Sz ι (((32 : ℕ) : ℝ) / (4 : ℕ)) 4 (wtc j a b) :=
  sz_ratTable (by norm_num) (by exact_mod_cast wtNum_bound j a b)

lemma sz_W4c (j : Fin 2) (l a b : Fin 9) :
    Sz ι (((32 : ℕ) : ℝ) / (4 : ℕ)) 4 ((a1Facts.W4num j l a b : ℂ) / ((4 : ℕ) : ℂ)) :=
  sz_ratTable (by norm_num) (a1Facts.W4num_bound j l a b)

/-! ### Extension by zero `Fin 9 → Fin 10` -/

/-- Extension by zero. -/
def E9 (f : Fin 9 → ℂ) (a : Fin 10) : ℂ := if h : (a : ℕ) < 9 then f ⟨a, h⟩ else 0

@[simp] lemma E9_cs (f : Fin 9 → ℂ) (i : Fin 9) : E9 f (Fin.castSucc i) = f i := by
  simp [E9]

@[simp] lemma E9_last (f : Fin 9 → ℂ) : E9 f (Fin.last 9) = 0 := by
  simp [E9]

@[simp] lemma E9_nine (f : Fin 9 → ℂ) : E9 f 9 = 0 := by
  simp [E9]

lemma sz_E9 {H : ℝ} {d : ℕ} {f : Fin 9 → ℂ} (hf : ∀ i, Sz ι H d (f i)) (hH : 0 ≤ H) (a : Fin 10) :
    Sz ι H d (E9 f a) := by
  unfold E9; split_ifs
  · exact hf _
  · exact (Sz.zero d).mono_le hH

lemma qsum (C : Fin 9 → Fin 9 → ℂ) (V : Fin 10 → ℂ) :
    ∑ a, ∑ b, E9 (fun a' => E9 (fun b' => C a' b') b) a * (V a * V b) =
      ∑ a : Fin 9, ∑ b : Fin 9, C a b * (V (Fin.castSucc a) * V (Fin.castSucc b)) := by
  rw [Fin.sum_univ_castSucc (n := 9)]
  simp only [E9_cs, E9_last, zero_mul, sum_const_zero, add_zero]
  refine sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_castSucc (n := 9)]
  simp

/-! ### The fibre ratio along a line -/

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad a1Facts hp hx} (D : ThetaData G)

/-- `τ = T₁(·, 0)/θ₄`. -/
def τf (z : Fin 2 → ℂ) : ℂ := D.fibT 4 z 0 / D.thetaN z 4

lemma tauV_eq : tauV (aBlockVD D) = τf D := by
  funext z
  exact congrArg (· / D.thetaN z 4) (fibOf_eq D z 0 1)

lemma clm_two (L : (Fin 2 → ℂ) →L[ℂ] ℂ) (v : Fin 2 → ℂ) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) := by
  have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → ℂ) + v 1 • (Pi.single 1 1 : Fin 2 → ℂ) := by
    funext i; fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

lemma normalize_eq_smul (z : Fin 2 → ℂ) : normalize 4 (D.theta z) = (D.thetaN z 4)⁻¹ • D.thetaN z := by
  funext l
  rw [← ratio_eq_normalize D z l, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

/-- **The fibre-ratio ODE**: `d/ds τ(s v) = Σ_j v_j WT_{1j}(θ/θ₄)`. -/
theorem hasDerivAt_tau (v : Fin 2 → ℂ) (s : ℂ) (hs : D.thetaN (s • v) 4 ≠ 0) :
    HasDerivAt (fun s : ℂ => τf D (s • v))
      (∑ j : Fin 2, v j * eval (normalize 4 (D.theta (s • v))) (WTV 1 j)) s := by
  have hline : HasDerivAt (fun s : ℂ => s • v) v s := by
    simpa using (hasDerivAt_id s).smul_const v
  have hT := D.ent_fibT 4 0 (s • v)
  have hθ := ent_cmp D.analyticAt_thetaN 4 (s • v)
  have h1 := hT.differentiableAt.hasFDerivAt.comp_hasDerivAt s hline
  have h2 := hθ.differentiableAt.hasFDerivAt.comp_hasDerivAt s hline
  have hq := h1.div h2 hs
  convert hq using 1
  · funext s'; rfl
  rw [clm_two (fderiv ℂ (fun z => D.fibT 4 z 0) (s • v)), clm_two (fderiv ℂ (cmpV D.thetaN 4) (s • v))]
  have f0 := D.fibT_flow (c := 4) (Or.inr (Or.inl rfl)) 0 (s • v) 0
  have f1 := D.fibT_flow (c := 4) (Or.inr (Or.inl rfl)) 1 (s • v) 0
  simp only [pd] at f0 f1
  rw [Fin.sum_univ_two, normalize_eq_smul, eval_smul_of_isHomogeneous (WTV_hom 1 0),
    eval_smul_of_isHomogeneous (WTV_hom 1 1), eval_WTV, eval_WTV]
  simp only [fcV_1, Function.comp_apply, cmpV] at f0 f1 ⊢
  rw [eq_div_iff (pow_ne_zero 2 hs)]
  have hinv : (D.thetaN (s • v) 4)⁻¹ ^ 2 * D.thetaN (s • v) 4 ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hs, one_pow]
  linear_combination (v 0 * (1 / 3 * kQ 4 0 0 (D.thetaN (s • v))) +
    v 1 * (1 / 3 * kQ 4 1 0 (D.thetaN (s • v)))) * hinv - v 0 * f0 - v 1 * f1

/-! ### The ten-function ODE -/

/-- The chart-4 coefficients along `v`. -/
def c4 (v : Fin 2 → ℂ) (l a b : Fin 9) : ℂ :=
  v 0 * ((a1Facts.W4num 0 l a b : ℂ) / ((4 : ℕ) : ℂ)) + v 1 * ((a1Facts.W4num 1 l a b : ℂ) / ((4 : ℕ) : ℂ))

/-- The fibre coefficients along `v`. -/
def cT (v : Fin 2 → ℂ) (a b : Fin 9) : ℂ := v 0 * wtc 0 a b + v 1 * wtc 1 a b

/-- The ten functions. -/
def V10 (v : Fin 2 → ℂ) (l : Fin 10) (s : ℂ) : ℂ :=
  if h : (l : ℕ) < 9 then normalize 4 (D.theta (s • v)) ⟨l, h⟩ else τf D (s • v)

/-- The ten-function coefficients. -/
def q10 (v : Fin 2 → ℂ) (l : Fin 10) : Fin 10 → Fin 10 → ℂ :=
  if h : (l : ℕ) < 9 then fun a b => E9 (fun a' => E9 (fun b' => c4 v ⟨l, h⟩ a' b') b) a
  else fun a b => E9 (fun a' => E9 (fun b' => cT v a' b') b) a

@[simp] lemma V10_cs (v : Fin 2 → ℂ) (i : Fin 9) (s : ℂ) :
    V10 D v (Fin.castSucc i) s = normalize 4 (D.theta (s • v)) i := by
  simp [V10]

@[simp] lemma V10_last (v : Fin 2 → ℂ) (s : ℂ) : V10 D v (Fin.last 9) s = τf D (s • v) := by
  simp [V10]

lemma q10_cs (v : Fin 2 → ℂ) (i : Fin 9) :
    q10 v (Fin.castSucc i) = fun a b => E9 (fun a' => E9 (fun b' => c4 v i a' b') b) a := by
  simp [q10]

lemma q10_last (v : Fin 2 → ℂ) :
    q10 v (Fin.last 9) = fun a b => E9 (fun a' => E9 (fun b' => cT v a' b') b) a := by
  simp [q10]

lemma theta_four_zero : D.theta 0 4 ≠ 0 := by
  obtain ⟨a, ha, h0⟩ := D.theta_zero
  rw [h0]; simpa [origin9] using ha

lemma eventually_ne (v : Fin 2 → ℂ) : ∀ᶠ s in 𝓝 (0 : ℂ), D.theta (s • v) 4 ≠ 0 := by
  have hcont : Continuous fun s : ℂ => D.theta (s • v) 4 :=
    (continuous_apply 4).comp (D.continuous_theta.comp (continuous_id.smul continuous_const))
  exact hcont.continuousAt.eventually_ne (by simpa using theta_four_zero D)

lemma ode_Y (v : Fin 2 → ℂ) (l : Fin 9) :
    deriv (fun s : ℂ => normalize 4 (D.theta (s • v)) l) =ᶠ[𝓝 0]
      fun s : ℂ => ∑ a, ∑ b, c4 v l a b * (normalize 4 (D.theta (s • v)) a * normalize 4 (D.theta (s • v)) b) := by
  have hline : ∀ s : ℂ, HasDerivAt (fun s : ℂ => s • v) v s := fun s => by
    simpa using (hasDerivAt_id s).smul_const v
  filter_upwards [eventually_ne D v] with s hs
  have hYd := (D.theta_PF4 (s • v)).hasFDerivAt_normalize a1Facts.W4_smul
    (D.analyticAt_theta _).differentiableAt hs
  have h0 := ((prj l).hasFDerivAt.comp (s • v) hYd).comp_hasDerivAt s (hline s)
  have h1 : HasDerivAt (fun s : ℂ => normalize 4 (D.theta (s • v)) l) _ s := h0
  rw [h1.deriv]
  simp only [ContinuousLinearMap.comp_apply, flowCLM_apply, one_smul, prj,
    ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a1Facts.W4_table, mul_sum, c4,
    add_mul, sum_add_distrib]
  have hd : (a1Facts.W4den : ℂ) = ((4 : ℕ) : ℂ) := rfl
  simp only [hd]
  refine congrArg₂ _ (sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring)
    (sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring)

lemma ode10 (v : Fin 2 → ℂ) (l : Fin 10) :
    deriv (V10 D v l) =ᶠ[𝓝 0] fun s => ∑ a, ∑ b, q10 v l a b * (V10 D v a s * V10 D v b s) := by
  induction l using Fin.lastCases with
  | last =>
    rw [q10_last]
    have e : V10 D v (Fin.last 9) = fun s => τf D (s • v) := funext fun s => V10_last D v s
    rw [e]
    have hne : ∀ᶠ s in 𝓝 (0 : ℂ), D.thetaN (s • v) 4 ≠ 0 := by
      filter_upwards [eventually_ne D v] with s hs using D.thetaN_cmp_ne hs
    filter_upwards [hne] with s hs
    rw [(hasDerivAt_tau D v s hs).deriv, qsum (cT v) (fun a => V10 D v a s)]
    simp only [V10_cs, Fin.sum_univ_two, eval_WTV1, cT, add_mul, sum_add_distrib, mul_sum]
    refine congrArg₂ _ (sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring)
      (sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring)
  | cast i =>
    rw [q10_cs]
    have e : V10 D v (Fin.castSucc i) = fun s => normalize 4 (D.theta (s • v)) i :=
      funext fun s => V10_cs D v i s
    rw [e]
    filter_upwards [ode_Y D v i] with s hs
    rw [hs, qsum (c4 v i) (fun a => V10 D v a s)]
    simp only [V10_cs]

lemma analytic10 (v : Fin 2 → ℂ) (l : Fin 10) : AnalyticAt ℂ (V10 D v l) 0 := by
  have hz : D.theta ((0 : ℂ) • v) 4 ≠ 0 := by simpa using theta_four_zero D
  have hlin : AnalyticAt ℂ (fun s : ℂ => s • v) 0 := by fun_prop
  induction l using Fin.lastCases with
  | last =>
    have e : V10 D v (Fin.last 9) = fun s => τf D (s • v) := funext fun s => V10_last D v s
    rw [e]
    have hT : AnalyticAt ℂ (fun s : ℂ => D.fibT 4 (s • v) 0) 0 :=
      AnalyticAt.comp (f := fun s : ℂ => s • v) (g := fun z => D.fibT 4 z 0) (D.ent_fibT 4 0 _) hlin
    have hθ : AnalyticAt ℂ (fun s : ℂ => D.thetaN (s • v) 4) 0 :=
      AnalyticAt.comp (f := fun s : ℂ => s • v) (g := cmpV D.thetaN 4) (ent_cmp D.analyticAt_thetaN 4 _) hlin
    exact hT.div hθ (D.thetaN_cmp_ne hz)
  | cast i =>
    have e : V10 D v (Fin.castSucc i) = fun s => normalize 4 (D.theta (s • v)) i :=
      funext fun s => V10_cs D v i s
    rw [e]
    have h1 : AnalyticAt ℂ (fun w => D.theta w 4) ((0 : ℂ) • v) :=
      (analyticAt_pi_iff.mp (D.analyticAt_theta _)) 4
    have hY : AnalyticAt ℂ (fun w => normalize 4 (D.theta w)) ((0 : ℂ) • v) :=
      (h1.inv hz).smul (D.analyticAt_theta _)
    exact (analyticAt_pi_iff.mp (AnalyticAt.comp (f := fun s : ℂ => s • v)
      (g := fun w => normalize 4 (D.theta w)) hY hlin)) i

lemma init10 (v : Fin 2 → ℂ) (l : Fin 10) : Sz ι 1 1 (V10 D v l 0) := by
  induction l using Fin.lastCases with
  | last =>
    rw [V10_last, zero_smul, τf]
    have h0 : D.fibT 4 0 0 = 0 := D.fibT_four_origin
    rw [h0, zero_div]
    exact (Sz.zero 1).mono_le zero_le_one
  | cast i =>
    rw [V10_cs, zero_smul]
    obtain ⟨a, ha, h0⟩ := D.theta_zero
    rw [h0]
    by_cases hl : i = 4
    · subst hl; simpa [JacAn.normalize, origin9, ha] using Sz.one (ι := ι)
    · simpa [JacAn.normalize, origin9, Pi.single_apply, hl] using (Sz.zero (ι := ι) 1).mono_le zero_le_one

/-- **`KS` for the fibre ratio.** -/
theorem ks_tau (v : Fin 2 → ℂ) (Hc : ℝ) (dc : ℕ) (hHc : 1 ≤ Hc) (hv : ∀ j, Sz ι Hc dc (v j)) :
    KS ι 1 (1600 * Hc) 1 (dc * 4) (fun s => τf D (s • v)) := by
  have hH0 : (0 : ℝ) ≤ Hc * (((32 : ℕ) : ℝ) / (4 : ℕ)) + Hc * (((32 : ℕ) : ℝ) / (4 : ℕ)) := by positivity
  have hq : ∀ l a b, Sz ι (Hc * (((32 : ℕ) : ℝ) / (4 : ℕ)) + Hc * (((32 : ℕ) : ℝ) / (4 : ℕ))) (dc * 4)
      (q10 v l a b) := by
    intro l a b
    unfold q10
    split_ifs with h
    · exact sz_E9 ι (fun a' => sz_E9 ι (fun b' => ((hv 0).mul (sz_W4c ι 0 _ a' b')).add
        ((hv 1).mul (sz_W4c ι 1 _ a' b'))) hH0 b) hH0 a
    · exact sz_E9 ι (fun a' => sz_E9 ι (fun b' => ((hv 0).mul (sz_wtc ι 0 a' b')).add
        ((hv 1).mul (sz_wtc ι 1 a' b'))) hH0 b) hH0 a
  have h := ks_quadODE (n := 10) (A := 1) (B := 1600 * Hc) (E := 1) (analytic10 D v) (ode10 D v) hq (init10 ι D v) le_rfl (by nlinarith)
    (by push_cast; nlinarith) (Fin.last 9)
  rw [mul_one] at h
  convert h using 1
  funext s
  exact (V10_last D v s).symm

/-! ### The package -/

/-- The base Taylor package with `c_B = 1600`. -/
def aBlockTay1600 : AbBlockTay (aBlockD D) ι where
  A := 1
  one_le_A := le_rfl
  cB := 1600
  one_le_cB := by norm_num
  E := 1
  one_le_E := le_rfl
  δ := 4
  one_le_δ := by norm_num
  ks v Hc dc hHc hv j := by
    have h := (aBlockTayD D K ι).ks v Hc dc hHc hv j
    have hδ : (aBlockTayD D K ι).δ = 4 := rfl
    have hA : (aBlockTayD D K ι).A = 1 := rfl
    have hE : (aBlockTayD D K ι).E = 1 := rfl
    have hB : (aBlockTayD D K ι).cB = 1296 := cBA_eq
    rw [hδ, hA, hE, hB] at h
    exact h.mono le_rfl (by positivity) (by nlinarith) dvd_rfl dvd_rfl

/-- **The Taylor package of `A_σ̄^♮`** (any `θ`-datum, any number field). -/
def aBlockVTayD : VBlockTay (aBlockVD D) ι :=
  { aBlockTay1600 ι D with
    ksT := fun v Hc dc hHc hv => by
      rw [tauV_eq]
      exact ks_tau ι D v Hc dc hHc hv }

/-- **The Taylor package of `aBlockV`.** -/
def aBlockVTay : VBlockTay aBlockV ι := aBlockVTayD ι stdPkg.D

end LSG.JacBlockV
