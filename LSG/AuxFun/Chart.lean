/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.AlgPoints
import LSG.AuxFun.ExpCoords
import LSG.AuxFun.WpSeries

/-!
# Charts for `exp_E` with lower bounds (Stage 3, D3a)

* `ellV L u = (σ³℘, σ³℘', σ³)(u)` (the cone coordinates `(U, V, W)` of `exp_E(u)`, entire);
  **`isRep_ellV`**: `ellV L u` represents `exp_E(u)` for every `u` (also on the lattice).
* **`exists_chart`** (replaces W83 Lemma 2.2 and the set `𝒯`): there are `ρ₀ > 0`, `c ≥ 0` such that
  for every `u ∈ ℂ` some coordinate `i` satisfies `|ellV(u + z)_i| ≥ e^{−c(1+|u|)²}` for all
  `|z| ≤ ρ₀`. (Quasi-periodicity reduces `u` to a fundamental domain; `ellV` never vanishes; uniform
  continuity on a compact disc.)
* `isRep_xi`: `(℘(z₀ + c s), ℘'(z₀ + c s), 1)` represents `exp_E(z₀ + c s)` near `s = 0`;
  `isRep_half`: `(e₁, 0, 1)` represents `exp_E(z₀)`.
-/

open Complex Finset Filter Topology LSG.Elliptic LSG.Weierstrass PeriodPair

noncomputable section

namespace LSG.Aux

variable (L : PeriodPair)

/-- The cone coordinates `(U, V, W) = (σ³℘, σ³℘', σ³)` of `exp_E`. -/
def ellV (u : ℂ) : Fin 3 → ℂ := ![ellW L 1 u, ellW L 2 u, ellW L 0 u]

lemma differentiable_ellV_apply (i : Fin 3) : Differentiable ℂ fun u => ellV L u i := by
  fin_cases i
  · exact differentiable_ellW L 1
  · exact differentiable_ellW L 2
  · exact differentiable_ellW L 0

lemma continuous_ellV : Continuous (ellV L) :=
  continuous_pi fun i => (differentiable_ellV_apply L i).continuous

lemma ellV_add {lam : ℂ} (hlam : lam ∈ L.lattice) (u : ℂ) :
    ellV L (u + lam) = sigmaMult L lam u ^ 3 • ellV L u := by
  funext i
  fin_cases i <;> simp [ellV, ellW_add L hlam]

lemma ellV_zero : ellV L 0 = ![0, -2, 0] := by
  have h0 : sigma L 0 = 0 := (sigma_eq_zero_iff L).mpr L.lattice.zero_mem
  have h1 : deriv (sigma L) 0 = 1 := deriv_sigma_zero L
  funext i
  fin_cases i <;> simp [ellV, ellW, h0, h1]

lemma isRep_affine {u : ℂ} (hu : u ∉ L.lattice) : IsRep L u ![℘[L] u, ℘'[L] u, 1] := by
  refine ⟨fun h => by simpa using congrFun h 2, ?_, ?_⟩
  · simp only [Fv, F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have := L.derivWeierstrassP_sq u hu
    linear_combination this
  · have hns : (curve L.g₂ L.g₃).toAffine.Nonsingular (℘[L] u) (℘'[L] u / 2) :=
      nonsingular_weierstrassP L hu
    rw [toPoint_some _ _ hns, expE_of_notMem L hu]
    rfl

lemma isRep_smul {u : ℂ} {X : Fin 3 → ℂ} (hX : IsRep L u X) {c : ℂ} (hc : c ≠ 0) :
    IsRep L u (c • X) := by
  refine ⟨smul_ne_zero hc hX.1, ?_, by rw [toPoint_smul _ hc]; exact hX.2.2⟩
  have := hX.2.1
  simp only [Fv, F, Pi.smul_apply, smul_eq_mul] at this ⊢
  linear_combination c ^ 3 * this

/-- **`ellV L u` represents `exp_E(u)`.** -/
theorem isRep_ellV (u : ℂ) : IsRep L u (ellV L u) := by
  by_cases hu : u ∈ L.lattice
  · have h := ellV_add L hu 0
    rw [zero_add, ellV_zero] at h
    have hm : sigmaMult L u 0 ^ 3 ≠ 0 := by
      unfold sigmaMult
      exact pow_ne_zero _ (mul_ne_zero (by
        intro h0; have := norm_sigmaSign L u; rw [h0, norm_zero] at this; norm_num at this)
        (Complex.exp_ne_zero _))
    have hO : (![0, -2, 0] : Fin 3 → ℂ) = (-2 : ℂ) • O := by
      funext i; fin_cases i <;> simp [O]
    rw [h, hO, smul_smul]
    refine isRep_smul L ⟨fun h => by simpa [O] using congrFun h 1, Fv_O _ _, ?_⟩ (mul_ne_zero hm
      (by norm_num))
    rw [toPoint_O, expE_of_mem L hu]; rfl
  · obtain ⟨h1, h2⟩ := ellW_eq_off L hu
    have : ellV L u = sigma L u ^ 3 • ![℘[L] u, ℘'[L] u, 1] := by
      funext i
      fin_cases i
      · exact h1
      · exact h2
      · show ellW L 0 u = sigma L u ^ 3 * 1
        simp [ellW]
    rw [this]
    exact isRep_smul L (isRep_affine L hu) (pow_ne_zero _ (sigma_ne_zero L hu))

lemma ellV_ne_zero (u : ℂ) : ellV L u ≠ 0 := (isRep_ellV L u).1

/-- The multiplier is bounded below. -/
lemma norm_sigmaMult_ge {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ lam ∈ L.lattice, ‖eta L lam‖ ≤ C * ‖lam‖)
    {lam : ℂ} (hlam : lam ∈ L.lattice) (z : ℂ) :
    Real.exp (-(C * (‖z‖ + ‖lam‖) ^ 2)) ≤ ‖sigmaMult L lam z‖ := by
  unfold sigmaMult
  rw [norm_mul, norm_sigmaSign, one_mul, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have h1 : ‖z + lam / 2‖ ≤ ‖z‖ + ‖lam‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg lam]
  have h2 : |(eta L lam * (z + lam / 2)).re| ≤ C * (‖z‖ + ‖lam‖) ^ 2 := by
    refine (abs_re_le_norm _).trans ?_
    rw [norm_mul]
    calc ‖eta L lam‖ * ‖z + lam / 2‖ ≤ (C * ‖lam‖) * (‖z‖ + ‖lam‖) := by
          gcongr; exact hC lam hlam
      _ ≤ C * (‖z‖ + ‖lam‖) ^ 2 := by
          have : ‖lam‖ ≤ ‖z‖ + ‖lam‖ := by linarith [norm_nonneg z]
          have h0 : 0 ≤ ‖z‖ + ‖lam‖ := by positivity
          calc C * ‖lam‖ * (‖z‖ + ‖lam‖) ≤ C * (‖z‖ + ‖lam‖) * (‖z‖ + ‖lam‖) := by gcongr
            _ = C * (‖z‖ + ‖lam‖) ^ 2 := by ring
  linarith [neg_abs_le (eta L lam * (z + lam / 2)).re]

/-- **Chart lower bound** (replaces W83 Lemma 2.2). -/
theorem exists_chart : ∃ ρ₀ c : ℝ, 0 < ρ₀ ∧ 0 ≤ c ∧ ∀ u : ℂ, ∃ i : Fin 3, ∀ z : ℂ, ‖z‖ ≤ ρ₀ →
    Real.exp (-(c * (1 + ‖u‖) ^ 2)) ≤ ‖ellV L (u + z) i‖ := by
  obtain ⟨Cη, hCη0, hCη⟩ := exists_eta_bound L
  obtain ⟨Bd, hBd0, hdec⟩ := exists_decomp L
  set B₀ : ℝ := ‖L.ω₁‖ + ‖L.ω₂‖
  have hB₀ : 0 ≤ B₀ := by positivity
  set Kc : Set ℂ := Metric.closedBall 0 (B₀ + 1)
  have hKc : IsCompact Kc := isCompact_closedBall _ _
  have hKne : Kc.Nonempty := ⟨0, by simp [Kc]; positivity⟩
  -- minimum of `‖ellV‖` on the disc
  obtain ⟨x₀, -, hx₀⟩ := hKc.exists_isMinOn hKne ((continuous_ellV L).norm.continuousOn)
  set m₀ := ‖ellV L x₀‖
  have hm₀ : 0 < m₀ := norm_pos_iff.mpr (ellV_ne_zero L x₀)
  -- uniform continuity
  have huc := hKc.uniformContinuousOn_of_continuous (continuous_ellV L).continuousOn
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := huc (m₀ / 2) (by positivity)
  set ρ₀ := min ρ₁ 1
  have hρ₀ : 0 < ρ₀ := lt_min hρ₁ one_pos
  -- constants
  set c₁ : ℝ := max 0 (-Real.log (m₀ / 2))
  set c : ℝ := 3 * Cη * (B₀ + 1 + B₀ + 1) ^ 2 + c₁
  refine ⟨ρ₀, c, hρ₀, by positivity, fun u => ?_⟩
  obtain ⟨mm, nn, hδ, -, -⟩ := hdec u
  set lam : ℂ := mm * L.ω₁ + nn * L.ω₂
  have hlam : lam ∈ L.lattice := L.mem_lattice.mpr ⟨mm, nn, rfl⟩
  set δ : ℂ := u - lam
  have hδ' : ‖δ‖ ≤ B₀ := by
    have : δ = u - mm * L.ω₁ - nn * L.ω₂ := by simp only [δ, lam]; ring
    rw [this]; exact hδ
  have hlamu : ‖lam‖ ≤ ‖u‖ + B₀ := by
    have : lam = u - δ := by simp only [δ]; ring
    rw [this]; exact (norm_sub_le _ _).trans (by linarith)
  -- the good coordinate at `δ`
  obtain ⟨i, hi⟩ : ∃ i, ‖ellV L δ‖ = ‖ellV L δ i‖ := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' univ_nonempty fun i => ‖ellV L δ i‖₊
    refine ⟨i, ?_⟩
    rw [← coe_nnnorm, Pi.nnnorm_def, ← Finset.sup'_eq_sup univ_nonempty, hi, coe_nnnorm]
  have hδK : δ ∈ Kc := by simp only [Kc, Metric.mem_closedBall, dist_zero_right]; linarith
  have hδm : m₀ ≤ ‖ellV L δ i‖ := by rw [← hi]; exact hx₀ hδK
  refine ⟨i, fun z hz => ?_⟩
  have hz1 : ‖z‖ ≤ 1 := hz.trans (min_le_right _ _)
  have hzρ : ‖z‖ ≤ ρ₁ := hz.trans (min_le_left _ _)
  have hδzK : δ + z ∈ Kc := by
    simp only [Kc, Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le _ _).trans (by linarith)
  have hclose : dist (ellV L δ) (ellV L (δ + z)) ≤ m₀ / 2 :=
    hρ₁' δ hδK (δ + z) hδzK (by simpa [dist_eq_norm] using hzρ)
  have hδz : m₀ / 2 ≤ ‖ellV L (δ + z) i‖ := by
    have h1 : ‖ellV L δ i - ellV L (δ + z) i‖ ≤ m₀ / 2 := by
      rw [dist_eq_norm] at hclose
      exact (norm_le_pi_norm (ellV L δ - ellV L (δ + z)) i).trans hclose
    have := norm_sub_norm_le (ellV L δ i) (ellV L (δ + z) i)
    linarith
  have hsplit : u + z = (δ + z) + lam := by simp only [δ]; ring
  rw [hsplit, ellV_add L hlam, Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  have hmult := norm_sigmaMult_ge L hCη0 hCη hlam (δ + z)
  have hδzn : ‖δ + z‖ ≤ B₀ + 1 := (norm_add_le _ _).trans (by linarith)
  -- assemble
  have hexp1 : Real.exp (-(Cη * (‖δ + z‖ + ‖lam‖) ^ 2)) ^ 3 =
      Real.exp (-(3 * Cη * (‖δ + z‖ + ‖lam‖) ^ 2)) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hlog : Real.exp (-c₁) ≤ m₀ / 2 := by
    calc Real.exp (-c₁) ≤ Real.exp (Real.log (m₀ / 2)) := by
          refine Real.exp_le_exp.mpr ?_
          have := le_max_right 0 (-Real.log (m₀ / 2)); linarith
      _ = m₀ / 2 := Real.exp_log (by positivity)
  have hsq : (‖δ + z‖ + ‖lam‖) ^ 2 ≤ (B₀ + 1 + B₀ + 1) ^ 2 * (1 + ‖u‖) ^ 2 := by
    have h0 : 0 ≤ ‖δ + z‖ + ‖lam‖ := by positivity
    have : ‖δ + z‖ + ‖lam‖ ≤ (B₀ + 1 + B₀ + 1) * (1 + ‖u‖) := by
      nlinarith [norm_nonneg u]
    calc (‖δ + z‖ + ‖lam‖) ^ 2 ≤ ((B₀ + 1 + B₀ + 1) * (1 + ‖u‖)) ^ 2 := by gcongr
      _ = _ := by ring
  have hc1 : 0 ≤ c₁ := le_max_left _ _
  have h1u : 1 ≤ (1 + ‖u‖) ^ 2 := by nlinarith [norm_nonneg u]
  calc Real.exp (-(c * (1 + ‖u‖) ^ 2))
      ≤ Real.exp (-(3 * Cη * (‖δ + z‖ + ‖lam‖) ^ 2)) * Real.exp (-c₁) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : 3 * Cη * (‖δ + z‖ + ‖lam‖) ^ 2 ≤ 3 * Cη * ((B₀ + 1 + B₀ + 1) ^ 2 * (1 + ‖u‖) ^ 2) := by
          gcongr
        simp only [c]
        nlinarith
    _ ≤ ‖sigmaMult L lam (δ + z)‖ ^ 3 * ‖ellV L (δ + z) i‖ := by
        rw [← hexp1]
        gcongr
        exact hlog.trans hδz

/-! ### The second argument of the addition law -/

lemma isRep_half : IsRep L (zh L) ![℘[L] (zh L), 0, 1] := by
  have := isRep_affine L (zh_notMem L)
  rwa [derivWp_zh] at this

lemma isRep_xi {c s : ℂ} (hs : zh L + c * s ∉ L.lattice) :
    IsRep L (zh L + c * s) ![wpP L c s, wpQ L c s, 1] := isRep_affine L hs

end LSG.Aux
