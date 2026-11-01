/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlock.ABlockInst
import LSG.AuxFunA.LemmaUFac
import LSG.JacAn3.TaylorFields

/-!
# A5.8: the analytic and Taylor packages of the A-block

* **`aBlockAnD D : AbBlockAn (aBlockD D)`** (and `aBlockAn : AbBlockAn aBlock`): `lat = latt`
  (`latt_le_kerE`, `isNsmulIn_latt_kerE`); growth from `thetaN_order2`; quasi-periodicity from `thetaN_add`,
  `fac_affine`, `norm_facN` with `κ_ω = facN ω 0`, `L_ω = Lf ω`, `c_Q = ‖Lext‖`.
* **`aBlockTayD D ι : AbBlockTay (aBlockD D) ι`** for every number field `K` and `ι : K →+* ℂ`: `ks_chart4F` at
  `z₀ = 0`, where `θ(0) ∥ e₄`, so the initial values `normalize 4 θ(0)` are `0, 1` (`A = E = 1`); `c_B = 81·2·W4H/W4den`,
  `δ = W4den`. The ratio `θ_N(sv)_l/θ_N(sv)_4` is `normalize 4 (θ(sv)) l`.
* **`tayAll_aBlock`**: the `TayAll` form of STAGE_A5 §6.1 for `B = fun _ => aBlock` (the data are rational).
-/

noncomputable section

open LSG.JacAn LSG.Jac LSG.AuxA LSG.Aux

namespace LSG.JacBlock

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad a1Facts hp hx} (D : ThetaData G)

/-! ### The analytic package -/

lemma growth_ex : ∃ cW : ℝ, 0 ≤ cW ∧ ∀ z, ‖D.thetaN z‖ ≤ Real.exp (cW * (1 + ‖z‖) ^ 2) := by
  obtain ⟨a, C, h⟩ := D.thetaN_order2
  refine ⟨max a 0 + max C 0, by positivity, fun z => (h z).trans (Real.exp_le_exp.mpr ?_)⟩
  have hz := norm_nonneg z
  have h1 : ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := by nlinarith
  have h2 : 1 ≤ (1 + ‖z‖) ^ 2 := by nlinarith
  have ha : a * ‖z‖ ^ 2 ≤ max a 0 * (1 + ‖z‖) ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_max_left a 0) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h1 (le_max_right a 0))
  have hC : C ≤ max C 0 * (1 + ‖z‖) ^ 2 :=
    (le_max_left C 0).trans (le_mul_of_one_le_right (le_max_right C 0) h2)
  nlinarith

lemma qp_ex : ∃ cQ : ℝ, 0 ≤ cQ ∧ ∀ ω ∈ latt, ∃ (κ : ℂ) (L : (Fin 2 → ℂ) →ₗ[ℂ] ℂ), κ ≠ 0 ∧
    ‖κ‖ ≤ Real.exp (cQ * ‖ω‖ ^ 2) ∧ ‖κ‖⁻¹ ≤ Real.exp (cQ * ‖ω‖ ^ 2) ∧ (∀ z, ‖L z‖ ≤ cQ * ‖ω‖ * ‖z‖) ∧
    ∀ z, D.thetaN (z + ω) = (κ * Complex.exp (L z)) • D.thetaN z := by
  set T := LinearMap.toContinuousLinearMap D.Lext
  have hT := norm_nonneg T
  refine ⟨‖T‖, hT, fun ω hω => ?_⟩
  have hL : D.Lf ω = T ω := by rw [← (D.ext_agree hω).1]; rfl
  have hn : ‖D.facN ω 0‖ = Real.exp ((D.Lf ω ω).re / 2) := by
    rw [D.norm_facN hω 0, map_zero, Complex.zero_re, add_zero]
  have hre : |(D.Lf ω ω).re| ≤ ‖T‖ * ‖ω‖ ^ 2 := by
    rw [hL]
    refine (Complex.abs_re_le_norm _).trans (((T ω).le_opNorm ω).trans ?_)
    rw [sq, ← mul_assoc]; gcongr; exact T.le_opNorm ω
  refine ⟨D.facN ω 0, (D.Lf ω : (Fin 2 → ℂ) →ₗ[ℂ] ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← norm_pos_iff, hn]; exact Real.exp_pos _
  · rw [hn]; apply Real.exp_le_exp.mpr
    have := (abs_le.mp hre).2
    nlinarith [mul_nonneg hT (sq_nonneg ‖ω‖)]
  · rw [hn, ← Real.exp_neg]; apply Real.exp_le_exp.mpr
    have := (abs_le.mp hre).1
    nlinarith [mul_nonneg hT (sq_nonneg ‖ω‖)]
  · intro z
    change ‖D.Lf ω z‖ ≤ _
    rw [hL]
    exact ((T ω).le_opNorm z).trans (by gcongr; exact T.le_opNorm ω)
  · intro z
    rw [D.thetaN_add (isPer_of_mem_latt hω) z]
    congr 1
    change D.facN ω z = D.facN ω 0 * Complex.exp (D.Lf ω z)
    simp only [ThetaData.facN]
    rw [D.fac_affine (isPer_of_mem_latt hω) z]
    ring

/-- **The analytic package of the A-block** (any `θ`-datum). -/
def aBlockAnD : AbBlockAn (aBlockD D) where
  lat := latt
  lat_le := LSG.W88.latt_le_kerE G
  lat_nsmul := LSG.W88.isNsmulIn_latt_kerE G
  cW := (growth_ex D).choose
  cW_nonneg := (growth_ex D).choose_spec.1
  growth := (growth_ex D).choose_spec.2
  cQ := (qp_ex D).choose
  cQ_nonneg := (qp_ex D).choose_spec.1
  qp := (qp_ex D).choose_spec.2

/-- **The analytic package of `aBlock`.** -/
def aBlockAn : AbBlockAn aBlock := aBlockAnD stdPkg.D

/-! ### The Taylor package -/

lemma ratio_eq_normalize (z : Fin 2 → ℂ) (l : Fin 9) :
    D.thetaN z l / D.thetaN z 4 = normalize 4 (D.theta z) l := by
  simp only [ThetaData.thetaN, Pi.smul_apply, smul_eq_mul, JacAn.normalize]
  rw [mul_div_mul_left _ _ (Complex.exp_ne_zero _), div_eq_inv_mul]

/-- The constant `c_B`. -/
def cBA : ℝ := 81 * (2 * ((a1Facts.W4H : ℝ) / a1Facts.W4den))

lemma cBA_eq : cBA = 1296 := by
  simp only [cBA, show a1Facts.W4H = 32 from rfl, show a1Facts.W4den = 4 from rfl]; norm_num

variable (K : Type*) [Field K] [NumberField K] (ι : K →+* ℂ)

/-- **The Taylor package of the A-block** over any number field. -/
def aBlockTayD : AbBlockTay (aBlockD D) ι where
  A := 1
  one_le_A := le_rfl
  cB := cBA
  one_le_cB := by rw [cBA_eq]; norm_num
  E := 1
  one_le_E := le_rfl
  δ := a1Facts.W4den
  one_le_δ := a1Facts.W4den_pos
  ks v Hc dc hHc hv j := by
    obtain ⟨a, ha, h0⟩ := D.theta_zero
    have hz : D.theta 0 4 ≠ 0 := by rw [h0]; simpa [origin9] using ha
    have hn : ∀ l, Sz ι 1 1 (normalize 4 (D.theta 0) l) := by
      intro l
      rw [h0]
      by_cases hl : l = 4
      · subst hl; simpa [JacAn.normalize, origin9, ha] using Sz.one (ι := ι)
      · simpa [JacAn.normalize, origin9, Pi.single_apply, hl] using (Sz.zero (ι := ι) 1).mono_le zero_le_one
    have hB1 : 1 ≤ cBA * Hc := by
      rw [cBA_eq]; nlinarith
    have h := D.ks_chart4F (z₀ := 0) (c := v) hz hv (A' := 1) (B := cBA * Hc) (E := 1) hn le_rfl hB1
      (by unfold cBA; nlinarith [le_refl Hc]) (![1, 8] j)
    rw [mul_one] at h
    convert h using 2 with s
    rw [zero_add]
    exact ratio_eq_normalize D (s • v) (![1, 8] j)

/-- **The Taylor package of `aBlock`.** -/
def aBlockTay : AbBlockTay aBlock ι := aBlockTayD stdPkg.D K ι

/-- **`TayAll` for `B = fun _ => aBlock`** (STAGE_A5 §6.1): Taylor packages over every number field. -/
def tayAll_aBlock (m : ℕ) :
    ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (k : Fin m), AbBlockTay ((fun _ => aBlock) k) ι :=
  fun K _ _ ι _ => aBlockTay K ι

end LSG.JacBlock
