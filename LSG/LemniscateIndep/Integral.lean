/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The lemniscate constant and its integral

* `LSG.LemniscateIndep.varpi = Γ(1/4)² / (2 √(2π))`.
* `LSG.LemniscateIndep.lemInt t = 1 / √(1 - t⁴)`, and `varpi = 2 ∫₀¹ lemInt` (`varpi_eq_integral`),
  via the Beta integral `B(1/4, 1/2)` and the reflection formula.
* The primitive `lemF x = ∫₀ˣ lemInt` is continuous on `[0, 1]` and has derivative `lemInt x`
  on `(0, 1)`.
-/

noncomputable section

open MeasureTheory Set Real

namespace LSG.LemniscateIndep

/-- The real period `ϖ = Γ(1/4)² / (2 √(2π))` of the lattice `ϖ ℤ[i]`. -/
noncomputable def varpi : ℝ := Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt (2 * π))

/-- The lemniscate integrand `1 / √(1 - t⁴)`. -/
def lemInt (t : ℝ) : ℝ := 1 / Real.sqrt (1 - t ^ 4)

/-- The real Beta integrand at `(1/4, 1/2)`. -/
def betaInt (u : ℝ) : ℝ := u ^ (-(3 / 4 : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ))

lemma image_pow_four_Ioo : (fun t : ℝ => t ^ 4) '' Ioo 0 1 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨pow_pos ht.1 4, pow_lt_one₀ ht.1.le ht.2 (by norm_num)⟩
  · intro hu
    refine ⟨u ^ (1 / 4 : ℝ), ⟨Real.rpow_pos_of_pos hu.1 _,
      Real.rpow_lt_one hu.1.le hu.2 (by norm_num)⟩, ?_⟩
    dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.1.le]
    norm_num

/-- Substitution `u = t⁴`. -/
lemma setIntegral_betaInt :
    ∫ u in Ioo (0 : ℝ) 1, betaInt u = 4 * ∫ t in Ioo (0 : ℝ) 1, lemInt t := by
  have hinj : InjOn (fun t : ℝ => t ^ 4) (Ioo 0 1) := fun a ha b hb h =>
    (pow_left_inj₀ ha.1.le hb.1.le (by norm_num)).mp h
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t _ => (hasDerivAt_pow 4 t).hasDerivWithinAt) hinj betaInt
  rw [image_pow_four_Ioo] at h
  rw [h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  have h1 : 0 < 1 - t ^ 4 := sub_pos.2 (pow_lt_one₀ ht.1.le ht.2 (by norm_num))
  have hpow : (t ^ 4) ^ (-(3 / 4 : ℝ)) = (t ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_mul ht0.le,
      show ((4 : ℕ) : ℝ) * (-(3 / 4 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg ht0.le, Real.rpow_natCast]
  have hsq : (1 - t ^ 4) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 - t ^ 4))⁻¹ := by
    rw [Real.rpow_neg h1.le, Real.sqrt_eq_rpow]
  simp only [betaInt, smul_eq_mul, hpow, hsq, lemInt]
  rw [abs_of_pos (by positivity)]
  have : (t ^ 3) ≠ 0 := by positivity
  field_simp
  ring

/-- The complex Beta integral at `(1/4, 1/2)` is the real Beta integral. -/
lemma betaIntegral_quarter_half' :
    Complex.betaIntegral (1 / 4) (1 / 2) = ((∫ u in Ioo (0 : ℝ) 1, betaInt u : ℝ) : ℂ) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_ofReal, Complex.betaIntegral]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [uIcc_of_le zero_le_one] at hx
  simp only [betaInt, Complex.ofReal_mul]
  rw [Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (sub_nonneg.2 hx.2)]
  push_cast
  norm_num

/-- `2 ∫₀¹ dt / √(1 - t⁴) = Γ(1/4)² / (2 √(2π))`. -/
theorem varpi_eq_integral : varpi = 2 * ∫ t in (0 : ℝ)..1, lemInt t := by
  -- Beta–Gamma relation, transported to `ℝ`
  have hBG := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := 1 / 4) (t := 1 / 2) (by norm_num) (by norm_num)
  rw [betaIntegral_quarter_half', setIntegral_betaInt] at hBG
  have hc : ∀ x : ℝ, Complex.Gamma (x : ℂ) = (Real.Gamma x : ℂ) := Complex.Gamma_ofReal
  have hBG' : Real.Gamma (1 / 4) * Real.Gamma (1 / 2) =
      Real.Gamma (3 / 4) * (4 * ∫ t in Ioo (0 : ℝ) 1, lemInt t) := by
    have e1 : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; ring
    have e2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    have e3 : (1 / 4 + 1 / 2 : ℂ) = ((3 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e3, e1, e2, hc, hc, hc] at hBG
    exact_mod_cast hBG
  -- reflection and `Γ(1/2) = √π`
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / 4)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show π * (1 / 4) = π / 4 by ring,
    Real.sin_pi_div_four] at hrefl
  rw [Real.Gamma_one_half_eq] at hBG'
  have hI : ∫ t in (0 : ℝ)..1, lemInt t = ∫ t in Ioo (0 : ℝ) 1, lemInt t := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  set J := ∫ t in Ioo (0 : ℝ) 1, lemInt t
  set g1 := Real.Gamma (1 / 4)
  set g3 := Real.Gamma (3 / 4)
  have hs : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hq : 0 < √2 := by positivity
  have hq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have h2π : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num) π
  have hg3 : 0 < g3 := Real.Gamma_pos_of_pos (by norm_num)
  unfold varpi
  rw [hI, h2π]
  have hrefl' : g1 * g3 * √2 = 2 * π := by
    rw [hrefl]; field_simp
  rw [← hs2] at hrefl'
  have key : 2 * J * (2 * √2 * √π) * g3 = g1 ^ 2 * g3 := by
    have h4 : 4 * g3 * J = g1 * √π := by linarith [hBG']
    have hL : 2 * J * (2 * √2 * √π) * g3 * √2 = 2 * g1 * √π ^ 2 := by
      calc _ = (4 * g3 * J) * √π * √2 ^ 2 := by ring
        _ = _ := by rw [h4, hq2]; ring
    have hR : g1 ^ 2 * g3 * √2 = 2 * g1 * √π ^ 2 := by
      calc _ = g1 * (g1 * g3 * √2) := by ring
        _ = _ := by rw [hrefl']; ring
    exact mul_right_cancel₀ hq.ne' (hL.trans hR.symm)
  have hJ : 2 * J * (2 * √2 * √π) = g1 ^ 2 := mul_right_cancel₀ hg3.ne' key
  field_simp
  linarith [hJ]

lemma varpi_pos : 0 < varpi := by
  unfold varpi
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)
  positivity

/-- The lemniscate integrand is integrable on `[0, 1]` (its integral is `varpi / 2 ≠ 0`). -/
lemma intervalIntegrable_lemInt : IntervalIntegrable lemInt volume 0 1 := by
  by_contra h
  have h0 := intervalIntegral.integral_undef h
  have := varpi_eq_integral
  rw [h0] at this
  linarith [varpi_pos]

/-- The primitive `x ↦ ∫₀ˣ dt / √(1 - t⁴)`. -/
def lemF (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, lemInt t

lemma lemF_zero : lemF 0 = 0 := by simp [lemF]

lemma lemF_one : lemF 1 = varpi / 2 := by
  rw [lemF, varpi_eq_integral]; ring

lemma continuousOn_lemF : ContinuousOn lemF (Icc 0 1) := by
  have := intervalIntegral.continuousOn_primitive_interval' intervalIntegrable_lemInt
    (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
  rwa [uIcc_of_le zero_le_one] at this

lemma continuousOn_lemInt : ContinuousOn lemInt (Ioo 0 1) := by
  refine continuousOn_const.div (by fun_prop) (fun t ht => ?_)
  have : t ^ 4 < 1 := pow_lt_one₀ ht.1.le ht.2 (by norm_num)
  exact (Real.sqrt_pos.2 (by linarith)).ne'

lemma hasDerivAt_lemF {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt lemF (lemInt x) x := by
  have hint : IntervalIntegrable lemInt volume 0 x :=
    intervalIntegrable_lemInt.mono_set (by
      rw [uIcc_of_le hx.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hx.2.le)
  exact intervalIntegral.integral_hasDerivAt_right hint
    (continuousOn_lemInt.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (continuousOn_lemInt.continuousAt (isOpen_Ioo.mem_nhds hx))

end LSG.LemniscateIndep
