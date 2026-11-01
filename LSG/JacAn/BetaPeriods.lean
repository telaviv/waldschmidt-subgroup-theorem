/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The Beta periods of `y² = 4x⁵ + 1` (ABVAR §1.2, §1.3, A0.1)

The curve `C₅ : y⁵ = x(1 − x)` becomes the Baker–Grant model `Y² = 4X⁵ + 1` under `X = −y`, `Y = 2x − 1`. Its
cycle `γ = ℓ − [ζ]ℓ` (ABVAR §1.2: `ℓ` the lift of `x ∈ [0,1]` with `y = (x(1−x))^{1/5} ≥ 0`, `[ζ](x,y) = (x, ζy)`)
is, in the model,

* `liftPath e : t ↦ (−ζ^e ρ(t), 2t − 1)`, `ρ(t) = (t(1−t))^{1/5}`, a `Path (0, −1) (0, 1)` on the curve
  (`liftPath_mem_curve`);
* `cycleE e = liftPath e ⬝ (liftPath (e+1))⁻¹`, a loop at `(0, −1)`; `cycleE 0 = γ`, `cycleE e = [ζ^e]γ`.

With Mathlib's `curveIntegral` and the forms `ω_j = X^j dX / Y` (`omegaJ j`):

* `curveIntegral_cycleE`: `∫_{[ζ^e]γ} X^j dX/Y = ((−1)^j/5) ((ζ^e)^{j+1} − (ζ^{e+1})^{j+1}) B((j+1)/5, (j+1)/5)`;
* `period_omega0`, `period_omega1`: `∫_γ dX/Y = perA5 0 / 5`, `∫_γ X dX/Y = −perA5 1 / 5`;
* `period_omega3`: `∫_γ X³ dX/Y = −perB5 / 5` (the second-kind period `P̄` of ABVAR §1.3).

`zetaN`, `betaG`, `perA5`, `perB5` are verbatim copies of lean_mstar's (`AbVar/ThmA.lean`, `ThmAn.lean`,
`Fermat7.lean`); lean_lsg may not import lean_mstar. In the model `dX/Y = (1/5) dx/y⁴`, `X dX/Y = −(1/5) dx/y³` and
`X³ dX/Y = −(1/5) dx/y` on `C₅`, which explains the factors.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology intervalIntegral

namespace LSG.JacAn.Beta

/-! ## Copies of the lean_mstar definitions -/

/-- `ζ_N = e^{2πi/N}` (copy of lean_mstar `CM4E.AbVar.zetaN`). -/
def zetaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / N)

lemma zetaN_prim (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (zetaN N) N := by
  simpa [zetaN] using Complex.isPrimitiveRoot_exp N hN

/-- `B(a, b) = Γ(a)Γ(b)/Γ(a + b)` (copy of lean_mstar `betaG`). -/
def betaG (a b : ℂ) : ℂ := Gamma a * Gamma b / Gamma (a + b)

lemma betaG_eq_betaIntegral {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    betaG a b = betaIntegral a b := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  have hne : Gamma (a + b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [betaG, h]; field_simp

/-- The eigen-periods `P s = (1 − ζ₅^{s+1}) B((s+1)/5, (s+1)/5)` (copy of lean_mstar `perA5`). -/
def perA5 (s : Fin 2) : ℂ :=
  (1 - zetaN 5 ^ ((s : ℕ) + 1)) * betaG ((((s : ℕ) + 1 : ℕ) : ℂ) / 5) ((((s : ℕ) + 1 : ℕ) : ℂ) / 5)

/-- The second-kind period `P̄ = (1 − ζ₅⁴) B(4/5, 4/5)` (copy of lean_mstar `perB5`). -/
def perB5 : ℂ := (1 - zetaN 5 ^ 4) * betaG (4 / 5) (4 / 5)

/-! ## The lifts -/

/-- `ρ(t) = (t(1 − t))^{1/5}`. -/
def rho (t : ℝ) : ℝ := (t * (1 - t)) ^ (1 / 5 : ℝ)

lemma continuous_rho : Continuous rho :=
  (Real.continuous_rpow_const (by norm_num)).comp (continuous_id.mul (continuous_const.sub continuous_id))

lemma rho_pow_five {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : rho t ^ 5 = t * (1 - t) := by
  rw [rho, ← Real.rpow_natCast, ← Real.rpow_mul (mul_nonneg h0 (by linarith))]; norm_num

/-- The lift `[ζ^e]ℓ` in the model `Y² = 4X⁵ + 1`: `t ↦ (−ζ^e ρ(t), 2t − 1)`. -/
def liftFun (e : ℕ) (t : ℝ) : ℂ × ℂ := (-(zetaN 5 ^ e) * (rho t : ℂ), 2 * (t : ℂ) - 1)

lemma continuous_liftFun (e : ℕ) : Continuous (liftFun e) :=
  (continuous_const.mul (continuous_ofReal.comp continuous_rho)).prodMk
    ((continuous_const.mul continuous_ofReal).sub continuous_const)

/-- `[ζ^e]ℓ` as a `Path (0, −1) (0, 1)`. -/
def liftPath (e : ℕ) : Path ((0 : ℂ), (-1 : ℂ)) ((0 : ℂ), (1 : ℂ)) where
  toFun t := liftFun e t
  continuous_toFun := (continuous_liftFun e).comp continuous_subtype_val
  source' := by simp [liftFun, rho]
  target' := by norm_num [liftFun, rho]

/-- The lifts lie on `Y² = 4X⁵ + 1`. -/
theorem liftPath_mem_curve (e : ℕ) (t : unitInterval) :
    (liftPath e t).2 ^ 2 = 4 * (liftPath e t).1 ^ 5 + 1 := by
  change (liftFun e t).2 ^ 2 = 4 * (liftFun e t).1 ^ 5 + 1
  have hz : zetaN 5 ^ 5 = 1 := (zetaN_prim 5 (by norm_num)).pow_eq_one
  have hr : ((rho t : ℝ) : ℂ) ^ 5 = (t : ℂ) * (1 - t) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) (rho_pow_five t.2.1 t.2.2)
    push_cast at this; exact this
  have : (-(zetaN 5 ^ e) * (rho t : ℂ)) ^ 5 = -((zetaN 5 ^ 5) ^ e * (rho t : ℂ) ^ 5) := by ring
  simp only [liftFun]
  rw [this, hz, one_pow, one_mul, hr]; ring

/-- The closed path `[ζ^e]γ = [ζ^e]ℓ − [ζ^{e+1}]ℓ`, a loop at `(0, −1)`. -/
def cycleE (e : ℕ) : Path ((0 : ℂ), (-1 : ℂ)) ((0 : ℂ), (-1 : ℂ)) :=
  (liftPath e).trans (liftPath (e + 1)).symm

/-! ## Derivatives -/

lemma hasDerivAt_rho {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt rho ((1 - 2 * t) * (1 / 5) * (t * (1 - t)) ^ ((1 / 5 : ℝ) - 1)) t := by
  have hf : HasDerivAt (fun y : ℝ => y * (1 - y)) (1 - 2 * t) t := by
    have := (hasDerivAt_id' t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id' t))
    convert this using 1; simp only [Pi.sub_apply]; ring
  exact hf.rpow_const (Or.inl (mul_pos h0 (by linarith)).ne')

lemma hasDerivAt_liftFun (e : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt (liftFun e)
      (-(zetaN 5 ^ e) * (((1 - 2 * t) * (1 / 5) * (t * (1 - t)) ^ ((1 / 5 : ℝ) - 1) : ℝ) : ℂ), (2 : ℂ))
      t := by
  have h1' := ((hasDerivAt_rho h0 h1).ofReal_comp).const_mul (-(zetaN 5 ^ e))
  have h2 : HasDerivAt (fun y : ℝ => 2 * (y : ℂ) - 1) 2 t := by
    have := ((hasDerivAt_id t).ofReal_comp.const_mul (2 : ℂ)).sub_const 1
    simpa using this
  exact h1'.prodMk h2

/-! ## The forms and the integrand -/

/-- The form `ω_j = X^j dX / Y` on `ℂ × ℂ ∋ (X, Y)`. -/
def omegaJ (j : ℕ) (p : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] ℂ := (p.1 ^ j / p.2) • ContinuousLinearMap.fst ℂ ℂ ℂ

/-- The constant `(−1)^j (ζ^e)^{j+1} / 5`. -/
def cst (e j : ℕ) : ℂ := (-1) ^ j * (zetaN 5 ^ e) ^ (j + 1) / 5

/-- The Beta integrand `(t(1 − t))^{(j+1)/5 − 1}`. -/
def betaFun (j : ℕ) (t : ℝ) : ℂ := (((t * (1 - t)) ^ (((j : ℝ) + 1) / 5 - 1) : ℝ) : ℂ)

lemma rho_pow_mul {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (j : ℕ) :
    rho t ^ j * (t * (1 - t)) ^ ((1 / 5 : ℝ) - 1) = (t * (1 - t)) ^ (((j : ℝ) + 1) / 5 - 1) := by
  have hp : 0 < t * (1 - t) := mul_pos h0 (by linarith)
  rw [rho, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_add hp]; congr 1; ring

lemma curveIntegralFun_liftPath (e j : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (hne : t ≠ 1 / 2) :
    curveIntegralFun (omegaJ j) (liftPath e) t = cst e j * betaFun j t := by
  have hev : (liftPath e).extend =ᶠ[𝓝 t] liftFun e := by
    filter_upwards [Ioo_mem_nhds h0 h1] with s hs
    rw [Path.extend_apply _ (Ioo_subset_Icc_self hs)]; rfl
  have hd : derivWithin (liftPath e).extend unitInterval t =
      (-(zetaN 5 ^ e) * (((1 - 2 * t) * (1 / 5) * (t * (1 - t)) ^ ((1 / 5 : ℝ) - 1) : ℝ) : ℂ), (2 : ℂ)) := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds h0 h1), hev.deriv_eq, (hasDerivAt_liftFun e h0 h1).deriv]
  rw [curveIntegralFun_def, hd, hev.eq_of_nhds]
  have hQ : betaFun j t = ((rho t : ℝ) : ℂ) ^ j * (((t * (1 - t)) ^ ((1 / 5 : ℝ) - 1) : ℝ) : ℂ) := by
    rw [betaFun, ← rho_pow_mul h0 h1 j]; push_cast; ring
  have h2 : (2 * (t : ℂ) - 1) ≠ 0 := by
    intro h
    apply hne
    have : (2 * t - 1 : ℝ) = 0 := by exact_mod_cast h
    linarith
  rw [hQ]
  simp only [omegaJ, liftFun, cst, smul_apply, ContinuousLinearMap.coe_fst',
    smul_eq_mul]
  push_cast
  field_simp
  ring

/-! ## The integrals -/

lemma ae_uIoc_of_Ioo {f g : ℝ → ℂ} (h : ∀ t, 0 < t → t < 1 → t ≠ 1 / 2 → f t = g t) :
    ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → f t = g t := by
  have hc : ({1 / 2, 1} : Set ℝ).Countable := (countable_singleton _).insert _
  filter_upwards [hc.ae_notMem volume] with t ht hmem
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
  rw [uIoc_of_le zero_le_one] at hmem
  exact h t hmem.1 (lt_of_le_of_ne hmem.2 ht.2) ht.1

lemma betaFun_eq_aux (j : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    betaFun j t = (t : ℂ) ^ (((j : ℂ) + 1) / 5 - 1) * (1 - (t : ℂ)) ^ (((j : ℂ) + 1) / 5 - 1) := by
  rw [betaFun, Real.mul_rpow h0.le (by linarith), Complex.ofReal_mul, Complex.ofReal_cpow h0.le,
    Complex.ofReal_cpow (by linarith)]
  push_cast; ring_nf

lemma integral_betaFun (j : ℕ) :
    ∫ t in (0 : ℝ)..1, betaFun j t = betaIntegral (((j : ℂ) + 1) / 5) (((j : ℂ) + 1) / 5) := by
  rw [betaIntegral]
  exact intervalIntegral.integral_congr_ae (ae_uIoc_of_Ioo fun t h0 h1 _ => betaFun_eq_aux j h0 h1)

lemma intervalIntegrable_betaFun (j : ℕ) : IntervalIntegrable (betaFun j) volume 0 1 := by
  have hre : 0 < (((j : ℂ) + 1) / 5).re := by
    rw [show ((j : ℂ) + 1) / 5 = (((j : ℝ) + 1) / 5 : ℝ) by push_cast; ring, Complex.ofReal_re]
    positivity
  refine (Complex.betaIntegral_convergent hre hre).congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  exact ae_uIoc_of_Ioo fun t h0 h1 _ => (betaFun_eq_aux j h0 h1).symm

lemma curveIntegrable_liftPath (e j : ℕ) : CurveIntegrable (omegaJ j) (liftPath e) := by
  refine ((intervalIntegrable_betaFun j).const_mul (cst e j)).congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  exact ae_uIoc_of_Ioo fun t h0 h1 hne => (curveIntegralFun_liftPath e j h0 h1 hne).symm

/-- `∫_{[ζ^e]ℓ} X^j dX/Y = ((−1)^j/5) (ζ^e)^{j+1} B((j+1)/5, (j+1)/5)`. -/
theorem curveIntegral_liftPath (e j : ℕ) :
    ∫ᶜ p in liftPath e, omegaJ j p = cst e j * betaIntegral (((j : ℂ) + 1) / 5) (((j : ℂ) + 1) / 5) := by
  rw [curveIntegral_def, ← integral_betaFun, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr_ae
    (ae_uIoc_of_Ioo fun t h0 h1 hne => curveIntegralFun_liftPath e j h0 h1 hne)

/-- **The periods of `[ζ^e]γ`.** -/
theorem curveIntegral_cycleE (e j : ℕ) :
    ∫ᶜ p in cycleE e, omegaJ j p =
      (-1) ^ j / 5 * ((zetaN 5 ^ e) ^ (j + 1) - (zetaN 5 ^ (e + 1)) ^ (j + 1)) *
        betaIntegral (((j : ℂ) + 1) / 5) (((j : ℂ) + 1) / 5) := by
  rw [cycleE, curveIntegral_trans (curveIntegrable_liftPath e j)
    (curveIntegrable_liftPath (e + 1) j).symm, curveIntegral_symm, curveIntegral_liftPath,
    curveIntegral_liftPath, cst, cst]
  ring

/-- `∫_γ X^j dX/Y = ((−1)^j/5) (1 − ζ^{j+1}) B((j+1)/5, (j+1)/5)`. -/
theorem curveIntegral_cycle (j : ℕ) :
    ∫ᶜ p in cycleE 0, omegaJ j p =
      (-1) ^ j / 5 * (1 - zetaN 5 ^ (j + 1)) * betaIntegral (((j : ℂ) + 1) / 5) (((j : ℂ) + 1) / 5) := by
  rw [curveIntegral_cycleE]; simp

lemma betaG_eq (j : ℕ) :
    betaG (((j : ℂ) + 1) / 5) (((j : ℂ) + 1) / 5) = betaIntegral (((j : ℂ) + 1) / 5) (((j : ℂ) + 1) / 5) := by
  have hre : 0 < (((j : ℂ) + 1) / 5).re := by
    rw [show ((j : ℂ) + 1) / 5 = (((j : ℝ) + 1) / 5 : ℝ) by push_cast; ring, Complex.ofReal_re]
    positivity
  exact betaG_eq_betaIntegral hre hre

/-- **`z₀(γ) = perA5 0 / 5`** (`dX/Y = (1/5) dx/y⁴`). -/
theorem period_omega0 : ∫ᶜ p in cycleE 0, omegaJ 0 p = perA5 0 / 5 := by
  have h := betaG_eq 0
  rw [curveIntegral_cycle, perA5]
  norm_num at h ⊢
  rw [h]; ring

/-- **`z₁(γ) = −perA5 1 / 5`** (`X dX/Y = −(1/5) dx/y³`). -/
theorem period_omega1 : ∫ᶜ p in cycleE 0, omegaJ 1 p = -perA5 1 / 5 := by
  have h := betaG_eq 1
  rw [curveIntegral_cycle, perA5]
  norm_num at h ⊢
  rw [h]; ring

/-- **`∫_γ X³ dX/Y = −perB5 / 5`** (`X³ dX/Y = −(1/5) dx/y`, the second-kind period `P̄`). -/
theorem period_omega3 : ∫ᶜ p in cycleE 0, omegaJ 3 p = -perB5 / 5 := by
  have h := betaG_eq 3
  rw [curveIntegral_cycle, perB5]
  norm_num at h ⊢
  rw [h]; ring

end LSG.JacAn.Beta
