/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The boundary integral of `1/z` over a rectangle centred at `0`

`LSG.Weierstrass.rectIntegral F z w` is the (counterclockwise) boundary integral of `F` over the
rectangle with opposite corners `z, w`, in the form used by Mathlib's Cauchy–Goursat theorem
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

* `LSG.Weierstrass.rectIntegral_inv`: for `a, b > 0`, the boundary integral of `z⁻¹` over
  `[-a, a] × [-b, b]` is `2πi`. Proof: explicit antiderivatives (branches of `log`) on the four
  sides, then `arg`-bookkeeping.
-/

open Complex MeasureTheory intervalIntegral Set
open scoped Real ComplexConjugate Interval

noncomputable section

namespace LSG.Weierstrass

/-- The counterclockwise boundary integral of `F` over the rectangle with corners `z`, `w`
(Mathlib's normalisation). -/
def rectIntegral (F : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))

/-- Cauchy–Goursat on a rectangle, in terms of `rectIntegral`. -/
lemma rectIntegral_eq_zero {F : ℂ → ℂ} {z w : ℂ}
    (H : DifferentiableOn ℂ F ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) : rectIntegral F z w = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w H

lemma intervalIntegrable_comp {F : ℂ → ℂ} {s t : ℝ} {g : ℝ → ℂ} (hg : Continuous g)
    (hF : ∀ x ∈ [[s, t]], ContinuousAt F (g x)) :
    IntervalIntegrable (fun x => F (g x)) volume s t :=
  ContinuousOn.intervalIntegrable fun x hx => ((hF x hx).comp hg.continuousAt).continuousWithinAt

/-- Additivity of `rectIntegral`, given continuity on the four sides. -/
lemma rectIntegral_add {F₁ F₂ : ℂ → ℂ} {z w : ℂ}
    (h₁ : ∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F₁ p)
    (h₂ : ∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F₂ p) :
    rectIntegral (fun p => F₁ p + F₂ p) z w = rectIntegral F₁ z w + rectIntegral F₂ z w := by
  have hz : z.im ∈ [[z.im, w.im]] := left_mem_uIcc
  have hw : w.im ∈ [[z.im, w.im]] := right_mem_uIcc
  have hz' : z.re ∈ [[z.re, w.re]] := left_mem_uIcc
  have hw' : w.re ∈ [[z.re, w.re]] := right_mem_uIcc
  have hor : ∀ (F : ℂ → ℂ), (∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F p) →
      ∀ c ∈ ({z.im, w.im} : Set ℝ),
      IntervalIntegrable (fun x : ℝ => F (x + c * I)) volume z.re w.re := by
    intro F hF c hc
    refine intervalIntegrable_comp (g := fun x : ℝ => (x : ℂ) + c * I) (by fun_prop) ?_
    intro x hx
    rcases hc with rfl | rfl
    · exact hF _ (by simp [mem_reProdIm, hx, hz]) (by simp)
    · exact hF _ (by simp [mem_reProdIm, hx, hw]) (by simp)
  have ver : ∀ (F : ℂ → ℂ), (∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F p) →
      ∀ c ∈ ({z.re, w.re} : Set ℝ),
      IntervalIntegrable (fun y : ℝ => F (c + y * I)) volume z.im w.im := by
    intro F hF c hc
    refine intervalIntegrable_comp (g := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop) ?_
    intro y hy
    rcases hc with rfl | rfl
    · exact hF _ (by simp [mem_reProdIm, hy, hz']) (by simp)
    · exact hF _ (by simp [mem_reProdIm, hy, hw']) (by simp)
  unfold rectIntegral
  rw [integral_add (hor F₁ h₁ _ (by simp)) (hor F₂ h₂ _ (by simp)),
    integral_add (hor F₁ h₁ _ (by simp)) (hor F₂ h₂ _ (by simp)),
    integral_add (ver F₁ h₁ _ (by simp)) (ver F₂ h₂ _ (by simp)),
    integral_add (ver F₁ h₁ _ (by simp)) (ver F₂ h₂ _ (by simp))]
  simp only [smul_add]
  ring

/-! ### Antiderivatives -/

lemma hasDerivAt_log_line {c d : ℂ} {x : ℝ} (h : c + x * d ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => log (c + t * d)) ((c + x * d)⁻¹ * d) x := by
  have h1 : HasDerivAt (fun w : ℂ => log (c + w * d)) ((c + x * d)⁻¹ * d) (x : ℂ) := by
    have := (hasDerivAt_log h).comp (x : ℂ) (((hasDerivAt_id (x : ℂ)).mul_const d).const_add c)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal

lemma integral_inv_line {c d : ℂ} {s t : ℝ} (hd : d ≠ 0)
    (h : ∀ x ∈ [[s, t]], c + x * d ∈ slitPlane) :
    ∫ x : ℝ in s..t, (c + x * d)⁻¹ = d⁻¹ * (log (c + t * d) - log (c + s * d)) := by
  have hcont : ∀ x ∈ [[s, t]], c + x * d ≠ 0 := fun x hx => slitPlane_ne_zero (h x hx)
  have := integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_log_line (h x hx))
    (ContinuousOn.intervalIntegrable (u := fun x : ℝ => (c + x * d)⁻¹ * d) (by
      refine ContinuousOn.mul ?_ continuousOn_const
      exact ContinuousOn.inv₀ (by fun_prop) hcont))
  rw [intervalIntegral.integral_mul_const] at this
  rw [← this, mul_comm _ d, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- The boundary integral of `z⁻¹` over `[-a, a] × [-b, b]` is `2πi`. -/
theorem rectIntegral_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    rectIntegral (fun z => z⁻¹) ⟨-a, -b⟩ ⟨a, b⟩ = 2 * π * I := by
  unfold rectIntegral
  simp only
  -- bottom and top: `c + x * 1` with `c = ± b i`
  have hB : ∫ x : ℝ in (-a)..a, ((x : ℂ) + ((-b : ℝ) : ℂ) * I)⁻¹ =
      log (((-b : ℝ) : ℂ) * I + a) - log (((-b : ℝ) : ℂ) * I + (-a : ℝ)) := by
    have := integral_inv_line (c := ((-b : ℝ) : ℂ) * I) (d := 1) (s := -a) (t := a) one_ne_zero
      (fun x _ => by rw [mem_slitPlane_iff]; right; simp; linarith)
    simpa [add_comm] using this
  have hT : ∫ x : ℝ in (-a)..a, ((x : ℂ) + (b : ℂ) * I)⁻¹ =
      log ((b : ℂ) * I + a) - log ((b : ℂ) * I + (-a : ℝ)) := by
    have := integral_inv_line (c := (b : ℂ) * I) (d := 1) (s := -a) (t := a) one_ne_zero
      (fun x _ => by rw [mem_slitPlane_iff]; right; simp; linarith)
    simpa [add_comm] using this
  have hR : ∫ y : ℝ in (-b)..b, ((a : ℂ) + y * I)⁻¹ =
      I⁻¹ * (log ((a : ℂ) + b * I) - log ((a : ℂ) + (-b : ℝ) * I)) :=
    integral_inv_line I_ne_zero (fun x _ => by rw [mem_slitPlane_iff]; left; simpa using ha)
  have hL : ∫ y : ℝ in (-b)..b, (((-a : ℝ) : ℂ) + y * I)⁻¹ =
      I⁻¹ * (log ((a : ℂ) + (-b : ℝ) * I) - log ((a : ℂ) + b * I)) := by
    have := integral_inv_line (c := (a : ℂ)) (d := -I) (s := -b) (t := b) (neg_ne_zero.mpr I_ne_zero)
      (fun x _ => by rw [mem_slitPlane_iff]; left; simpa using ha)
    have e : ∀ y : ℝ, (((-a : ℝ) : ℂ) + y * I)⁻¹ = -((a : ℂ) + y * -I)⁻¹ := by
      intro y; rw [← inv_neg]; congr 1; push_cast; ring
    simp_rw [e, intervalIntegral.integral_neg, this]
    push_cast
    rw [inv_neg]
    ring_nf
  rw [hB, hT, hR, hL]
  -- now the `arg` bookkeeping, with `p = a + b i`
  set p : ℂ := (a : ℂ) + b * I with hp
  have hpre : p.re = a := by simp [hp]
  have hpim : p.im = b := by simp [hp]
  have e1 : ((-b : ℝ) : ℂ) * I + a = conj p := by
    apply Complex.ext <;> simp [hp]
  have e2 : ((-b : ℝ) : ℂ) * I + (-a : ℝ) = -p := by
    apply Complex.ext <;> simp [hp]
  have e3 : (b : ℂ) * I + a = p := by rw [hp]; ring
  have e4 : (b : ℂ) * I + (-a : ℝ) = -conj p := by
    apply Complex.ext <;> simp [hp]
  have e5 : (a : ℂ) + (-b : ℝ) * I = conj p := by
    apply Complex.ext <;> simp [hp]
  rw [e1, e2, e3, e4, e5]
  have hargp : arg p ≠ π := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    linarith [this.2, hpim]
  have harg1 : arg (conj p) = -arg p := by rw [arg_conj, ite_eq_right_iff.mpr (fun h => absurd h hargp)]
  have harg2 : arg (-p) = arg p - π := arg_neg_eq_arg_sub_pi_of_im_pos (by rw [hpim]; exact hb)
  have harg3 : arg (-conj p) = -arg p + π := by
    rw [arg_neg_eq_arg_add_pi_of_im_neg (by simp [hpim, hb]), harg1]
  have hn1 : ‖conj p‖ = ‖p‖ := Complex.norm_conj p
  have hn2 : ‖-p‖ = ‖p‖ := norm_neg p
  have hn3 : ‖-conj p‖ = ‖p‖ := by rw [norm_neg, hn1]
  have key : log (-conj p) - log (-p) + log p - log (conj p) = 2 * π * I := by
    apply Complex.ext
    · simp only [sub_re, add_re, log_re, hn1, hn2, hn3]
      simp
    · simp only [sub_im, add_im, log_im, harg1, harg2, harg3]
      simp
      ring
  simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
  linear_combination key

end LSG.Weierstrass
