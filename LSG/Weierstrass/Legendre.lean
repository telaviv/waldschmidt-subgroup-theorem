/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.ZetaQuasiPeriod
import LSG.Weierstrass.RectInv
import LSG.Weierstrass.Basic

/-!
# Legendre's relation

For a period pair `L` with quasi-periods `η₁ = η(ω₁)`, `η₂ = η(ω₂)`:

  `η₁ ω₂ - η₂ ω₁ = 2πi`   if `Im (ω₂/ω₁) > 0`,   and `= -2πi` if `Im (ω₂/ω₁) < 0`.

(Mathlib's `PeriodPair` carries no orientation assumption.)

## Proof
Let `(α, β)` be a basis of `Λ` with `τ = β/α` in the upper half-plane. The function
`f(z) = α ζ(αz) - α η(α) z` is `1`-periodic, satisfies `f(z + τ) = f(z) + c` with
`c = α η(β) - η(α) β`, and `f(z) = G(z) + 1/z` with `G` holomorphic near the closed rectangle
`R = [-1/2, 1/2] × [-Im τ/2, Im τ/2]` (`G` is built from the `ζ`-series with the `0`-term removed).
On `∂R`: the vertical sides cancel by periodicity, and the top side is the bottom side shifted by
`τ` (up to a horizontal translation, harmless by periodicity), so `∮_{∂R} f = -c`. On the other hand
`∮ G = 0` (Cauchy–Goursat on a rectangle) and `∮ 1/z = 2πi` (`rectIntegral_inv`). Only rectangle
integrals appear; no residue theorem or parallelogram contour is needed.
-/

open Module Filter Complex MeasureTheory intervalIntegral Set
open scoped Topology Real Interval

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

lemma differentiableOn_zetaExcept (l₀ : L.lattice) :
    DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {(l₀ : ℂ)} : Set ℂ)ᶜ := by
  refine (hasSumLocallyUniformly_zetaExcept L l₀).tendstoLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) L.isOpen_compl_lattice_sdiff
  intro x hx
  split_ifs with hl
  · exact differentiableWithinAt_const _
  · have hxl : x - l ≠ 0 := by
      intro e
      have hxe : x = l := sub_eq_zero.mp e
      apply hx
      refine ⟨hxe ▸ l.2, ?_⟩
      rw [Set.mem_singleton_iff, hxe]
      exact fun h' ↦ hl (Subtype.ext h')
    exact (hasDerivAt_zetaSummand l x hxl).differentiableAt.differentiableWithinAt

lemma differentiableAt_zetaExcept_zero {w : ℂ} (hw : w ∉ L.lattice ∨ w = 0) :
    DifferentiableAt ℂ (zetaExcept L 0) w := by
  refine (differentiableOn_zetaExcept L 0 w ?_).differentiableAt
    (L.isOpen_compl_lattice_sdiff.mem_nhds ?_) <;>
  · rintro ⟨h1, h2⟩
    rcases hw with hw | hw
    · exact hw h1
    · exact h2 (by simp [hw])

/-- `ζ(w) = ζ₀(w) + 1/w` for every `w`, where `ζ₀` is the series without the `0`-term. -/
lemma zeta_eq_zetaExcept_zero_add (w : ℂ) : zeta L w = zetaExcept L 0 w + w⁻¹ := by
  rw [zeta_eq_zetaExcept_add L 0 w]
  simp [zetaSummand]

/-- **Legendre's relation** for a basis `(α, β)` of the lattice with `Im (β/α) > 0`. -/
theorem legendre_of_basis {α β : ℂ} (hα : α ∈ L.lattice) (hβ : β ∈ L.lattice)
    (hspan : ∀ l ∈ L.lattice, ∃ m n : ℤ, l = m * α + n * β) (him : 0 < (β / α).im) :
    eta L α * β - eta L β * α = 2 * π * I := by
  have hα0 : α ≠ 0 := by rintro rfl; simp at him
  set τ := β / α with hτ
  set b := τ.im / 2 with hb_def
  have hb : 0 < b := by positivity
  have hατ : α * τ = β := by rw [hτ]; field_simp
  set c := α * eta L β - eta L α * β with hc
  set f : ℂ → ℂ := fun z => α * zeta L (α * z) - α * eta L α * z with hf
  set G : ℂ → ℂ := fun z => α * zetaExcept L 0 (α * z) - α * eta L α * z with hG
  have hfG : f = fun z => G z + z⁻¹ := by
    funext z
    simp only [hf, hG]
    rw [zeta_eq_zetaExcept_zero_add, mul_inv, mul_add, mul_inv_cancel_left₀ hα0]
    ring
  have hf1 : ∀ z, f (z + 1) = f z := by
    intro z
    simp only [hf]
    rw [mul_add, mul_one, zeta_add L hα]
    ring
  have hfτ : ∀ z, f (z + τ) = f z + c := by
    intro z
    simp only [hf, hc]
    rw [mul_add, hατ, zeta_add L hβ, mul_add (α * eta L α), ← hατ]
    ring
  -- the lattice points `α z` with `z` in the closed rectangle
  have hmem : ∀ z : ℂ, α * z ∈ L.lattice → ∃ m n : ℤ, z = m + n * τ := by
    intro z hz
    obtain ⟨m, n, hmn⟩ := hspan _ hz
    refine ⟨m, n, ?_⟩
    rw [hτ]
    field_simp
    linear_combination hmn
  have hpole : ∀ z : ℂ, z.re ∈ Icc (-1/2 : ℝ) (1/2) → z.im ∈ Icc (-b) b →
      α * z ∈ L.lattice → z = 0 := by
    intro z hre him' hz
    obtain ⟨m, n, rfl⟩ := hmem z hz
    have hi : ((m : ℂ) + n * τ).im = n * (2 * b) := by
      simp only [add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add]
      rw [hb_def]; ring
    rw [hi] at him'
    have hn : n = 0 := by
      have h1 : (n : ℝ) * (2 * b) ≤ b := him'.2
      have h2 : -b ≤ (n : ℝ) * (2 * b) := him'.1
      have h3 : (n : ℝ) < 1 := by nlinarith
      have h4 : (-1 : ℝ) < n := by nlinarith
      have : n < 1 := by exact_mod_cast h3
      have : -1 < n := by exact_mod_cast h4
      omega
    subst hn
    have hr : ((m : ℂ) + ((0 : ℤ) : ℂ) * τ).re = m := by simp
    rw [hr] at hre
    have hm : m = 0 := by
      have h3 : (m : ℝ) < 1 := by linarith [hre.2]
      have h4 : (-1 : ℝ) < m := by linarith [hre.1]
      have : m < 1 := by exact_mod_cast h3
      have : -1 < m := by exact_mod_cast h4
      omega
    subst hm
    simp
  -- the horizontal lines `Im z = ± b` avoid the poles
  have hline : ∀ z : ℂ, (z.im = -b ∨ z.im = b) → α * z ∉ L.lattice := by
    intro z hz hzm
    obtain ⟨m, n, rfl⟩ := hmem z hzm
    have hi : ((m : ℂ) + n * τ).im = n * (2 * b) := by
      simp only [add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add]
      rw [hb_def]; ring
    rw [hi] at hz
    rcases hz with hz | hz
    · have : (n : ℝ) * 2 = -1 := by nlinarith
      have : n * 2 = -1 := by exact_mod_cast this
      omega
    · have : (n : ℝ) * 2 = 1 := by nlinarith
      have : n * 2 = 1 := by exact_mod_cast this
      omega
  have hfcont : ∀ z : ℂ, α * z ∉ L.lattice → ContinuousAt f z := by
    intro z hz
    have h1 : DifferentiableAt ℂ (zeta L) (α * z) :=
      (differentiableOn_zeta L _ hz).differentiableAt ((isOpen_compl_coe_lattice L).mem_nhds hz)
    have : DifferentiableAt ℂ f z := by
      simp only [hf]
      fun_prop
    exact this.continuousAt
  -- `G` is holomorphic on the closed rectangle
  set z₀ : ℂ := ⟨-1/2, -b⟩
  set w₀ : ℂ := ⟨1/2, b⟩
  have hrect : ∀ p ∈ [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]],
      p.re ∈ Icc (-1/2 : ℝ) (1/2) ∧ p.im ∈ Icc (-b) b := by
    intro p hp
    rw [mem_reProdIm] at hp
    simp only [z₀, w₀] at hp
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by linarith)] at hp
    exact hp
  have hGd : ∀ p ∈ [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]], DifferentiableAt ℂ G p := by
    intro p hp
    obtain ⟨h1, h2⟩ := hrect p hp
    have hz : α * p ∉ L.lattice ∨ α * p = 0 := by
      by_cases h : α * p ∈ L.lattice
      · right; rw [hpole p h1 h2 h, mul_zero]
      · left; exact h
    have := differentiableAt_zetaExcept_zero L hz
    simp only [hG]
    fun_prop
  have hGzero : rectIntegral G z₀ w₀ = 0 :=
    rectIntegral_eq_zero fun p hp => (hGd p hp).differentiableWithinAt
  -- `1/z` on the boundary
  have hinv : rectIntegral (fun z => z⁻¹) z₀ w₀ = 2 * π * I := by
    have := rectIntegral_inv (a := 1/2) (b := b) (by norm_num) hb
    convert this using 2
    simp [z₀]
    norm_num
  have hbd_ne : ∀ p ∈ [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]],
      (p.re = z₀.re ∨ p.re = w₀.re ∨ p.im = z₀.im ∨ p.im = w₀.im) → p ≠ 0 := by
    rintro p - h rfl
    simp only [zero_re, zero_im, z₀, w₀] at h
    rcases h with h | h | h | h <;> linarith
  have hsplit : rectIntegral f z₀ w₀ = 2 * π * I := by
    rw [hfG, rectIntegral_add (fun p hp _ => (hGd p hp).continuousAt)
      (fun p hp hb' => continuousAt_inv₀ (hbd_ne p hp hb')), hGzero, hinv, zero_add]
  -- periodicity computation of the boundary integral of `f`
  have hver : (∫ y : ℝ in z₀.im..w₀.im, f (w₀.re + y * I)) =
      ∫ y : ℝ in z₀.im..w₀.im, f (z₀.re + y * I) := by
    refine integral_congr fun y _ => ?_
    rw [← hf1 ((z₀.re : ℂ) + y * I)]
    congr 1
    simp only [z₀, w₀]
    push_cast
    ring
  set g : ℝ → ℂ := fun x => f (x + z₀.im * I) with hg
  have hgper : Function.Periodic g 1 := by
    intro x
    simp only [hg]
    rw [← hf1 ((x : ℂ) + z₀.im * I)]
    congr 1
    push_cast
    ring
  have hgcont : Continuous g := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have : ContinuousAt f ((x : ℂ) + z₀.im * I) :=
      hfcont _ (hline _ (Or.inl (by simp [z₀])))
    exact this.comp (g := f) (f := fun x : ℝ => (x : ℂ) + z₀.im * I) (by fun_prop)
  have htop : (∫ x : ℝ in z₀.re..w₀.re, f (x + w₀.im * I)) =
      (∫ x : ℝ in z₀.re..w₀.re, f (x + z₀.im * I)) + c := by
    have e : ∀ x : ℝ, f (x + w₀.im * I) = g (x - τ.re) + c := by
      intro x
      simp only [hg]
      rw [← hfτ]
      congr 1
      apply Complex.ext
      · simp [z₀, w₀, hb_def]
      · simp [z₀, w₀, hb_def]
        ring
    simp_rw [e]
    have hint : IntervalIntegrable (fun x => g (x - τ.re)) volume z₀.re w₀.re :=
      (hgcont.comp (continuous_sub_right τ.re)).intervalIntegrable _ _
    rw [integral_add hint _root_.intervalIntegrable_const, integral_comp_sub_right, intervalIntegral.integral_const]
    have hw : w₀.re - τ.re = (z₀.re - τ.re) + 1 := by simp [z₀, w₀]; ring
    have hw' : w₀.re = z₀.re + 1 := by simp [z₀, w₀]; norm_num
    rw [hw, hgper.intervalIntegral_add_eq (z₀.re - τ.re) z₀.re, ← hw']
    have h1 : w₀.re - z₀.re = 1 := by simp [z₀, w₀]; norm_num
    rw [h1, one_smul]
  have hper : rectIntegral f z₀ w₀ = -c := by
    unfold rectIntegral
    rw [hver, htop]
    ring
  rw [hper] at hsplit
  rw [hc] at hsplit
  linear_combination hsplit

lemma im_div_ne_zero : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro h
  have h1 := ω₁_ne_zero L
  set t := (L.ω₂ / L.ω₁).re
  have ht : L.ω₂ / L.ω₁ = (t : ℂ) := Complex.ext (by simp [t]) (by simp [h])
  have hω : L.ω₂ = t * L.ω₁ := by rw [← ht]; field_simp
  have := LinearIndependent.pair_iff.mp L.indep t (-1) (by
    simp only [Complex.real_smul, hω]; push_cast; ring)
  norm_num at this

/-- **Legendre's relation**, positively oriented case. -/
theorem legendre_of_im_pos (h : 0 < (L.ω₂ / L.ω₁).im) :
    eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ = 2 * π * I :=
  legendre_of_basis L L.ω₁_mem_lattice L.ω₂_mem_lattice
    (fun l hl => by obtain ⟨m, n, h⟩ := mem_lattice.mp hl; exact ⟨m, n, h.symm⟩) h

/-- **Legendre's relation**, negatively oriented case. -/
theorem legendre_of_im_neg (h : (L.ω₂ / L.ω₁).im < 0) :
    eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ = -(2 * π * I) := by
  have h' : 0 < (L.ω₁ / L.ω₂).im := by
    have : L.ω₁ / L.ω₂ = (L.ω₂ / L.ω₁)⁻¹ := by rw [inv_div]
    rw [this, inv_im, neg_div]
    apply neg_pos.mpr
    apply div_neg_of_neg_of_pos h
    rw [normSq_pos]
    intro h0
    rw [h0] at h
    simp at h
  have := legendre_of_basis L L.ω₂_mem_lattice L.ω₁_mem_lattice
    (fun l hl => by
      obtain ⟨m, n, h⟩ := mem_lattice.mp hl
      exact ⟨n, m, by rw [← h]; ring⟩) h'
  linear_combination -this

/-- **Legendre's relation**: `η₁ ω₂ - η₂ ω₁ = ±2πi`, with sign `+` iff `Im (ω₂/ω₁) > 0`. -/
theorem legendre :
    eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ =
      2 * π * I * (if 0 < (L.ω₂ / L.ω₁).im then 1 else -1) := by
  split_ifs with h
  · rw [mul_one]; exact legendre_of_im_pos L h
  · rw [legendre_of_im_neg L (lt_of_le_of_ne (not_lt.mp h) (im_div_ne_zero L))]
    ring

lemma legendre_ne_zero : eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ ≠ 0 := by
  rw [legendre]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  split_ifs <;> simp [hπ, I_ne_zero]

end LSG.Weierstrass
