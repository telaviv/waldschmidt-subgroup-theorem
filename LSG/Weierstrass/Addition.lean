/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.Degree

/-!
# The addition theorem for `℘`

For `z, w, z + w ∉ Λ` with `℘(z) ≠ ℘(w)` (equivalently `z ± w ∉ Λ`), with
`m = (℘'(z) - ℘'(w)) / (℘(z) - ℘(w))`:

* `weierstrassP_add`: `℘(z + w) = -℘(z) - ℘(w) + m²/4`;
* `derivWeierstrassP_add`: `℘'(z + w) = -m (℘(z + w) - ℘(z)) - ℘'(z)`.

For `2z ∉ Λ` (then `℘'(z) ≠ 0`), with `℘''(z) = 6℘(z)² - g₂/2`:

* `weierstrassP_two_mul`: `℘(2z) = -2℘(z) + (℘''(z)/℘'(z))²/4`;
* `derivWeierstrassP_two_mul`: `℘'(2z) = -(℘''(z)/℘'(z)) (℘(2z) - ℘(z)) - ℘'(z)`.

## Proof
Generic case (`z, w, -(z+w)` pairwise incongruent and off `Λ`): the line `y = m x + ν` through
`(℘(z), ℘'(z))` and `(℘(w), ℘'(w))` gives the elliptic function `φ = ℘' - m℘ - ν`, and
`φ(t) σ(t)³ / (σ(t - z) σ(t - w) σ(t + z + w))` has at most a simple pole along `-(z+w) + Λ`; by
`eq_const_of_simple_pole` it is constant, which forces `φ(-(z+w)) = 0`. So `℘(z)`, `℘(w)`,
`℘(z+w)` are three distinct roots of `4X³ - g₂X - g₃ - (mX + ν)²`, and Vieta gives the sum.
The remaining cases follow by continuity in `w` (the exceptional `w` form a discrete set), and the
duplication formulas by letting `w → z`.
-/

open Module Filter Complex Set
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

/-- Vieta for three distinct roots of a cubic `4X³ + aX² + bX + c`. -/
lemma vieta_three {a b c x₁ x₂ x₃ : ℂ} (h₁ : 4 * x₁ ^ 3 + a * x₁ ^ 2 + b * x₁ + c = 0)
    (h₂ : 4 * x₂ ^ 3 + a * x₂ ^ 2 + b * x₂ + c = 0) (h₃ : 4 * x₃ ^ 3 + a * x₃ ^ 2 + b * x₃ + c = 0)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) : x₁ + x₂ + x₃ = -a / 4 := by
  have q12 : 4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + a * (x₁ + x₂) + b = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h12)
    linear_combination h₁ - h₂
  have q13 : 4 * (x₁ ^ 2 + x₁ * x₃ + x₃ ^ 2) + a * (x₁ + x₃) + b = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h13)
    linear_combination h₁ - h₃
  have : 4 * (x₁ + x₂ + x₃) + a = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h23)
    linear_combination q12 - q13
  linear_combination this / 4

lemma notMem_of_sub {x y : ℂ} (hx : x ∉ L.lattice) (hy : y ∈ L.lattice) : x - y ∉ L.lattice :=
  fun h => hx (by simpa using add_mem h hy)

section Generic

variable {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hzw : z + w ∉ L.lattice)
  (hd : z - w ∉ L.lattice) (h1 : 2 * z + w ∉ L.lattice) (h2 : z + 2 * w ∉ L.lattice)

/-- The slope of the chord through `(℘(z), ℘'(z))` and `(℘(w), ℘'(w))`. -/
def chordSlope (z w : ℂ) : ℂ := (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)

/-- The function `φ(t) = ℘'(t) - m ℘(t) - ν` of the chord. -/
def chordFun (z w t : ℂ) : ℂ :=
  ℘'[L] t - chordSlope L z w * ℘[L] t - (℘'[L] z - chordSlope L z w * ℘[L] z)

/-- `φ(t) σ(t)³ / (σ(t - z) σ(t - w) σ(t + (z + w)))`. -/
def addF (z w t : ℂ) : ℂ :=
  chordFun L z w t * sigma L t ^ 3 /
    (sigma L (t - z) * sigma L (t - w) * sigma L (t + (z + w)))

/-- The singular set of `addF`. -/
def addS (z w : ℂ) : Set ℂ :=
  {t | t ∈ L.lattice ∨ t - z ∈ L.lattice ∨ t - w ∈ L.lattice ∨ t + (z + w) ∈ L.lattice}

lemma discr_addS (z w : ℂ) : Discr (addS L z w) := by
  have h := (((discr_add L 0).union (discr_sub L z)).union (discr_sub L w)).union
    (discr_add L (z + w))
  convert h using 1
  ext u
  simp [addS, or_assoc]

lemma addS_add {t ω : ℂ} (ht : t ∈ addS L z w) (hω : ω ∈ L.lattice) : t + ω ∈ addS L z w := by
  rcases ht with h | h | h | h
  · exact Or.inl (add_mem h hω)
  · right; left; rw [show t + ω - z = (t - z) + ω by ring]; exact add_mem h hω
  · right; right; left; rw [show t + ω - w = (t - w) + ω by ring]; exact add_mem h hω
  · right; right; right; rw [show t + ω + (z + w) = (t + (z + w)) + ω by ring]; exact add_mem h hω

lemma chordFun_add (z w t : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) :
    chordFun L z w (t + ω) = chordFun L z w t := by
  unfold chordFun
  rw [weierstrassP_add_mem L t hω, derivWeierstrassP_add_mem L t hω]

lemma addF_add (z w t : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) : addF L z w (t + ω) = addF L z w t := by
  unfold addF
  rw [chordFun_add L z w t hω, sigma_add' L hω t, show t + ω - z = (t - z) + ω by ring,
    sigma_add' L hω (t - z), show t + ω - w = (t - w) + ω by ring, sigma_add' L hω (t - w),
    show t + ω + (z + w) = (t + (z + w)) + ω by ring, sigma_add' L hω (t + (z + w))]
  set s := sigmaSign L ω
  set e := eta L ω
  have hE : exp (e * (t - z + ω / 2)) * exp (e * (t - w + ω / 2)) *
      exp (e * (t + (z + w) + ω / 2)) =
      exp (e * (t + ω / 2)) * exp (e * (t + ω / 2)) * exp (e * (t + ω / 2)) := by
    simp only [← exp_add]
    congr 1
    ring
  have hK : s * s * s * (exp (e * (t + ω / 2)) * exp (e * (t + ω / 2)) *
      exp (e * (t + ω / 2))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (sigmaSign_ne_zero L ω) (sigmaSign_ne_zero L ω))
      (sigmaSign_ne_zero L ω)) (mul_ne_zero (mul_ne_zero (exp_ne_zero _) (exp_ne_zero _))
      (exp_ne_zero _))
  rw [show s * exp (e * (t - z + ω / 2)) * sigma L (t - z) *
      (s * exp (e * (t - w + ω / 2)) * sigma L (t - w)) *
      (s * exp (e * (t + (z + w) + ω / 2)) * sigma L (t + (z + w))) =
      sigma L (t - z) * sigma L (t - w) * sigma L (t + (z + w)) *
        (s * s * s * (exp (e * (t - z + ω / 2)) * exp (e * (t - w + ω / 2)) *
          exp (e * (t + (z + w) + ω / 2)))) by ring, hE,
    show chordFun L z w t * (s * exp (e * (t + ω / 2)) * sigma L t) ^ 3 =
      chordFun L z w t * sigma L t ^ 3 * (s * s * s * (exp (e * (t + ω / 2)) *
        exp (e * (t + ω / 2)) * exp (e * (t + ω / 2)))) by ring,
    mul_div_mul_right _ _ hK]

lemma differentiableAt_chordFun {t : ℂ} (ht : t ∉ L.lattice) :
    DifferentiableAt ℂ (chordFun L z w) t := by
  unfold chordFun
  exact ((differentiableAt_derivWeierstrassP L ht).sub
    ((differentiableAt_weierstrassP L ht).const_mul _)).sub_const _

lemma differentiableAt_addF {x : ℂ} (hx : x ∉ addS L z w) : DifferentiableAt ℂ (addF L z w) x := by
  have h0 : x ∉ L.lattice := fun h => hx (Or.inl h)
  have h1 : x - z ∉ L.lattice := fun h => hx (Or.inr (Or.inl h))
  have h2 : x - w ∉ L.lattice := fun h => hx (Or.inr (Or.inr (Or.inl h)))
  have h3 : x + (z + w) ∉ L.lattice := fun h => hx (Or.inr (Or.inr (Or.inr h)))
  have hs := differentiable_sigma L
  unfold addF
  refine DifferentiableAt.div ?_ ?_
    (mul_ne_zero (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2)) (sigma_ne_zero L h3))
  · exact (differentiableAt_chordFun L h0).mul ((hs x).pow 3)
  · exact (((hs _).comp x (differentiableAt_id.sub_const z)).mul
      ((hs _).comp x (differentiableAt_id.sub_const w))).mul
      ((hs _).comp x (differentiableAt_id.add_const (z + w)))

include hz hw hzw hd in
lemma pdiff_ne : ℘[L] z - ℘[L] w ≠ 0 := by
  intro h
  rw [sub_eq_zero, eq_comm] at h
  rcases (weierstrassP_eq_iff L hz hw).mp h with h' | h'
  · exact hd (by simpa using neg_mem h')
  · exact hzw (by rwa [add_comm] at h')

lemma chordFun_self : chordFun L z w z = 0 := by unfold chordFun; ring

include hz hw hzw hd in
lemma chordFun_right : chordFun L z w w = 0 := by
  have := pdiff_ne L hz hw hzw hd
  unfold chordFun chordSlope
  field_simp
  ring

include hz hw hzw in
lemma locBdd_addF_zero : LocBdd (addF L z w) 0 := by
  set m := chordSlope L z w
  set ν := ℘'[L] z - m * ℘[L] z
  have hz' : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
  have hw' : -w ∉ L.lattice := fun h => hw (by simpa using neg_mem h)
  set g : ℂ → ℂ := fun t => (t ^ 3 * L.derivWeierstrassPExcept 0 t - 2 -
      m * (t ^ 3 * L.weierstrassPExcept 0 t + t) - ν * t ^ 3) * sigmaProd L t ^ 3 /
    (sigma L (t - z) * sigma L (t - w) * sigma L (t + (z + w)))
  have hc : ContinuousAt g 0 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · refine ContinuousAt.mul ?_ ((continuous_sigmaProd L).continuousAt.pow 3)
      exact ((((continuousAt_id.pow 3).mul (continuousAt_derivWeierstrassPExcept_zero L)).sub
        continuousAt_const).sub (continuousAt_const.mul (((continuousAt_id.pow 3).mul
        (continuousAt_weierstrassPExcept_zero L)).add continuousAt_id))).sub
        (continuousAt_const.mul (continuousAt_id.pow 3))
    · exact (((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const))).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [zero_sub, zero_add]
      exact mul_ne_zero (mul_ne_zero (sigma_ne_zero L hz') (sigma_ne_zero L hw'))
        (sigma_ne_zero L hzw)
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  simp only [g, addF, chordFun, sigma_eq_mul_sigmaProd L t, weierstrassP_eq_except_zero L t,
    derivWeierstrassP_eq_except_zero L t]
  congr 1
  field_simp
  ring

include hz hd h1 in
lemma locBdd_addF_left : LocBdd (addF L z w) z := by
  set g : ℂ → ℂ := fun t => dslope (chordFun L z w) z t * sigma L t ^ 3 /
    (sigmaProd L (t - z) * sigma L (t - w) * sigma L (t + (z + w)))
  have hc : ContinuousAt g z := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_chordFun L hz)).mul
        ((continuous_sigma L).continuousAt.pow 3)
    · exact (((continuous_sigmaProd L).continuousAt.comp
        (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const))).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [sub_self, sigmaProd_zero, one_mul]
      refine mul_ne_zero (sigma_ne_zero L hd) (sigma_ne_zero L ?_)
      rwa [show z + (z + w) = 2 * z + w by ring]
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t - z ≠ 0 := sub_ne_zero.mpr ht
  simp only [g, addF, dslope_eq_div ht, chordFun_self, sub_zero, sigma_eq_mul_sigmaProd L (t - z)]
  field_simp

include hz hw hzw hd h2 in
lemma locBdd_addF_right : LocBdd (addF L z w) w := by
  set g : ℂ → ℂ := fun t => dslope (chordFun L z w) w t * sigma L t ^ 3 /
    (sigma L (t - z) * sigmaProd L (t - w) * sigma L (t + (z + w)))
  have hd' : w - z ∉ L.lattice := fun h => hd (by simpa using neg_mem h)
  have hc : ContinuousAt g w := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_chordFun L hw)).mul
        ((continuous_sigma L).continuousAt.pow 3)
    · exact (((continuous_sigma L).continuousAt.comp
        (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigmaProd L).continuousAt.comp (continuousAt_id.sub continuousAt_const))).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [sub_self, sigmaProd_zero, mul_one]
      refine mul_ne_zero (sigma_ne_zero L hd') (sigma_ne_zero L ?_)
      rwa [show w + (z + w) = z + 2 * w by ring]
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t - w ≠ 0 := sub_ne_zero.mpr ht
  simp only [g, addF, dslope_eq_div ht, chordFun_right L hz hw hzw hd, sub_zero,
    sigma_eq_mul_sigmaProd L (t - w)]
  field_simp

include hzw h1 h2 in
lemma locBdd_mul_addF_pole : LocBdd (fun t => (t - -(z + w)) * addF L z w t) (-(z + w)) := by
  have ha : -(z + w) ∉ L.lattice := fun h => hzw (by simpa using neg_mem h)
  set g : ℂ → ℂ := fun t => chordFun L z w t * sigma L t ^ 3 /
    (sigma L (t - z) * sigma L (t - w) * sigmaProd L (t + (z + w)))
  have hc : ContinuousAt g (-(z + w)) := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (differentiableAt_chordFun L ha).continuousAt.mul
        ((continuous_sigma L).continuousAt.pow 3)
    · exact (((continuous_sigma L).continuousAt.comp
        (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const))).mul
        ((continuous_sigmaProd L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [neg_add_cancel, sigmaProd_zero, mul_one]
      refine mul_ne_zero (sigma_ne_zero L ?_) (sigma_ne_zero L ?_)
      · intro h; apply h1; have := neg_mem h; rwa [show -(-(z + w) - z) = 2 * z + w by ring] at this
      · intro h; apply h2; have := neg_mem h; rwa [show -(-(z + w) - w) = z + 2 * w by ring] at this
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t + (z + w) ≠ 0 := by
    intro h; apply ht; simp only [mem_singleton_iff]; linear_combination h
  simp only [g, addF, sub_neg_eq_add, sigma_eq_mul_sigmaProd L (t + (z + w))]
  field_simp

include hz hw hzw hd h1 h2 in
/-- The third intersection point: `φ(-(z+w)) = 0`. -/
lemma chordFun_neg_add : chordFun L z w (-(z + w)) = 0 := by
  have hb : ∀ s ∈ addS L z w, s - -(z + w) ∉ L.lattice → LocBdd (addF L z w) s := by
    intro s hs hsa
    rcases hs with h | h | h | h
    · have := (locBdd_addF_zero L hz hw hzw).of_periodic (ω := s) (fun t => addF_add L z w t h)
      rwa [zero_add] at this
    · have := (locBdd_addF_left L hz hd h1).of_periodic (ω := s - z)
        (fun t => addF_add L z w t h)
      rwa [show z + (s - z) = s by ring] at this
    · have := (locBdd_addF_right L hz hw hzw hd h2).of_periodic (ω := s - w)
        (fun t => addF_add L z w t h)
      rwa [show w + (s - w) = s by ring] at this
    · exact absurd (by rwa [sub_neg_eq_add]) hsa
  obtain ⟨C, hC⟩ := eq_const_of_simple_pole L (-(z + w)) (discr_addS L z w)
    (fun u hu ω hω => addS_add L hu hω) (fun u _ ω hω => addF_add L z w u hω)
    (fun x hx => differentiableAt_addF L hx) hb (locBdd_mul_addF_pole L hzw h1 h2)
  have ha : -(z + w) ∉ L.lattice := fun h => hzw (by simpa using neg_mem h)
  have hs := continuous_sigma L
  have key := eq_of_eventuallyEq_nhdsNE
    (F₁ := fun t => C * (sigma L (t - z) * sigma L (t - w) * sigma L (t + (z + w))))
    (F₂ := fun t => chordFun L z w t * sigma L t ^ 3) (u := -(z + w)) (by fun_prop)
    ((differentiableAt_chordFun L ha).continuousAt.mul (hs.continuousAt.pow 3)) (by
      filter_upwards [discr_addS L z w (-(z + w))] with t ht
      have h1 : t - z ∉ L.lattice := fun h => ht (Or.inr (Or.inl h))
      have h2 : t - w ∉ L.lattice := fun h => ht (Or.inr (Or.inr (Or.inl h)))
      have h3 : t + (z + w) ∉ L.lattice := fun h => ht (Or.inr (Or.inr (Or.inr h)))
      have := hC t ht
      unfold addF at this
      rw [div_eq_iff (mul_ne_zero (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2))
        (sigma_ne_zero L h3))] at this
      exact this.symm)
  simp only [neg_add_cancel, sigma_zero, mul_zero] at key
  rcases mul_eq_zero.mp key.symm with h | h
  · exact h
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) (sigma_ne_zero L ha)

include hz hw hzw hd h1 h2 in
/-- The addition theorem, generic case. -/
lemma addition_generic :
    ℘[L] (z + w) = -℘[L] z - ℘[L] w + chordSlope L z w ^ 2 / 4 ∧
      ℘'[L] (z + w) = -chordSlope L z w * (℘[L] (z + w) - ℘[L] z) - ℘'[L] z := by
  have hφ := chordFun_neg_add L hz hw hzw hd h1 h2
  have hne := pdiff_ne L hz hw hzw hd
  set m := chordSlope L z w with hm
  set ν := ℘'[L] z - m * ℘[L] z with hν
  unfold chordFun at hφ
  rw [L.derivWeierstrassP_neg, L.weierstrassP_neg] at hφ
  rw [← hm] at hφ
  set x₁ := ℘[L] z
  set x₂ := ℘[L] w
  set x₃ := ℘[L] (z + w)
  have hy₃ : ℘'[L] (z + w) = -(m * x₃ + ν) := by linear_combination -hφ
  have hy₂ : ℘'[L] w = m * x₂ + ν := by
    have : m * (x₁ - x₂) = ℘'[L] z - ℘'[L] w := by
      rw [hm]
      show (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] z - ℘[L] w) = _
      exact div_mul_cancel₀ _ hne
    linear_combination this
  have c₁ := L.derivWeierstrassP_sq z hz
  have c₂ := L.derivWeierstrassP_sq w hw
  have c₃ := L.derivWeierstrassP_sq (z + w) hzw
  have e₁ : 4 * x₁ ^ 3 + (-m ^ 2) * x₁ ^ 2 + (-(L.g₂ + 2 * m * ν)) * x₁ + (-(L.g₃ + ν ^ 2)) = 0 := by
    linear_combination -c₁
  have e₂ : 4 * x₂ ^ 3 + (-m ^ 2) * x₂ ^ 2 + (-(L.g₂ + 2 * m * ν)) * x₂ + (-(L.g₃ + ν ^ 2)) = 0 := by
    linear_combination -c₂ + (℘'[L] w + m * x₂ + ν) * hy₂
  have e₃ : 4 * x₃ ^ 3 + (-m ^ 2) * x₃ ^ 2 + (-(L.g₂ + 2 * m * ν)) * x₃ + (-(L.g₃ + ν ^ 2)) = 0 := by
    linear_combination -c₃ + (℘'[L] (z + w) - m * x₃ - ν) * hy₃
  have d₁₂ : x₁ ≠ x₂ := sub_ne_zero.mp hne
  have d₁₃ : x₁ ≠ x₃ := by
    intro h
    rcases (weierstrassP_eq_iff L hz hzw).mp h.symm with h' | h'
    · exact hw (by rwa [show z + w - z = w by ring] at h')
    · exact h1 (by rwa [show z + w + z = 2 * z + w by ring] at h')
  have d₂₃ : x₂ ≠ x₃ := by
    intro h
    rcases (weierstrassP_eq_iff L hw hzw).mp h.symm with h' | h'
    · exact hz (by rwa [show z + w - w = z by ring] at h')
    · exact h2 (by rwa [show z + w + w = z + 2 * w by ring] at h')
  have hsum := vieta_three e₁ e₂ e₃ d₁₂ d₁₃ d₂₃
  refine ⟨by linear_combination hsum, ?_⟩
  rw [hy₃, hν]
  ring

end Generic

/-- Near any `w₀`, all `w ≠ w₀` avoid the five exceptional families. -/
lemma eventually_generic (z w₀ : ℂ) :
    ∀ᶠ w in 𝓝[≠] w₀, w ∉ L.lattice ∧ z + w ∉ L.lattice ∧ z - w ∉ L.lattice ∧
      2 * z + w ∉ L.lattice ∧ z + 2 * w ∉ L.lattice := by
  filter_upwards [discr_affine L one_ne_zero 0 w₀, discr_affine L one_ne_zero z w₀,
    discr_affine L (neg_ne_zero.mpr one_ne_zero) z w₀, discr_affine L one_ne_zero (2 * z) w₀,
    discr_affine L two_ne_zero z w₀] with w h₁ h₂ h₃ h₄ h₅
  simp only [one_mul, add_zero, neg_mul] at h₁ h₂ h₃ h₄ h₅
  refine ⟨h₁, by rwa [add_comm], by rwa [neg_add_eq_sub] at h₃, by rwa [add_comm],
    by rwa [add_comm]⟩

lemma continuousAt_chordSlope {z w : ℂ} (hw : w ∉ L.lattice) (hne : ℘[L] z - ℘[L] w ≠ 0) :
    ContinuousAt (fun v => chordSlope L z v) w := by
  unfold chordSlope
  exact (continuousAt_const.sub (continuousAt_derivWeierstrassP L hw)).div
    (continuousAt_const.sub (continuousAt_weierstrassP L hw)) hne

/-- **Addition theorem for `℘`.** -/
theorem weierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hd : z - w ∉ L.lattice) :
    ℘[L] (z + w) = -℘[L] z - ℘[L] w + chordSlope L z w ^ 2 / 4 := by
  refine eq_of_eventuallyEq_nhdsNE (F₁ := fun v => ℘[L] (z + v))
    (F₂ := fun v => -℘[L] z - ℘[L] v + chordSlope L z v ^ 2 / 4)
    ((continuousAt_weierstrassP L hzw).comp (continuousAt_const.add continuousAt_id))
    ((continuousAt_const.sub (continuousAt_weierstrassP L hw)).add
      (((continuousAt_chordSlope L hw (pdiff_ne L hz hw hzw hd)).pow 2).div_const _)) ?_
  filter_upwards [eventually_generic L z w] with v ⟨h₁, h₂, h₃, h₄, h₅⟩
  exact (addition_generic L hz h₁ h₂ h₃ h₄ h₅).1

/-- **Addition theorem for `℘'`.** -/
theorem derivWeierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hd : z - w ∉ L.lattice) :
    ℘'[L] (z + w) = -chordSlope L z w * (℘[L] (z + w) - ℘[L] z) - ℘'[L] z := by
  refine eq_of_eventuallyEq_nhdsNE (F₁ := fun v => ℘'[L] (z + v))
    (F₂ := fun v => -chordSlope L z v * (℘[L] (z + v) - ℘[L] z) - ℘'[L] z)
    ((continuousAt_derivWeierstrassP L hzw).comp (continuousAt_const.add continuousAt_id))
    (((continuousAt_chordSlope L hw (pdiff_ne L hz hw hzw hd)).neg.mul
      (((continuousAt_weierstrassP L hzw).comp (continuousAt_const.add continuousAt_id)).sub
      continuousAt_const)).sub continuousAt_const) ?_
  filter_upwards [eventually_generic L z w] with v ⟨h₁, h₂, h₃, h₄, h₅⟩
  exact (addition_generic L hz h₁ h₂ h₃ h₄ h₅).2

/-- The slope of the tangent: `℘''(z)/℘'(z)` with `℘'' = 6℘² - g₂/2`. -/
def tangentSlope (z : ℂ) : ℂ := (6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z

lemma notMem_of_two_mul_notMem {z : ℂ} (h2 : 2 * z ∉ L.lattice) : z ∉ L.lattice :=
  fun h => h2 (by simpa [two_mul] using add_mem h h)

lemma derivWeierstrassP_ne_zero {z : ℂ} (h2 : 2 * z ∉ L.lattice) : ℘'[L] z ≠ 0 := by
  rw [Ne, derivWeierstrassP_eq_zero_iff L (notMem_of_two_mul_notMem L h2)]
  exact h2

/-- The chord slope as a quotient of `dslope`s. -/
lemma chordSlope_eq_dslope {z v : ℂ} (hv : v ≠ z) (hne : ℘[L] z - ℘[L] v ≠ 0) :
    chordSlope L z v = dslope ℘'[L] z v / dslope ℘[L] z v := by
  rw [dslope_eq_div hv, dslope_eq_div hv]
  have hv' : v - z ≠ 0 := sub_ne_zero.mpr hv
  have hne' : ℘[L] v - ℘[L] z ≠ 0 := by
    intro h; apply hne; linear_combination -h
  unfold chordSlope
  field_simp
  ring

lemma continuousAt_slope_quot {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ContinuousAt (fun v => dslope ℘'[L] z v / dslope ℘[L] z v) z := by
  have hz := notMem_of_two_mul_notMem L h2
  refine ContinuousAt.div (continuousAt_dslope_same.mpr (differentiableAt_derivWeierstrassP L hz))
    (continuousAt_dslope_same.mpr (differentiableAt_weierstrassP L hz)) ?_
  rw [dslope_same, L.deriv_weierstrassP]
  exact derivWeierstrassP_ne_zero L h2

lemma slope_quot_self {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    dslope ℘'[L] z z / dslope ℘[L] z z = tangentSlope L z := by
  have hz := notMem_of_two_mul_notMem L h2
  rw [dslope_same, dslope_same, L.deriv_weierstrassP, (hasDerivAt_derivWeierstrassP L hz).deriv]
  rfl

/-- Near `z` (punctured), the addition theorem applies to `(z, v)`. -/
lemma eventually_near_self {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ∀ᶠ v in 𝓝[≠] z, v ∉ L.lattice ∧ z + v ∉ L.lattice ∧ z - v ∉ L.lattice ∧ v ≠ z := by
  have hz := notMem_of_two_mul_notMem L h2
  have e1 : ∀ᶠ v in 𝓝 z, v ∉ L.lattice := (isOpen_compl_lattice L).mem_nhds hz
  have e2 : ∀ᶠ v in 𝓝 z, v ∉ {u | 1 * u + z ∈ L.lattice} :=
    (discr_affine L one_ne_zero z).eventually_nhds (by simpa [two_mul] using h2)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2,
    discr_affine L (neg_ne_zero.mpr one_ne_zero) z z, self_mem_nhdsWithin] with v h₁ h₂ h₃ h₄
  simp only [one_mul, neg_mul] at h₂ h₃
  exact ⟨h₁, by rwa [add_comm], by rwa [neg_add_eq_sub] at h₃, h₄⟩

/-- **Duplication formula for `℘`.** -/
theorem weierstrassP_two_mul {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ℘[L] (2 * z) = -2 * ℘[L] z + tangentSlope L z ^ 2 / 4 := by
  have hz := notMem_of_two_mul_notMem L h2
  have h2' : z + z ∉ L.lattice := by rwa [← two_mul]
  have key := eq_of_eventuallyEq_nhdsNE (F₁ := fun v => ℘[L] (z + v))
    (F₂ := fun v => -℘[L] z - ℘[L] v + (dslope ℘'[L] z v / dslope ℘[L] z v) ^ 2 / 4) (u := z)
    ((continuousAt_weierstrassP L h2').comp (continuousAt_const.add continuousAt_id))
    ((continuousAt_const.sub (continuousAt_weierstrassP L hz)).add
      (((continuousAt_slope_quot L h2).pow 2).div_const _)) (by
      filter_upwards [eventually_near_self L h2] with v ⟨h₁, h₂, h₃, h₄⟩
      have hne := pdiff_ne L hz h₁ h₂ h₃
      rw [weierstrassP_add L hz h₁ h₂ h₃, chordSlope_eq_dslope L h₄ hne])
  simp only [slope_quot_self L h2] at key
  rw [two_mul, key]
  ring

/-- **Duplication formula for `℘'`.** -/
theorem derivWeierstrassP_two_mul {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ℘'[L] (2 * z) = -tangentSlope L z * (℘[L] (2 * z) - ℘[L] z) - ℘'[L] z := by
  have hz := notMem_of_two_mul_notMem L h2
  have h2' : z + z ∉ L.lattice := by rwa [← two_mul]
  have key := eq_of_eventuallyEq_nhdsNE (F₁ := fun v => ℘'[L] (z + v))
    (F₂ := fun v => -(dslope ℘'[L] z v / dslope ℘[L] z v) * (℘[L] (z + v) - ℘[L] z) - ℘'[L] z)
    (u := z)
    ((continuousAt_derivWeierstrassP L h2').comp (continuousAt_const.add continuousAt_id))
    ((((continuousAt_slope_quot L h2).neg.mul
      (((continuousAt_weierstrassP L h2').comp (continuousAt_const.add continuousAt_id)).sub
      continuousAt_const))).sub continuousAt_const) (by
      filter_upwards [eventually_near_self L h2] with v ⟨h₁, h₂, h₃, h₄⟩
      have hne := pdiff_ne L hz h₁ h₂ h₃
      rw [derivWeierstrassP_add L hz h₁ h₂ h₃, chordSlope_eq_dslope L h₄ hne])
  simp only [slope_quot_self L h2] at key
  rw [two_mul, key]

end LSG.Weierstrass
