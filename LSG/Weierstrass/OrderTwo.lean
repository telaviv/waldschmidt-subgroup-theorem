/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.SigmaGrowth

/-!
# `℘` and `℘'` as quotients of entire functions of order two

From `ζ = σ'/σ` and `ζ' = -℘` off the lattice:
* `℘ = (σ'² - σσ'')/σ² = σ(σ'² - σσ'')/σ³`,
* `℘' = -(2σ'³ - 3σσ'σ'' + σ²σ''')/σ³`.

Together with the order-two growth of `σ, σ', σ'', σ'''` this proves
`LSG.WeierstrassOrderTwo L` with `h = σ³`.
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

lemma differentiable_deriv_sigma : Differentiable ℂ (deriv (sigma L)) :=
  (differentiable_sigma L).deriv

lemma differentiable_deriv_deriv_sigma : Differentiable ℂ (deriv (deriv (sigma L))) :=
  (differentiable_sigma L).deriv.deriv

lemma differentiable_deriv_deriv_deriv_sigma :
    Differentiable ℂ (deriv (deriv (deriv (sigma L)))) :=
  (differentiable_sigma L).deriv.deriv.deriv

/-- `ζ = σ'/σ` in a neighbourhood of any non-lattice point. -/
lemma zeta_eventuallyEq {z : ℂ} (hz : z ∉ L.lattice) :
    zeta L =ᶠ[𝓝 z] fun w ↦ deriv (sigma L) w / sigma L w :=
  Filter.eventually_of_mem ((isOpen_compl_coe_lattice L).mem_nhds hz) fun w hw ↦ by
    change zeta L w = deriv (sigma L) w / sigma L w
    rw [deriv_sigma L hw, mul_div_cancel_right₀ _ (sigma_ne_zero L hw)]

/-- `℘ = (σ'² - σσ'')/σ²` off the lattice. -/
lemma weierstrassP_eq_sigma {z : ℂ} (hz : z ∉ L.lattice) :
    ℘[L] z = (deriv (sigma L) z * deriv (sigma L) z - sigma L z * deriv (deriv (sigma L)) z) /
      (sigma L z * sigma L z) := by
  have hs := sigma_ne_zero L hz
  have h0 := (differentiable_sigma L z).hasDerivAt
  have h1 := (differentiable_deriv_sigma L z).hasDerivAt
  have hq := (h1.div h0 hs).congr_of_eventuallyEq (zeta_eventuallyEq L hz)
  have := (hasDerivAt_zeta L hz).unique hq
  rw [neg_eq_iff_eq_neg] at this
  rw [this]
  field_simp
  ring

/-- `℘ = σ(σ'² - σσ'')/σ³` off the lattice. -/
lemma weierstrassP_eq_sigma_cube {z : ℂ} (hz : z ∉ L.lattice) :
    ℘[L] z = sigma L z * (deriv (sigma L) z ^ 2 - sigma L z * deriv (deriv (sigma L)) z) /
      sigma L z ^ 3 := by
  have hs := sigma_ne_zero L hz
  rw [weierstrassP_eq_sigma L hz]
  field_simp

/-- `℘' = -(2σ'³ - 3σσ'σ'' + σ²σ''')/σ³` off the lattice. -/
lemma derivWeierstrassP_eq_sigma_cube {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = -(2 * deriv (sigma L) z ^ 3 -
        3 * sigma L z * deriv (sigma L) z * deriv (deriv (sigma L)) z +
        sigma L z ^ 2 * deriv (deriv (deriv (sigma L))) z) / sigma L z ^ 3 := by
  have hs := sigma_ne_zero L hz
  have h0 := (differentiable_sigma L z).hasDerivAt
  have h1 := (differentiable_deriv_sigma L z).hasDerivAt
  have h2 := (differentiable_deriv_deriv_sigma L z).hasDerivAt
  have hq := ((h1.mul h1).sub (h0.mul h2)).div (h0.mul h0) (mul_ne_zero hs hs)
  have heq : ℘[L] =ᶠ[𝓝 z] fun w ↦ (deriv (sigma L) w * deriv (sigma L) w -
      sigma L w * deriv (deriv (sigma L)) w) / (sigma L w * sigma L w) :=
    Filter.eventually_of_mem ((isOpen_compl_coe_lattice L).mem_nhds hz) fun w hw ↦
      weierstrassP_eq_sigma L hw
  have hP := hq.congr_of_eventuallyEq heq
  rw [← L.deriv_weierstrassP, hP.deriv]
  simp only [Pi.mul_apply, Pi.sub_apply]
  field_simp
  ring

/-- **`℘` and `℘'` are quotients of entire functions of order `≤ 2`** with the common
denominator `σ³`, which vanishes exactly on the lattice. -/
theorem weierstrassOrderTwo : LSG.WeierstrassOrderTwo L := by
  set s0 := sigma L
  set s1 := deriv (sigma L)
  set s2 := deriv (deriv (sigma L))
  set s3 := deriv (deriv (deriv (sigma L)))
  have d0 : Differentiable ℂ s0 := differentiable_sigma L
  have d1 : Differentiable ℂ s1 := differentiable_deriv_sigma L
  have d2 : Differentiable ℂ s2 := differentiable_deriv_deriv_sigma L
  have d3 : Differentiable ℂ s3 := differentiable_deriv_deriv_deriv_sigma L
  have g0 : GrowthLE 2 s0 := growthLE_sigma L
  have g1 : GrowthLE 2 s1 := growthLE_deriv_sigma L
  have g2 : GrowthLE 2 s2 := growthLE_deriv_deriv_sigma L
  have g3 : GrowthLE 2 s3 := growthLE_deriv_deriv_deriv_sigma L
  refine ⟨fun z ↦ s0 z ^ 3, fun z ↦ s0 z * (s1 z ^ 2 - s0 z * s2 z),
    fun z ↦ -(2 * s1 z ^ 3 - 3 * s0 z * s1 z * s2 z + s0 z ^ 2 * s3 z),
    d0.pow 3, d0.mul ((d1.pow 2).sub (d0.mul d2)),
    ((((d1.pow 3).const_mul 2).sub (((d0.const_mul 3).mul d1).mul d2)).add
      ((d0.pow 2).mul d3)).neg, growthLE_pow g0 3, ?_, ?_, ?_, ?_⟩
  · exact growthLE_mul g0 (growthLE_sub (growthLE_pow g1 2) (growthLE_mul g0 g2))
  · refine growthLE_neg (growthLE_add (growthLE_sub (growthLE_const_mul 2 (growthLE_pow g1 3)) ?_)
      (growthLE_mul (growthLE_pow g0 2) g3))
    exact growthLE_congr (growthLE_const_mul 3 (growthLE_mul (growthLE_mul g0 g1) g2))
      fun z ↦ by ring
  · intro z
    rw [pow_eq_zero_iff (by norm_num)]
    exact sigma_eq_zero_iff L
  · intro z hz
    exact ⟨weierstrassP_eq_sigma_cube L hz, by rw [derivWeierstrassP_eq_sigma_cube L hz, neg_div]⟩

end LSG.Weierstrass
