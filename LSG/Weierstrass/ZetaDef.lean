/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The Weierstrass `ζ` function

For a period pair `L` we define the Weierstrass zeta function as the lattice sum
`ζ(z) = 1/z + Σ'_{ω ≠ 0} (1/(z - ω) + 1/ω + z/ω²)`.

In Lean the term for `ω = 0` is `1/(z - 0) + 1/0 + z/0² = 1/z` (junk value `1/0 = 0`), so we can
sum over the whole lattice.

## Main results
* `LSG.Weierstrass.hasSumLocallyUniformly_zeta`: the series converges locally uniformly on `ℂ`.
* `LSG.Weierstrass.differentiableOn_zeta`: `ζ` is holomorphic off the lattice.
* `LSG.Weierstrass.hasDerivAt_zeta`: `ζ' = -℘` off the lattice.
* `LSG.Weierstrass.zeta_neg`: `ζ` is odd.
-/

open Module Filter
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

/-- The summand of the Weierstrass `ζ` series: `1/(z - l) + 1/l + z/l²`. For `l = 0` it equals
`1/z`. -/
def zetaSummand (l z : ℂ) : ℂ := 1 / (z - l) + 1 / l + z / l ^ 2

lemma zetaSummand_eq (l z : ℂ) (hl : l ≠ 0) (hz : z ≠ l) :
    zetaSummand l z = z ^ 2 / (l ^ 2 * (z - l)) := by
  have : z - l ≠ 0 := sub_ne_zero.mpr hz
  unfold zetaSummand
  field_simp
  ring

/-- Bound on the summands for `‖z‖ < r ≤ ‖l‖/2`. -/
lemma zetaSummand_bound (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < r) (l : ℂ)
    (h : 2 * r ≤ ‖l‖) : ‖zetaSummand l z‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hl : l ≠ 0 := norm_pos_iff.mp hl0
  have hzl : z ≠ l := by rintro rfl; linarith
  have hzl' : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]
    have := norm_sub_norm_le l z
    linarith
  rw [zetaSummand_eq l z hl hzl, Real.rpow_neg hl0.le, norm_div, norm_mul, norm_pow, norm_pow]
  have h3 : ‖l‖ ^ (3 : ℝ) = ‖l‖ ^ 3 := by norm_cast
  rw [h3, div_le_iff₀ (mul_pos (by positivity) (by linarith))]
  have hz2 : ‖z‖ ^ 2 ≤ r ^ 2 := by gcongr
  calc ‖z‖ ^ 2 ≤ r ^ 2 := hz2
    _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ * (‖l‖ ^ 2 * (‖l‖ / 2)) := by field_simp
    _ ≤ 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ * (‖l‖ ^ 2 * ‖z - l‖) := by gcongr

/-- The Weierstrass `ζ` function `ζ(z) = 1/z + Σ'_{ω ≠ 0} (1/(z - ω) + 1/ω + z/ω²)`. -/
def zeta (z : ℂ) : ℂ := ∑' l : L.lattice, zetaSummand l z

lemma hasSumLocallyUniformly_zeta :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ zetaSummand l z) (zeta L) := by
  refine PeriodPair.hasSumLocallyUniformly_aux L (u := fun r l ↦ 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ)) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  exact zetaSummand_bound r hr s hs l h

lemma hasSum_zeta (z : ℂ) : HasSum (fun l : L.lattice ↦ zetaSummand l z) (zeta L z) :=
  (hasSumLocallyUniformly_zeta L).hasSum

lemma summable_zetaSummand (z : ℂ) : Summable (fun l : L.lattice ↦ zetaSummand l z) :=
  (hasSum_zeta L z).summable

lemma isOpen_compl_coe_lattice : IsOpen (L.latticeᶜ : Set ℂ) :=
  L.isClosed_lattice.isOpen_compl

lemma hasDerivAt_zetaSummand (l x : ℂ) (hxl : x - l ≠ 0) :
    HasDerivAt (zetaSummand l) (-(1 / (x - l) ^ 2 - 1 / l ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℂ ↦ y - l) 1 x := (hasDerivAt_id x).sub_const _
  have h2 : HasDerivAt (fun y : ℂ ↦ 1 / (y - l)) (-(1 : ℂ) / (x - l) ^ 2) x := by
    have := h1.inv hxl
    simp only [one_div]
    convert this using 1
  have h3 : HasDerivAt (fun y : ℂ ↦ y / l ^ 2) (1 / l ^ 2) x :=
    (hasDerivAt_id x).div_const _
  have h4 : HasDerivAt (fun y ↦ 1 / (y - l) + 1 / l + y / l ^ 2)
      (-(1 : ℂ) / (x - l) ^ 2 + 0 + 1 / l ^ 2) x :=
    (h2.add (hasDerivAt_const x (1 / l))).add h3
  have : zetaSummand l = fun y ↦ 1 / (y - l) + 1 / l + y / l ^ 2 := rfl
  rw [this]
  convert h4 using 1
  ring

lemma sub_coe_ne_zero {x : ℂ} (hx : x ∉ L.lattice) (l : L.lattice) : x - l ≠ 0 :=
  fun e ↦ hx (by rw [sub_eq_zero.mp e]; exact l.2)

lemma differentiableOn_zetaSummand (l : L.lattice) :
    DifferentiableOn ℂ (zetaSummand l) L.latticeᶜ := fun x hx ↦
  (hasDerivAt_zetaSummand l x (sub_coe_ne_zero L hx l)).differentiableAt.differentiableWithinAt

lemma deriv_zetaSummand (l : L.lattice) (x : ℂ) (hx : x ∉ L.lattice) :
    deriv (zetaSummand l) x = -(1 / (x - l) ^ 2 - 1 / (l : ℂ) ^ 2) :=
  (hasDerivAt_zetaSummand l x (sub_coe_ne_zero L hx l)).deriv

/-- `ζ` is holomorphic off the lattice. -/
lemma differentiableOn_zeta : DifferentiableOn ℂ (zeta L) L.latticeᶜ := by
  refine (hasSumLocallyUniformly_zeta L).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun i _ ↦ differentiableOn_zetaSummand L i)
    (isOpen_compl_coe_lattice L)

lemma hasSumLocallyUniformly_neg_weierstrassP :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ -(1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
      (fun z ↦ -℘[L] z) := by
  have := PeriodPair.hasSumLocallyUniformly_aux L
    (fun (l : L.lattice) (z : ℂ) ↦ -(1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
    (u := fun r l ↦ 10 * r * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, by
      rintro _ h s hs l rfl
      rw [norm_neg]
      exact PeriodPair.weierstrassP_bound r hr s hs l h⟩
  convert this using 2 with z
  rw [tsum_neg, PeriodPair.weierstrassP]

/-- `ζ' = -℘` off the lattice. -/
lemma eqOn_deriv_zeta : Set.EqOn (deriv (zeta L)) (fun z ↦ -℘[L] z) L.latticeᶜ := by
  refine ((hasSumLocallyUniformly_zeta L).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ ?_) (isOpen_compl_coe_lattice L)).unique ?_
  · exact .fun_sum fun i _ ↦ differentiableOn_zetaSummand L i
  · have := (hasSumLocallyUniformly_neg_weierstrassP L).tendstoLocallyUniformlyOn
      (s := L.latticeᶜ)
    refine this.congr ?_
    intro s x hx
    simp only [Function.comp_apply]
    rw [deriv_fun_sum (fun i _ ↦ (differentiableOn_zetaSummand L i x hx).differentiableAt
      ((isOpen_compl_coe_lattice L).mem_nhds hx))]
    exact Finset.sum_congr rfl fun i _ ↦ (deriv_zetaSummand L i x hx).symm

/-- `ζ' = -℘` off the lattice. -/
lemma hasDerivAt_zeta {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt (zeta L) (-℘[L] z) z := by
  have hd : DifferentiableAt ℂ (zeta L) z :=
    (differentiableOn_zeta L z hz).differentiableAt ((isOpen_compl_coe_lattice L).mem_nhds hz)
  have := hd.hasDerivAt
  rwa [eqOn_deriv_zeta L hz] at this

lemma zetaSummand_neg (l z : ℂ) : zetaSummand (-l) (-z) = -zetaSummand l z := by
  unfold zetaSummand
  have h1 : -z - -l = -(z - l) := by ring
  rw [h1]
  simp only [one_div, inv_neg, neg_sq, neg_div]
  ring

/-- `ζ` is odd. -/
lemma zeta_neg (z : ℂ) : zeta L (-z) = -zeta L z := by
  calc zeta L (-z) = ∑' l : L.lattice, zetaSummand ((Equiv.neg L.lattice l : L.lattice) : ℂ) (-z) :=
        ((Equiv.neg L.lattice).tsum_eq (fun l : L.lattice ↦ zetaSummand (l : ℂ) (-z))).symm
    _ = ∑' l : L.lattice, -zetaSummand (l : ℂ) z := by
        congr 1 with l
        simp only [Equiv.neg_apply, NegMemClass.coe_neg, zetaSummand_neg]
    _ = -zeta L z := tsum_neg

end LSG.Weierstrass
