import Mathlib
import LSG.ME.SubgroupLie

/-!
# Surjectivity of the exponential maps

* **`exists_weierstrassP_eq`**: `℘` takes every value off the lattice (otherwise `1/(℘ − x)`,
  extended by `0` on `Λ`, is an entire `Λ`-periodic function, hence constant by Liouville, but it
  vanishes on `Λ` and not elsewhere).
* **`expE_surjective`**: `expE : ℂ → E(ℂ)` is onto (the sign of `y` via `z ↦ −z`).
* **`expG_surjective`**: `expG : Tan → G(ℂ)` is onto.

Needed to transfer statements about all points of a Zariski-closed subgroup `H` to its analytic
preimage (e.g. surjectivity of `(π_L, π_{J₂})` in the Hilbert lower bound, and the translation
argument for Zariski tangent spaces).
-/

open Filter Topology Set LSG.Weierstrass

namespace LSG.ME

/-- **`℘` takes every value.** -/
theorem exists_weierstrassP_eq (L : PeriodPair) (x : ℂ) :
    ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = x := by
  classical
  by_contra hne
  push Not at hne
  let f : ℂ → ℂ := fun z => if z ∈ L.lattice then 0 else (L.weierstrassP z - x)⁻¹
  have hdiff : Differentiable ℂ f := by
    intro z₀
    by_cases h₀ : z₀ ∈ L.lattice
    · -- near a lattice point: `(z − z₀)² / (1 + (z − z₀)² (℘Exc z − 1/z₀² − x))`
      set A : ℂ → ℂ := fun z => L.weierstrassPExcept z₀ z - 1 / z₀ ^ 2 - x
      let g : ℂ → ℂ := fun z => (z - z₀) ^ 2 / (1 + (z - z₀) ^ 2 * A z)
      have hA : AnalyticAt ℂ A z₀ :=
        ((L.analyticAt_weierstrassPExcept z₀).sub analyticAt_const).sub analyticAt_const
      have hden : AnalyticAt ℂ (fun z => 1 + (z - z₀) ^ 2 * A z) z₀ := by
        have : AnalyticAt ℂ (fun z : ℂ => z - z₀) z₀ := analyticAt_id.sub analyticAt_const
        exact analyticAt_const.add ((this.pow 2).mul hA)
      have hg : AnalyticAt ℂ g z₀ :=
        ((analyticAt_id.sub analyticAt_const).pow 2).div hden (by simp)
      refine hg.differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z₀] with z hz
      by_cases hzz : z = z₀
      · subst hzz; simp [f, g, h₀]
      · have hzL : z ∉ L.lattice := fun h => hz ⟨h, hzz⟩
        have hw : z - z₀ ≠ 0 := sub_ne_zero.mpr hzz
        have e1 := L.weierstrassPExcept_def ⟨z₀, h₀⟩ z
        simp only at e1
        have hpx : L.weierstrassP z - x ≠ 0 := sub_ne_zero.mpr (hne z hzL)
        have hden' : 1 + (z - z₀) ^ 2 * A z ≠ 0 := by
          intro h
          apply hpx
          have : L.weierstrassP z - x = (1 + (z - z₀) ^ 2 * A z) / (z - z₀) ^ 2 := by
            simp only [A, e1]; field_simp; ring
          rw [this, h, zero_div]
        simp only [f, g, hzL, ite_false]
        rw [eq_div_iff hden']
        simp only [A, e1]
        field_simp
        ring
    · have hd : DifferentiableAt ℂ (fun z => (L.weierstrassP z - x)⁻¹) z₀ :=
        ((L.differentiableOn_weierstrassP.differentiableAt
          (L.isClosed_lattice.isOpen_compl.mem_nhds h₀)).sub_const x).inv
          (sub_ne_zero.mpr (hne z₀ h₀))
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds h₀] with z hz
      simp [f, show z ∉ L.lattice from hz]
  have hper : ∀ z w, w ∈ L.lattice → f (z + w) = f z := by
    intro z w hw
    have hmem : z + w ∈ L.lattice ↔ z ∈ L.lattice := L.lattice.add_mem_iff_left hw
    have hp : L.weierstrassP (z + w) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨w, hw⟩
    simp only [f, hmem, hp]
  have hbd := (IsZLattice.isCompact_range_of_periodic L.lattice f hdiff.continuous hper).isBounded
  have hz := hdiff.apply_eq_apply_of_bounded hbd (L.ω₁ / 2) 0
  have h1 : f (L.ω₁ / 2) ≠ 0 := by
    simp only [f, L.ω₁_div_two_notMem_lattice, ite_false]
    exact inv_ne_zero (sub_ne_zero.mpr (hne _ L.ω₁_div_two_notMem_lattice))
  exact h1 (hz.trans (by simp [f, L.lattice.zero_mem]))

/-- **`expE` is onto.** -/
theorem expE_surjective (L : PeriodPair) : Function.Surjective (expE L) := by
  intro P
  cases P with
  | zero => exact ⟨0, expE_zero L⟩
  | some x y h =>
    obtain ⟨z, hz, hzx⟩ := exists_weierstrassP_eq L x
    -- `(℘'(z)/2)² = y²`
    have hy : (L.derivWeierstrassP z / 2) ^ 2 = y ^ 2 := by
      have e1 := (equation_weierstrassP L hz)
      have e2 := h.1
      rw [WeierstrassCurve.Affine.equation_iff] at e1 e2
      simp only [curveA, curve, zero_mul, add_zero] at e1 e2
      rw [hzx] at e1
      linear_combination e1 - e2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h' | h'
    · exact ⟨z, by rw [expE_of_notMem L hz]; exact some_eq_some L hzx h'⟩
    · have hz' : -z ∉ L.lattice := fun h => hz (by simpa using L.lattice.neg_mem h)
      refine ⟨-z, ?_⟩
      rw [expE_of_notMem L hz']
      refine some_eq_some L (by rw [L.weierstrassP_neg, hzx]) ?_
      rw [L.derivWeierstrassP_neg, neg_div, h', neg_neg]

/-- **`expG` is onto.** -/
theorem expG_surjective {d₀ d₁ m : ℕ} (Ls : Fin m → PeriodPair) :
    Function.Surjective (expG (d₀ := d₀) (d₁ := d₁) Ls) := by
  intro g
  choose z hz using fun k => expE_surjective (Ls k) (g.2.2 k)
  refine ⟨(g.1, fun j => Complex.log (Additive.toMul g.2.1 j : ℂ), z), Prod.ext rfl (Prod.ext ?_ ?_)⟩
  · show Additive.ofMul _ = g.2.1
    rw [← ofMul_toMul g.2.1]
    congr 1
    funext j
    exact Units.ext (by simp [expU, Complex.exp_log (Units.ne_zero _)])
  · funext k; exact hz k

end LSG.ME
