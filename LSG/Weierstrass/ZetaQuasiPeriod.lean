/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.SigmaQuasiPeriod

/-!
# Quasi-periodicity of `ζ` at every point

`zeta_add_eta` proves `ζ(z + ω) = ζ(z) + η(ω)` off the lattice. Here we extend it to all `z`,
including the lattice points, where Lean's junk value of the series is the regular part
`lim_{w → l} (ζ(w) - 1/(w - l))`. The tool is `zetaExcept l₀`, the `ζ`-series with the
`l₀`-term removed, which is holomorphic at `l₀`.
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

/-- The `ζ`-series with the `l₀`-term removed. -/
def zetaExcept (l₀ : L.lattice) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l = l₀ then 0 else zetaSummand l z

lemma hasSumLocallyUniformly_zetaExcept (l₀ : L.lattice) :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ if l = l₀ then 0 else zetaSummand l z)
      (zetaExcept L l₀) := by
  refine PeriodPair.hasSumLocallyUniformly_aux L (u := fun r l ↦ 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    _ (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · rw [norm_zero]; positivity
  · exact zetaSummand_bound r hr s hs l h

lemma zeta_eq_zetaExcept_add (l₀ : L.lattice) (z : ℂ) :
    zeta L z = zetaExcept L l₀ z + zetaSummand l₀ z := by
  have h := ((hasSumLocallyUniformly_zetaExcept L l₀).hasSum (x := z)).add
    (hasSum_ite_eq l₀ (zetaSummand l₀ z))
  refine (hasSum_zeta L z).unique ?_
  convert h using 1
  funext l
  by_cases hl : l = l₀
  · simp [hl]
  · simp [hl]

lemma continuousAt_zetaExcept (l₀ : L.lattice) : ContinuousAt (zetaExcept L l₀) l₀ := by
  have hU : IsOpen (L.lattice \ {(l₀ : ℂ)} : Set ℂ)ᶜ := L.isOpen_compl_lattice_sdiff
  have hd : DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {(l₀ : ℂ)} : Set ℂ)ᶜ := by
    refine (hasSumLocallyUniformly_zetaExcept L l₀).tendstoLocallyUniformlyOn.differentiableOn
      (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) hU
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
  exact ((hd _ (by simp)).differentiableAt (hU.mem_nhds (by simp))).continuousAt

/-- **Quasi-periodicity of `ζ`** at every point (including lattice points, with Lean's junk
values): `ζ(z + ω) = ζ(z) + η(ω)` for `ω ∈ Λ`. -/
theorem zeta_add {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    zeta L (z + ω) = zeta L z + eta L ω := by
  by_cases hz : z ∉ L.lattice
  · exact zeta_add_eta L hω hz
  replace hz := not_not.mp hz
  set l₀ : L.lattice := ⟨z, hz⟩
  set l₁ : L.lattice := ⟨z + ω, add_mem hz hω⟩
  let G : ℂ → ℂ := fun w ↦ zetaExcept L l₁ (w + ω) - zetaExcept L l₀ w +
    (1 / (z + ω) + (w + ω) / (z + ω) ^ 2 - 1 / z - w / z ^ 2) - eta L ω
  have hG : ∀ w, zeta L (w + ω) - zeta L w - eta L ω = G w := by
    intro w
    rw [zeta_eq_zetaExcept_add L l₁ (w + ω), zeta_eq_zetaExcept_add L l₀ w]
    simp only [G, zetaSummand, l₀, l₁]
    rw [show w + ω - (z + ω) = w - z by ring]
    ring
  have hc : ContinuousAt G z := by
    have h1 : ContinuousAt (fun w ↦ zetaExcept L l₁ (w + ω)) z :=
      (continuousAt_zetaExcept L l₁).comp (f := fun w ↦ w + ω) (continuousAt_id.add_const ω)
    have h2 : ContinuousAt (zetaExcept L l₀) z := continuousAt_zetaExcept L l₀
    exact ((h1.sub h2).add (by fun_prop)).sub continuousAt_const
  have hev : G =ᶠ[𝓝[≠] z] fun _ ↦ 0 := by
    have := L.compl_lattice_sdiff_singleton_mem_nhds z
    filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with w hw hwz
    have hw' : w ∉ L.lattice := fun h ↦ hw ⟨h, hwz⟩
    rw [← hG, zeta_add_eta L hω hw']
    ring
  have hlim : Tendsto G (𝓝[≠] z) (𝓝 (G z)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have h0 : G z = 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
  have := hG z
  rw [h0] at this
  linear_combination this

end LSG.Weierstrass
