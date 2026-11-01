/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.CM.Rot

/-!
# `κ₁ = 0` gives CM data: from `ζ(αz) = ᾱζ(z)` to `CMData`

lean_mstar's premise `KappaOneZero L` is `ζ(αz) = ᾱ ζ(z)` for all `z`. Since `ζ` has a simple pole
with residue `1` at every lattice point (`tendsto_sub_mul_zeta`) and is continuous elsewhere, such
an identity forces `αΛ ⊆ Λ` and, applied to `α⁻¹`, `α⁻¹Λ ⊆ Λ` (`mul_mem_of_zeta_mul`). Then `ζ(αz) =
α⁻¹ζ(z)` (`zeta_mul`) and `ζ(ω₁) = η(ω₁) ≠ 0` (Legendre) give `ᾱ = α⁻¹`: **`cmData_of_zeta`**.
-/

open Complex LSG.Weierstrass PeriodPair Filter Topology

namespace LSG.CM

variable (L : PeriodPair)

/-- `(z − λ) ζ(z) → 1` as `z → λ ∈ Λ`. -/
lemma tendsto_sub_mul_zeta {l : ℂ} (hl : l ∈ L.lattice) :
    Tendsto (fun z => (z - l) * zeta L z) (𝓝[≠] l) (𝓝 1) := by
  have h1 : Tendsto (fun z => (z - l) * zetaExcept L ⟨l, hl⟩ z) (𝓝[≠] l) (𝓝 0) := by
    have : ContinuousAt (fun z => (z - l) * zetaExcept L ⟨l, hl⟩ z) l :=
      (continuousAt_id.sub continuousAt_const).mul (continuousAt_zetaExcept L ⟨l, hl⟩)
    have h := this.tendsto
    simp only [sub_self, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z => (z - l) * zetaSummand l z) (𝓝[≠] l) (𝓝 1) := by
    have hc : ContinuousAt (fun z => 1 + (z - l) * (1 / l + z / l ^ 2)) l :=
      continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul
        (continuousAt_const.add (continuousAt_id.div_const _)))
    have h := hc.tendsto
    simp only [sub_self, zero_mul, add_zero] at h
    refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z - l ≠ 0 := sub_ne_zero.mpr hz
    simp only [zetaSummand]
    have e : (z - l) * (1 / (z - l)) = 1 := mul_one_div_cancel hz'
    linear_combination -e
  have := h1.add h2
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun z => ?_)
  simp only
  rw [zeta_eq_zetaExcept_add L ⟨l, hl⟩ z]
  ring

/-- **An identity `ζ(βz) = c ζ(z)` (`c ≠ 0`) forces `βΛ ⊆ Λ`.** -/
theorem mul_mem_of_zeta_mul {β c : ℂ} (hc : c ≠ 0) (h : ∀ z, zeta L (β * z) = c * zeta L z)
    {l : ℂ} (hl : l ∈ L.lattice) : β * l ∈ L.lattice := by
  by_contra hβ
  have hcont : ContinuousAt (zeta L) (β * l) :=
    ((differentiableOn_zeta L _ hβ).differentiableAt
      ((isOpen_compl_coe_lattice L).mem_nhds hβ)).continuousAt
  have hc2 : ContinuousAt (fun z => (z - l) * zeta L (β * z)) l :=
    (continuousAt_id.sub continuousAt_const).mul
      (ContinuousAt.comp (g := zeta L) (f := fun z => β * z) hcont
        (continuousAt_const.mul continuousAt_id))
  have T2 := hc2.tendsto
  simp only [sub_self, zero_mul] at T2
  have T1 := (tendsto_sub_mul_zeta L hl).const_mul c
  rw [mul_one] at T1
  have T1' : Tendsto (fun z => (z - l) * zeta L (β * z)) (𝓝[≠] l) (𝓝 c) := by
    refine T1.congr' (Eventually.of_forall fun z => ?_)
    simp only [h]; ring
  exact hc (tendsto_nhds_unique T1' (T2.mono_left nhdsWithin_le_nhds))

/-- **`κ₁ = 0` gives CM data.** -/
theorem cmData_of_zeta {α : ℂ} (hω : L.ω₂ = α * L.ω₁) (him : 0 < α.im) (halg : IsAlgebraic ℚ α)
    (hz : ∀ z, zeta L (α * z) = starRingEnd ℂ α * zeta L z) : CMData L α := by
  have hα : α ≠ 0 := by rintro rfl; simp at him
  have hcα : starRingEnd ℂ α ≠ 0 := (map_ne_zero _).mpr hα
  have hinv : ∀ w, zeta L (α⁻¹ * w) = (starRingEnd ℂ α)⁻¹ * zeta L w := by
    intro w
    have := hz (α⁻¹ * w)
    rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul] at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hcα, one_mul]
  have hunit : IsLatUnit L α :=
    ⟨hα, fun x hx => mul_mem_of_zeta_mul L hcα hz hx,
      fun x hx => mul_mem_of_zeta_mul L (inv_ne_zero hcα) hinv hx⟩
  -- `η(ω₁) ≠ 0`
  have hpos : 0 < (L.ω₂ / L.ω₁).im := by
    rw [hω, mul_div_cancel_right₀ _ (ω₁_ne_zero L)]; exact him
  have hη : eta L L.ω₁ ≠ 0 := by
    intro h0
    have h := legendre_of_im_pos L hpos
    rw [hω, eta_mul L hunit L.ω₁_mem_lattice, h0] at h
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [zero_mul, mul_zero, sub_zero] at h
    exact (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero) h.symm
  have hconj : starRingEnd ℂ α = α⁻¹ := by
    have h1 := hz L.ω₁
    rw [zeta_mul L hunit, LSG.W88.Vec.zeta_of_mem_lattice L L.ω₁_mem_lattice] at h1
    exact (mul_right_cancel₀ hη h1).symm
  exact ⟨hunit, hω, hconj, him, halg⟩

end LSG.CM
