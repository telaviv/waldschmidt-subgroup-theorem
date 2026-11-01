/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.Legendre

/-!
# Elliptic functions with at most one simple pole are constant

This file provides the "Liouville + removable singularities" toolkit for elliptic functions,
without any residue theorem.

* `LSG.Weierstrass.LocBdd f s`: `f` is bounded on a punctured neighbourhood of `s`.
* `LSG.Weierstrass.Discr S`: every point has a punctured neighbourhood disjoint from `S`.
* `exists_differentiable_extension`: a function holomorphic off a discrete set `S` and bounded
  near each point of `S` agrees off `S` with an entire function (Riemann's removable singularity
  theorem, applied at every point of `S`).
* `eq_linear_of_add_sub_const`: an entire function whose `Λ`-differences are constant is linear
  (its derivative is entire and periodic, hence constant by Liouville).
* `eq_const_of_simple_pole` (**sum of residues**): an elliptic function whose only possible poles
  are simple poles at `a + Λ` is constant. Proof (the `ζ`-subtraction trick): with `r` the residue
  at `a`, `g = f - r ζ(· - a)` extends to an entire function with constant `Λ`-differences
  `-r η(ω)`, hence `g = αz + β`; so `α ω = -r η(ω)` on `Λ`, and Legendre's relation
  (`η₁ω₂ - η₂ω₁ ≠ 0`) forces `r = 0`, then `α = 0`.
-/

open Module Filter Complex Set
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

/-- `f` is bounded on a punctured neighbourhood of `s`. -/
def LocBdd (f : ℂ → ℂ) (s : ℂ) : Prop := ∃ M : ℝ, ∀ᶠ u in 𝓝[≠] s, ‖f u‖ ≤ M

/-- Every point has a punctured neighbourhood disjoint from `S`. -/
def Discr (S : Set ℂ) : Prop := ∀ x, ∀ᶠ y in 𝓝[≠] x, y ∉ S

/-! ### Local boundedness -/

section LocBdd

variable {f g : ℂ → ℂ} {s : ℂ}

lemma LocBdd.of_continuousAt (h : ContinuousAt f s) : LocBdd f s := by
  refine ⟨‖f s‖ + 1, nhdsWithin_le_nhds ?_⟩
  exact (h.norm.eventually (Iio_mem_nhds (lt_add_one _))).mono fun u hu => le_of_lt hu

lemma LocBdd.congr (h : LocBdd f s) (hfg : ∀ᶠ u in 𝓝[≠] s, f u = g u) : LocBdd g s := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, (hM.and hfg).mono fun u hu => hu.2 ▸ hu.1⟩

lemma LocBdd.add (hf : LocBdd f s) (hg : LocBdd g s) : LocBdd (fun u => f u + g u) s := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, (hM.and hN).mono fun u hu => (norm_add_le _ _).trans (add_le_add hu.1 hu.2)⟩

lemma LocBdd.sub (hf : LocBdd f s) (hg : LocBdd g s) : LocBdd (fun u => f u - g u) s := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, (hM.and hN).mono fun u hu => (norm_sub_le _ _).trans (add_le_add hu.1 hu.2)⟩

lemma LocBdd.mul (hf : LocBdd f s) (hg : LocBdd g s) : LocBdd (fun u => f u * g u) s := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨max M 0 * max N 0, (hM.and hN).mono fun u hu => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hu.1.trans (le_max_left _ _)) (hu.2.trans (le_max_left _ _)) (norm_nonneg _)
    (le_max_right _ _)

lemma tendsto_sub_nhdsNE (s ω : ℂ) : Tendsto (fun u => u - ω) (𝓝[≠] (s + ω)) (𝓝[≠] s) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := (continuous_sub_right ω).tendsto (s + ω)
    simp only [add_sub_cancel_right] at this
    exact this.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun u hu => ?_
    simp only [mem_compl_iff, mem_singleton_iff] at hu ⊢
    intro h
    exact hu (by rw [← h]; ring)

lemma tendsto_neg_nhdsNE (s : ℂ) : Tendsto (fun u => -u) (𝓝[≠] (-s)) (𝓝[≠] s) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := continuous_neg.tendsto (-s)
    simp only [neg_neg] at this
    exact this.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun u hu => ?_
    simp only [mem_compl_iff, mem_singleton_iff] at hu ⊢
    intro h
    exact hu (by rw [← h]; ring)

lemma LocBdd.of_periodic {ω : ℂ} (hper : ∀ u, f (u + ω) = f u) (h : LocBdd f s) :
    LocBdd f (s + ω) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ((tendsto_sub_nhdsNE s ω).eventually hM).mono fun u hu => ?_⟩
  have := hper (u - ω)
  rw [sub_add_cancel] at this
  rw [this]; exact hu

lemma LocBdd.of_even (heven : ∀ u, f (-u) = f u) (h : LocBdd f s) : LocBdd f (-s) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ((tendsto_neg_nhdsNE s).eventually hM).mono fun u hu => ?_⟩
  have := heven u
  rwa [this] at hu

end LocBdd

/-- Two functions continuous at `u` that agree on a punctured neighbourhood agree at `u`. -/
lemma eq_of_eventuallyEq_nhdsNE {F₁ F₂ : ℂ → ℂ} {u : ℂ} (h₁ : ContinuousAt F₁ u)
    (h₂ : ContinuousAt F₂ u) (h : ∀ᶠ v in 𝓝[≠] u, F₁ v = F₂ v) : F₁ u = F₂ u :=
  tendsto_nhds_unique ((h₁.tendsto.mono_left nhdsWithin_le_nhds).congr' h)
    (h₂.tendsto.mono_left nhdsWithin_le_nhds)

/-! ### Discrete sets -/

section Discr

variable (L : PeriodPair)

lemma Discr.union {S T : Set ℂ} (hS : Discr S) (hT : Discr T) : Discr (S ∪ T) := fun x =>
  ((hS x).and (hT x)).mono fun _ hy h => h.elim hy.1 hy.2

lemma Discr.eventually_nhds {S : Set ℂ} (hS : Discr S) {x : ℂ} (hx : x ∉ S) :
    ∀ᶠ y in 𝓝 x, y ∉ S := by
  have := hS x
  rw [eventually_nhdsWithin_iff] at this
  filter_upwards [this] with y hy
  by_cases h : y = x
  · rw [h]; exact hx
  · exact hy h

lemma Discr.exists_notMem {S : Set ℂ} (hS : Discr S) : ∃ u, u ∉ S := (hS 0).exists

/-- `{u | c u + d ∈ Λ}` is discrete for `c ≠ 0`. -/
lemma discr_affine {c : ℂ} (hc : c ≠ 0) (d : ℂ) : Discr {u | c * u + d ∈ L.lattice} := by
  intro x
  have h1 := L.compl_lattice_sdiff_singleton_mem_nhds (c * x + d)
  have h2 : Tendsto (fun u => c * u + d) (𝓝 x) (𝓝 (c * x + d)) :=
    ((continuous_const.mul continuous_id).add continuous_const).tendsto x
  filter_upwards [nhdsWithin_le_nhds (h2.eventually h1), self_mem_nhdsWithin] with u hu hux
  intro hmem
  apply hu
  refine ⟨hmem, fun h => hux ?_⟩
  simp only [mem_singleton_iff, add_left_inj] at h ⊢
  exact mul_left_cancel₀ hc h

lemma discr_sub (a : ℂ) : Discr {u | u - a ∈ L.lattice} := by
  have := discr_affine L one_ne_zero (-a)
  simpa [sub_eq_add_neg] using this

lemma discr_add (a : ℂ) : Discr {u | u + a ∈ L.lattice} := by
  have := discr_affine L one_ne_zero a
  simpa using this

end Discr

/-! ### Removable singularities and Liouville -/

/-- A function holomorphic off a discrete set `S` and bounded near every point of `S` agrees
off `S` with an entire function. -/
theorem exists_differentiable_extension {f : ℂ → ℂ} {S : Set ℂ} (hS : Discr S)
    (hd : ∀ x ∉ S, DifferentiableAt ℂ f x) (hb : ∀ s ∈ S, LocBdd f s) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x ∉ S, F x = f x := by
  classical
  set F : ℂ → ℂ := fun x => if x ∈ S then limUnder (𝓝[≠] x) f else f x with hF
  refine ⟨F, fun x => ?_, fun x hx => by simp [hF, hx]⟩
  by_cases hx : x ∈ S
  · obtain ⟨M, hM⟩ := hb x hx
    have h := (hS x).and hM
    rw [eventually_nhdsWithin_iff] at h
    set U := {y | y ≠ x → y ∉ S ∧ ‖f y‖ ≤ M}
    have hU : U ∈ 𝓝 x := h
    have hdU : DifferentiableOn ℂ f (U \ {x}) := fun y hy =>
      (hd y (hy.1 hy.2).1).differentiableWithinAt
    have hbU : BddAbove (norm ∘ f '' (U \ {x})) :=
      ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact (hy.1 hy.2).2⟩
    have hD := (Complex.differentiableOn_update_limUnder_of_bddAbove hU hdU hbU).differentiableAt hU
    refine hD.congr_of_eventuallyEq ?_
    filter_upwards [hU] with y hy
    by_cases hyx : y = x
    · subst hyx; simp [hF, hx]
    · simp [hF, (hy hyx).1, Function.update_of_ne hyx]
  · refine (hd x hx).congr_of_eventuallyEq ?_
    filter_upwards [hS.eventually_nhds hx] with y hy
    simp [hF, hy]

variable (L : PeriodPair)

/-- An entire function with constant `Λ`-differences is linear. -/
theorem eq_linear_of_add_sub_const {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ∀ ω ∈ L.lattice, ∃ c, ∀ u, F (u + ω) = F u + c) :
    ∃ α β : ℂ, ∀ u, F u = α * u + β := by
  have hd : Differentiable ℂ (deriv F) := hF.deriv
  have hper : ∀ u ω, ω ∈ L.lattice → deriv F (u + ω) = deriv F u := by
    intro u ω hω
    obtain ⟨c, hc⟩ := h ω hω
    have e : (fun v => F (v + ω)) = fun v => F v + c := funext hc
    have h1 : deriv (fun v => F (v + ω)) u = deriv F (u + ω) := deriv_comp_add_const F ω u
    rw [← h1, e, deriv_add_const]
  have hc := IsZLattice.isCompact_range_of_periodic L.lattice _ hd.continuous
    (fun z w hw => hper z w hw)
  set α := deriv F 0
  have hconst : ∀ u, deriv F u = α := fun u => hd.apply_eq_apply_of_bounded hc.isBounded u 0
  refine ⟨α, F 0, fun u => ?_⟩
  have hG : Differentiable ℂ (fun v => F v - α * v) := hF.sub (differentiable_id.const_mul α)
  have hG' : ∀ v, deriv (fun v => F v - α * v) v = 0 := by
    intro v
    have : HasDerivAt (fun v => F v - α * v) (deriv F v - α * 1) v :=
      (hF v).hasDerivAt.sub ((hasDerivAt_id' v).const_mul α)
    rw [this.deriv, hconst v]
    ring
  have := is_const_of_deriv_eq_zero hG hG' u 0
  simp only [mul_zero, sub_zero] at this
  linear_combination this

/-- **Sum of residues, one simple pole.** An elliptic function whose only possible poles are
simple poles along `a + Λ` is constant (off its singular set). -/
theorem eq_const_of_simple_pole {f : ℂ → ℂ} {S : Set ℂ} (a : ℂ) (hS : Discr S)
    (hSinv : ∀ u ∈ S, ∀ ω ∈ L.lattice, u + ω ∈ S)
    (hper : ∀ u ∉ S, ∀ ω ∈ L.lattice, f (u + ω) = f u)
    (hd : ∀ x ∉ S, DifferentiableAt ℂ f x)
    (hb : ∀ s ∈ S, s - a ∉ L.lattice → LocBdd f s)
    (ha : LocBdd (fun u => (u - a) * f u) a) :
    ∃ C, ∀ u ∉ S, f u = C := by
  set A : Set ℂ := {u | u - a ∈ L.lattice} with hA_def
  set S' := S ∪ A with hS'_def
  have hS' : Discr S' := hS.union (discr_sub L a)
  have hS'inv : ∀ u ∉ S', ∀ ω ∈ L.lattice, u + ω ∉ S' := by
    intro u hu ω hω h
    apply hu
    rcases h with h | h
    · left
      have := hSinv _ h (-ω) (neg_mem hω)
      rwa [add_neg_cancel_right] at this
    · right
      change u + ω - a ∈ L.lattice at h
      change u - a ∈ L.lattice
      have := sub_mem h hω
      rwa [show u + ω - a - ω = u - a by ring] at this
  -- the residue at `a`
  set h : ℂ → ℂ := fun u => (u - a) * f u with hh_def
  obtain ⟨M, hM⟩ := ha
  have hh := (hS a).and hM
  rw [eventually_nhdsWithin_iff] at hh
  set U := {y | y ≠ a → y ∉ S ∧ ‖h y‖ ≤ M}
  have hU : U ∈ 𝓝 a := hh
  have hdU : DifferentiableOn ℂ h (U \ {a}) := fun y hy =>
    ((differentiableAt_id.sub_const a).mul (hd y (hy.1 hy.2).1)).differentiableWithinAt
  have hbU : BddAbove (norm ∘ h '' (U \ {a})) :=
    ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact (hy.1 hy.2).2⟩
  set r := limUnder (𝓝[≠] a) h
  set H := Function.update h a r with hH_def
  have hH : DifferentiableAt ℂ H a :=
    (Complex.differentiableOn_update_limUnder_of_bddAbove hU hdU hbU).differentiableAt hU
  have hdsl : ContinuousAt (dslope H a) a := continuousAt_dslope_same.mpr hH
  have hloc : ∀ u, u ≠ a → f u - r * (u - a)⁻¹ = dslope H a u := by
    intro u hu
    have hu' : u - a ≠ 0 := sub_ne_zero.mpr hu
    rw [dslope_of_ne _ hu, slope_def_field]
    simp only [hH_def, Function.update_of_ne hu, Function.update_self, hh_def]
    field_simp
  -- subtract `r ζ(· - a)`
  set g : ℂ → ℂ := fun u => f u - r * zeta L (u - a) with hg_def
  have hzc : ∀ x, x - a ∉ L.lattice → DifferentiableAt ℂ (fun u => zeta L (u - a)) x := by
    intro x hx
    have := (differentiableOn_zeta L _ hx).differentiableAt
      ((isOpen_compl_coe_lattice L).mem_nhds hx)
    exact this.comp x (differentiableAt_id.sub_const a)
  have hgd : ∀ x ∉ S', DifferentiableAt ℂ g x := by
    intro x hx
    have h1 : x ∉ S := fun h => hx (Or.inl h)
    have h2 : x - a ∉ L.lattice := fun h => hx (Or.inr h)
    exact (hd x h1).sub ((hzc x h2).const_mul r)
  have hgper : ∀ u ∉ S', ∀ ω ∈ L.lattice, g (u + ω) = g u + -(r * eta L ω) := by
    intro u hu ω hω
    have h1 : u ∉ S := fun h => hu (Or.inl h)
    simp only [hg_def]
    rw [hper u h1 ω hω, show u + ω - a = (u - a) + ω by ring, zeta_add L hω]
    ring
  have hga : LocBdd g a := by
    have hc : ContinuousAt (fun u => dslope H a u - r * zetaExcept L 0 (u - a)) a := by
      have h1 : ContinuousAt (fun u => zetaExcept L 0 (u - a)) a := by
        have := (differentiableAt_zetaExcept_zero L (w := a - a) (Or.inr (sub_self a))).continuousAt
        exact this.comp (f := fun u => u - a) (continuousAt_id.sub continuousAt_const)
      exact hdsl.sub (continuousAt_const.mul h1)
    refine (LocBdd.of_continuousAt hc).congr ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [← hloc u hu]
    simp only [hg_def]
    rw [zeta_eq_zetaExcept_zero_add]
    ring
  have hgb : ∀ s ∈ S', LocBdd g s := by
    intro s hs
    by_cases hsa : s - a ∈ L.lattice
    · obtain ⟨M', hM'⟩ := hga
      refine ⟨M' + ‖r * eta L (s - a)‖, ?_⟩
      have h1 := (tendsto_sub_nhdsNE a (s - a)).eventually (hM'.and (hS' a))
      rw [show a + (s - a) = s by ring] at h1
      filter_upwards [h1] with u hu
      have := hgper (u - (s - a)) hu.2 (s - a) hsa
      rw [sub_add_cancel] at this
      rw [this]
      exact (norm_add_le _ _).trans (by rw [norm_neg]; linarith [hu.1])
    · have hsS : s ∈ S := hs.resolve_right hsa
      exact (hb s hsS hsa).sub
        (LocBdd.of_continuousAt (continuousAt_const.mul (hzc s hsa).continuousAt))
  obtain ⟨G, hGd, hGg⟩ := exists_differentiable_extension hS' hgd hgb
  have hGper : ∀ ω ∈ L.lattice, ∃ c, ∀ u, G (u + ω) = G u + c := by
    intro ω hω
    refine ⟨-(r * eta L ω), fun u => ?_⟩
    refine eq_of_eventuallyEq_nhdsNE (F₁ := fun u => G (u + ω)) (F₂ := fun u => G u + -(r * eta L ω))
      ((hGd _).continuousAt.comp (continuousAt_id.add continuousAt_const))
      ((hGd u).continuousAt.add continuousAt_const) ?_
    filter_upwards [hS' u] with v hv
    rw [hGg _ (hS'inv v hv ω hω), hGg v hv, hgper v hv ω hω]
  obtain ⟨α, β, hαβ⟩ := eq_linear_of_add_sub_const L hGd hGper
  obtain ⟨u₀, hu₀⟩ := hS'.exists_notMem
  have hαω : ∀ ω ∈ L.lattice, α * ω = -(r * eta L ω) := by
    intro ω hω
    have h1 := hgper u₀ hu₀ ω hω
    rw [← hGg _ (hS'inv u₀ hu₀ ω hω), ← hGg u₀ hu₀, hαβ, hαβ] at h1
    linear_combination h1
  have hr : r = 0 := by
    have h1 := hαω _ L.ω₁_mem_lattice
    have h2 := hαω _ L.ω₂_mem_lattice
    have hl := legendre_ne_zero L
    have : r * (eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁) = 0 := by
      linear_combination L.ω₂ * h1 - L.ω₁ * h2
    exact (mul_eq_zero.mp this).resolve_right hl
  have hα : α = 0 := by
    have h1 := hαω _ L.ω₁_mem_lattice
    rw [hr, zero_mul, neg_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right (ω₁_ne_zero L)
  have hfG : ∀ v ∉ S', f v = β := by
    intro v hv
    have := hGg v hv
    rw [hαβ, hα, zero_mul, zero_add] at this
    simp only [hg_def, hr, zero_mul, sub_zero] at this
    exact this.symm
  refine ⟨β, fun u hu => ?_⟩
  by_cases hua : u - a ∈ L.lattice
  · refine eq_of_eventuallyEq_nhdsNE (F₂ := fun _ => β) (hd u hu).continuousAt continuousAt_const ?_
    filter_upwards [hS' u] with v hv
    exact hfG v hv
  · exact hfG u (fun h => h.elim hu hua)

/-- An elliptic function bounded near each point of its (discrete) singular set is constant. -/
theorem eq_const_of_locBdd {f : ℂ → ℂ} {S : Set ℂ} (hS : Discr S)
    (hSinv : ∀ u ∈ S, ∀ ω ∈ L.lattice, u + ω ∈ S)
    (hper : ∀ u ∉ S, ∀ ω ∈ L.lattice, f (u + ω) = f u)
    (hd : ∀ x ∉ S, DifferentiableAt ℂ f x) (hb : ∀ s ∈ S, LocBdd f s) :
    ∃ C, ∀ u ∉ S, f u = C := by
  by_cases h0 : (0 : ℂ) ∈ S
  · exact eq_const_of_simple_pole L 0 hS hSinv hper hd (fun s hs _ => hb s hs)
      ((LocBdd.of_continuousAt (f := fun u => u - 0) (by fun_prop)).mul (hb 0 h0))
  · exact eq_const_of_simple_pole L 0 hS hSinv hper hd (fun s hs _ => hb s hs)
      (LocBdd.of_continuousAt (((continuous_id.sub continuous_const).continuousAt).mul
        (hd 0 h0).continuousAt))

end LSG.Weierstrass
