/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.Addition

/-!
# The addition formula for the Weierstrass `ζ` function

For `u, v, u + v, u − v ∉ Λ`:
`ζ(u + v) − ζ(u) − ζ(v) = ½ (℘'(u) − ℘'(v)) / (℘(u) − ℘(v))`  (`zeta_add_formula`).

This is the cocycle of the universal vector extension `E^♮` (see `VECEXT_SPIKE.md`): with
`exp(z, w) = (exp_E z, w − ζ(z))`, the fibre coordinate of a sum is `t₁ + t₂ − c(P₁, P₂)`,
`c = ½ (y₁ − y₂)/(x₁ − x₂)`.

## Proof
`h(u, v) = ζ(u + v) − ζ(u) − ζ(v) − ½ m(u, v)` (`m` the chord slope) has `∂h/∂u = 0` off the
exceptional set (by `ζ' = −℘`, the addition theorem for `℘` and `℘'² = 4℘³ − g₂℘ − g₃`), and the
set `S_v = {u | u, u + v, u − v ∉ Λ}` is connected (complement of a countable set). Hence `h(·, v)`
is constant on `S_v`. With the symmetry `h(u, v) = h(v, u)` and the oddness
`h(−u, −v) = −h(u, v)`: `h(u,v) = h(−u,v) = h(v,−u) = h(−v,−u) = h(−u,−v) = −h(u,v)`.
No Laurent expansion is needed.
-/

open Module Filter Complex Set
open scoped Topology

noncomputable section

namespace LSG.Elliptic

open PeriodPair LSG.Weierstrass

variable (L : PeriodPair)

/-- The defect `ζ(u + v) − ζ(u) − ζ(v) − ½ m(u, v)` of the `ζ` addition formula. -/
def zetaDefect (u v : ℂ) : ℂ :=
  zeta L (u + v) - zeta L u - zeta L v - chordSlope L u v / 2

/-- The good set `{u | u, u + v, u − v ∉ Λ}`. -/
def goodSet (v : ℂ) : Set ℂ :=
  {u | u ∉ L.lattice ∧ u + v ∉ L.lattice ∧ u - v ∉ L.lattice}

lemma goodSet_compl (v : ℂ) :
    (goodSet L v)ᶜ = (L.lattice : Set ℂ) ∪ ((fun u => u + v) ⁻¹' L.lattice) ∪
      ((fun u => u - v) ⁻¹' L.lattice) := by
  ext u
  simp only [goodSet, mem_compl_iff, mem_ofPred_eq, not_and_or, not_not, mem_union, mem_preimage,
    SetLike.mem_coe, or_assoc]

lemma isOpen_goodSet (v : ℂ) : IsOpen (goodSet L v) := by
  have hc : IsClosed (L.lattice : Set ℂ) := L.isClosed_lattice
  have : IsClosed (goodSet L v)ᶜ := by
    rw [goodSet_compl]
    exact (hc.union (hc.preimage (continuous_id.add continuous_const))).union
      (hc.preimage (continuous_id.sub continuous_const))
  simpa using this.isOpen_compl

lemma countable_goodSet_compl (v : ℂ) : (goodSet L v)ᶜ.Countable := by
  rw [goodSet_compl]
  have hΛ := countable_lattice L
  exact (hΛ.union (hΛ.preimage (add_left_injective v))).union
    (hΛ.preimage (sub_left_injective (b := v)))

lemma isPreconnected_goodSet (v : ℂ) : IsPreconnected (goodSet L v) := by
  have := (countable_goodSet_compl L v).isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
  simpa using this.isPreconnected

lemma pdiff_ne' {u v : ℂ} (hu : u ∈ goodSet L v) (hv : v ∉ L.lattice) : ℘[L] u - ℘[L] v ≠ 0 :=
  pdiff_ne L hu.1 hv hu.2.1 hu.2.2

/-- The derivative of the chord slope in its first argument. -/
lemma hasDerivAt_chordSlope_left {u v : ℂ} (hu : u ∉ L.lattice) (hne : ℘[L] u - ℘[L] v ≠ 0) :
    HasDerivAt (fun a => chordSlope L a v)
      (((6 * ℘[L] u ^ 2 - L.g₂ / 2) * (℘[L] u - ℘[L] v) - (℘'[L] u - ℘'[L] v) * ℘'[L] u) /
        (℘[L] u - ℘[L] v) ^ 2) u := by
  have hf : HasDerivAt (fun a => ℘'[L] a - ℘'[L] v) (6 * ℘[L] u ^ 2 - L.g₂ / 2) u :=
    (hasDerivAt_derivWeierstrassP L hu).sub_const _
  have hg : HasDerivAt (fun a => ℘[L] a - ℘[L] v) (℘'[L] u) u :=
    (hasDerivAt_weierstrassP L hu).sub_const _
  exact hf.div hg hne

/-- `∂h/∂u = 0` on the good set. -/
lemma hasDerivAt_zetaDefect {u v : ℂ} (hu : u ∈ goodSet L v) (hv : v ∉ L.lattice) :
    HasDerivAt (fun a => zetaDefect L a v) 0 u := by
  obtain ⟨hu0, hup, hum⟩ := hu
  have hne := pdiff_ne L hu0 hv hup hum
  have h1 : HasDerivAt (fun a => zeta L (a + v)) (-℘[L] (u + v)) u :=
    (hasDerivAt_zeta L hup).comp_add_const u v
  have h2 := hasDerivAt_zeta L hu0
  have h3 := (hasDerivAt_chordSlope_left L hu0 hne).div_const 2
  have h := ((h1.sub h2).sub_const (zeta L v)).sub h3
  have hp := L.derivWeierstrassP_sq u hu0
  have hq := L.derivWeierstrassP_sq v hv
  have hadd := weierstrassP_add L hu0 hv hup hum
  have e : -℘[L] (u + v) - -℘[L] u - ((6 * ℘[L] u ^ 2 - L.g₂ / 2) * (℘[L] u - ℘[L] v) -
      (℘'[L] u - ℘'[L] v) * ℘'[L] u) / (℘[L] u - ℘[L] v) ^ 2 / 2 = 0 := by
    rw [hadd]
    unfold chordSlope
    set a := ℘[L] u
    set b := ℘[L] v
    set p := ℘'[L] u
    set q := ℘'[L] v
    have key : 4 * (a - b) ^ 2 * (2 * a + b) - (p - q) ^ 2 - 2 * (6 * a ^ 2 - L.g₂ / 2) * (a - b) +
        2 * (p - q) * p = 0 := by
      linear_combination hp - hq
    field_simp
    linear_combination key + 3 * hp - 3 * hq
  rw [e] at h
  exact h

lemma zetaDefect_eq_of_mem {a b v : ℂ} (ha : a ∈ goodSet L v) (hb : b ∈ goodSet L v)
    (hv : v ∉ L.lattice) : zetaDefect L a v = zetaDefect L b v :=
  (isOpen_goodSet L v).is_const_of_deriv_eq_zero (isPreconnected_goodSet L v)
    (fun _ hx => (hasDerivAt_zetaDefect L hx hv).differentiableAt.differentiableWithinAt)
    (fun _ hx => (hasDerivAt_zetaDefect L hx hv).deriv) ha hb

lemma zetaDefect_comm (u v : ℂ) : zetaDefect L u v = zetaDefect L v u := by
  unfold zetaDefect chordSlope
  rw [add_comm u v]
  by_cases h : ℘[L] u - ℘[L] v = 0
  · have h' : ℘[L] v - ℘[L] u = 0 := by linear_combination -h
    rw [h, h', div_zero, div_zero]
    ring
  · have h' : ℘[L] v - ℘[L] u ≠ 0 := fun h' => h (by linear_combination -h')
    field_simp
    ring

lemma zetaDefect_neg (u v : ℂ) : zetaDefect L (-u) (-v) = -zetaDefect L u v := by
  unfold zetaDefect chordSlope
  rw [show -u + -v = -(u + v) by ring, zeta_neg, zeta_neg, zeta_neg, L.weierstrassP_neg,
    L.weierstrassP_neg, L.derivWeierstrassP_neg, L.derivWeierstrassP_neg]
  ring

/-- **Addition formula for `ζ`**: for `u, v, u + v, u − v ∉ Λ`,
`ζ(u + v) − ζ(u) − ζ(v) = ½ (℘'(u) − ℘'(v)) / (℘(u) − ℘(v))`. -/
theorem zeta_add_formula {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice)
    (hp : u + v ∉ L.lattice) (hm : u - v ∉ L.lattice) :
    zeta L (u + v) - zeta L u - zeta L v = chordSlope L u v / 2 := by
  have neg_mem' : ∀ {x : ℂ}, -x ∈ L.lattice ↔ x ∈ L.lattice := fun {x} =>
    ⟨fun h => by simpa using neg_mem h, fun h => neg_mem h⟩
  have hu' : u ∈ goodSet L v := ⟨hu, hp, hm⟩
  -- `−u ∈ S_v`
  have hnu : -u ∈ goodSet L v := ⟨by rwa [neg_mem'], by rwa [show -u + v = -(u - v) by ring,
    neg_mem'], by rwa [show -u - v = -(u + v) by ring, neg_mem']⟩
  -- `v, −v ∈ S_{−u}`
  have hnu0 : -u ∉ L.lattice := by rwa [neg_mem']
  have hv' : v ∈ goodSet L (-u) := ⟨hv, by rwa [show v + -u = -(u - v) by ring, neg_mem'],
    by rwa [show v - -u = u + v by ring]⟩
  have hnv : -v ∈ goodSet L (-u) := ⟨by rwa [neg_mem'], by rwa [show -v + -u = -(u + v) by ring,
    neg_mem'], by rwa [show -v - -u = u - v by ring]⟩
  have e1 := zetaDefect_eq_of_mem L hu' hnu hv
  have e2 := zetaDefect_eq_of_mem L hv' hnv hnu0
  have e3 : zetaDefect L u v = -zetaDefect L u v := by
    calc zetaDefect L u v = zetaDefect L (-u) v := e1
      _ = zetaDefect L v (-u) := zetaDefect_comm L _ _
      _ = zetaDefect L (-v) (-u) := e2
      _ = zetaDefect L (-u) (-v) := zetaDefect_comm L _ _
      _ = -zetaDefect L u v := zetaDefect_neg L _ _
  have h0 : zetaDefect L u v = 0 := by linear_combination e3 / 2
  unfold zetaDefect at h0
  linear_combination h0

/-- The `ζ` addition formula in the form `ζ(u + v) = ζ(u) + ζ(v) + c`,
`c = (℘'(u) − ℘'(v)) / (2 (℘(u) − ℘(v)))`. -/
theorem zeta_add_eq {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice)
    (hp : u + v ∉ L.lattice) (hm : u - v ∉ L.lattice) :
    zeta L (u + v) = zeta L u + zeta L v + (℘'[L] u - ℘'[L] v) / (2 * (℘[L] u - ℘[L] v)) := by
  have h := zeta_add_formula L hu hv hp hm
  unfold chordSlope at h
  rw [mul_comm, ← div_div]
  linear_combination h

end LSG.Elliptic
