/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.SigmaDef

/-!
# Quasi-periodicity of `ζ` and `σ`

For `ω` in the period lattice, `ζ(z + ω) - ζ(z)` is a constant `η(ω)` (the quasi-period), since
its derivative `-℘(z + ω) + ℘(z)` vanishes on the connected open set `ℂ ∖ Λ`. Consequently
`σ(z + ω) = c · exp (η(ω) z) σ(z)`, and evaluating at `z = -ω/2` (using that `σ` is odd) gives
`σ(z + ω) = -exp (η(ω) (z + ω/2)) σ(z)` when `ω/2 ∉ Λ`.

## Main results
* `LSG.Weierstrass.eta`: the quasi-period map `η : ℂ → ℂ` (meaningful on the lattice).
* `LSG.Weierstrass.zeta_add_eta`: `ζ(z + ω) = ζ(z) + η(ω)` for `ω ∈ Λ`, `z ∉ Λ`.
* `LSG.Weierstrass.eta_add`: `η` is additive on `Λ`.
* `LSG.Weierstrass.eta_eq_two_mul_zeta_half`: `η(ω) = 2 ζ(ω/2)` if `ω/2 ∉ Λ`.
* `LSG.Weierstrass.sigma_add_of_half_notMem`: `σ(z + ω) = -exp (η(ω) (z + ω/2)) σ(z)` if
  `ω ∈ Λ`, `ω/2 ∉ Λ`.
* `LSG.Weierstrass.sigma_add_ω₁`, `sigma_add_ω₂`: the two basis cases.
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

lemma countable_lattice : (L.lattice : Set ℂ).Countable := by
  have : Countable L.lattice := L.latticeEquivProd.injective.countable
  exact Set.countable_coe_iff.mp this

/-- The complement of the lattice is connected. -/
lemma isConnected_compl_lattice : IsConnected (L.lattice : Set ℂ)ᶜ :=
  Set.Countable.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
    (countable_lattice L)

lemma add_notMem_lattice {z ω : ℂ} (hz : z ∉ L.lattice) (hω : ω ∈ L.lattice) :
    z + ω ∉ L.lattice := fun h ↦ hz ((Submodule.add_mem_iff_left _ hω).mp h)

lemma zero_mem_lattice : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem

lemma ne_zero_of_notMem_lattice {z : ℂ} (hz : z ∉ L.lattice) : z ≠ 0 :=
  fun h ↦ hz (h ▸ zero_mem_lattice L)

/-- A function on `ℂ ∖ Λ` with vanishing derivative is constant there. -/
lemma eq_of_hasDerivAt_zero {g : ℂ → ℂ} (hg : ∀ z ∉ L.lattice, HasDerivAt g 0 z) {z w : ℂ}
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) : g z = g w :=
  (isOpen_compl_coe_lattice L).is_const_of_deriv_eq_zero
    (isConnected_compl_lattice L).isPreconnected
    (fun x hx ↦ (hg x hx).differentiableAt.differentiableWithinAt) (fun x hx ↦ (hg x hx).deriv)
    hz hw

/-! ### The quasi-periods of `ζ` -/

/-- The quasi-period `η(ω) = ζ(z + ω) - ζ(z)` (independent of `z ∉ Λ` when `ω ∈ Λ`); we use the
base point `z = ω₁/2`. -/
def eta (ω : ℂ) : ℂ := zeta L (L.ω₁ / 2 + ω) - zeta L (L.ω₁ / 2)

lemma hasDerivAt_zeta_add_sub {ω : ℂ} (hω : ω ∈ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (fun z ↦ zeta L (z + ω) - zeta L z) 0 z := by
  have h1 := (hasDerivAt_zeta L (add_notMem_lattice L hz hω)).comp_add_const z ω
  have h2 : HasDerivAt (fun z ↦ zeta L (z + ω) - zeta L z) (-℘[L] (z + ω) - -℘[L] z) z :=
    h1.sub (hasDerivAt_zeta L hz)
  have hp : ℘[L] (z + ω) = ℘[L] z := L.weierstrassP_add_coe z ⟨ω, hω⟩
  rwa [hp, sub_self] at h2

/-- `ζ(z + ω) = ζ(z) + η(ω)` for `ω ∈ Λ` and `z ∉ Λ`. -/
lemma zeta_add_eta {ω : ℂ} (hω : ω ∈ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    zeta L (z + ω) = zeta L z + eta L ω := by
  have : zeta L (z + ω) - zeta L z = zeta L (L.ω₁ / 2 + ω) - zeta L (L.ω₁ / 2) :=
    eq_of_hasDerivAt_zero L (g := fun z ↦ zeta L (z + ω) - zeta L z)
      (fun x hx ↦ hasDerivAt_zeta_add_sub L hω hx) hz L.ω₁_div_two_notMem_lattice
  rw [eta]
  linear_combination this

@[simp] lemma eta_zero : eta L 0 = 0 := by simp [eta]

/-- `η` is additive on the lattice. -/
lemma eta_add {ω ω' : ℂ} (hω : ω ∈ L.lattice) (hω' : ω' ∈ L.lattice) :
    eta L (ω + ω') = eta L ω + eta L ω' := by
  have h0 := L.ω₁_div_two_notMem_lattice
  have h1 := zeta_add_eta L (add_mem hω hω') h0
  have h2 := zeta_add_eta L hω' (add_notMem_lattice L h0 hω)
  have h3 := zeta_add_eta L hω h0
  rw [← add_assoc, h2, h3] at h1
  linear_combination -h1

lemma eta_neg {ω : ℂ} (hω : ω ∈ L.lattice) : eta L (-ω) = -eta L ω := by
  have := eta_add L hω (neg_mem hω)
  rw [add_neg_cancel, eta_zero] at this
  linear_combination -this

lemma eta_sub {ω ω' : ℂ} (hω : ω ∈ L.lattice) (hω' : ω' ∈ L.lattice) :
    eta L (ω - ω') = eta L ω - eta L ω' := by
  rw [sub_eq_add_neg, eta_add L hω (neg_mem hω'), eta_neg L hω', sub_eq_add_neg]

lemma eta_zsmul {ω : ℂ} (hω : ω ∈ L.lattice) (n : ℤ) : eta L (n * ω) = n * eta L ω := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℂ) * ω ∈ L.lattice := by
      simpa [zsmul_eq_mul] using L.lattice.smul_mem (n : ℤ) hω
    push_cast at ih ⊢
    rw [add_mul, one_mul, eta_add L hn hω, ih]; ring
  | pred n ih =>
    have hn : (-(n : ℂ)) * ω ∈ L.lattice := by
      simpa [zsmul_eq_mul] using L.lattice.smul_mem (-(n : ℤ)) hω
    push_cast at ih ⊢
    rw [sub_mul, one_mul, eta_sub L hn hω, ih]; ring

/-- `η(ω) = 2 ζ(ω/2)` when `ω/2 ∉ Λ`. -/
lemma eta_eq_two_mul_zeta_half {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) :
    eta L ω = 2 * zeta L (ω / 2) := by
  have hm : -(ω / 2) ∉ L.lattice := fun h ↦ hω2 (by simpa using neg_mem h)
  have := zeta_add_eta L hω hm
  rw [show -(ω / 2) + ω = ω / 2 by ring, zeta_neg] at this
  linear_combination -this

/-! ### Quasi-periodicity of `σ` -/

lemma hasDerivAt_sigma (z : ℂ) : HasDerivAt (sigma L) (deriv (sigma L) z) z :=
  (differentiable_sigma L z).hasDerivAt

/-- `σ(z + ω) = c · exp (η(ω) z) · σ(z)` for some constant `c`, for every `ω ∈ Λ`. -/
lemma exists_sigma_add {ω : ℂ} (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, ∀ z, sigma L (z + ω) = c * exp (eta L ω * z) * sigma L z := by
  let G : ℂ → ℂ := fun z ↦ sigma L (z + ω) * exp (-(eta L ω * z)) / sigma L z
  have hG : ∀ z ∉ L.lattice, HasDerivAt G 0 z := by
    intro z hz
    have hz' := add_notMem_lattice L hz hω
    have h1 := (hasDerivAt_sigma L (z + ω)).comp_add_const z ω
    have h2 : HasDerivAt (fun z ↦ exp (-(eta L ω * z))) (exp (-(eta L ω * z)) * -(eta L ω * 1))
        z := ((hasDerivAt_id' z).const_mul (eta L ω)).neg.cexp
    have h3 := (h1.mul h2).div (hasDerivAt_sigma L z) (sigma_ne_zero L hz)
    refine h3.congr_deriv ?_
    rw [deriv_sigma L hz', deriv_sigma L hz, zeta_add_eta L hω hz]
    simp only [Pi.mul_apply]
    ring
  refine ⟨G (L.ω₁ / 2), fun z ↦ ?_⟩
  by_cases hz : z ∈ L.lattice
  · rw [sigma_coe L ⟨z, hz⟩, sigma_coe L ⟨z + ω, add_mem hz hω⟩, mul_zero]
  · have := eq_of_hasDerivAt_zero L hG hz L.ω₁_div_two_notMem_lattice
    have h1 := sigma_ne_zero L hz
    have h2 : exp (-(eta L ω * z)) * exp (eta L ω * z) = 1 := by rw [← exp_add]; simp
    have h3 : sigma L (z + ω) * exp (-(eta L ω * z)) = G (L.ω₁ / 2) * sigma L z := by
      rw [← this]; simp only [G]; rw [div_mul_cancel₀ _ h1]
    calc sigma L (z + ω) = sigma L (z + ω) * (exp (-(eta L ω * z)) * exp (eta L ω * z)) := by
          rw [h2, mul_one]
      _ = (sigma L (z + ω) * exp (-(eta L ω * z))) * exp (eta L ω * z) := by ring
      _ = _ := by rw [h3]; ring

/-- `σ(z + ω) = -exp (η(ω) (z + ω/2)) σ(z)` for `ω ∈ Λ` with `ω/2 ∉ Λ`. -/
lemma sigma_add_of_half_notMem {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) (z : ℂ) :
    sigma L (z + ω) = -exp (eta L ω * (z + ω / 2)) * sigma L z := by
  obtain ⟨c, hc⟩ := exists_sigma_add L hω
  set e := eta L ω
  have hs := sigma_ne_zero L hω2
  have h := hc (-(ω / 2))
  rw [show -(ω / 2) + ω = ω / 2 by ring, sigma_neg] at h
  have he : exp (e * -(ω / 2)) * exp (e * (ω / 2)) = 1 := by rw [← exp_add]; ring_nf; simp
  have hce : c * exp (e * -(ω / 2)) = -1 := by
    have : sigma L (ω / 2) * (c * exp (e * -(ω / 2)) + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hs
    · linear_combination h'
  have hc' : c = -exp (e * (ω / 2)) := by linear_combination exp (e * (ω / 2)) * hce - c * he
  rw [hc z, hc', mul_add, exp_add]
  ring

lemma sigma_add_ω₁ (z : ℂ) :
    sigma L (z + L.ω₁) = -exp (eta L L.ω₁ * (z + L.ω₁ / 2)) * sigma L z :=
  sigma_add_of_half_notMem L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice z

lemma sigma_add_ω₂ (z : ℂ) :
    sigma L (z + L.ω₂) = -exp (eta L L.ω₂ * (z + L.ω₂ / 2)) * sigma L z :=
  sigma_add_of_half_notMem L L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice z

/-- The inverse form: `σ(z - ω) = -exp (-η(ω) (z - ω/2)) σ(z)` for `ω ∈ Λ`, `ω/2 ∉ Λ`. -/
lemma sigma_sub_of_half_notMem {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) (z : ℂ) :
    sigma L (z - ω) = -exp (-(eta L ω * (z - ω / 2))) * sigma L z := by
  have h := sigma_add_of_half_notMem L hω hω2 (z - ω)
  rw [sub_add_cancel, show z - ω + ω / 2 = z - ω / 2 by ring] at h
  have : exp (-(eta L ω * (z - ω / 2))) * exp (eta L ω * (z - ω / 2)) = 1 := by
    rw [← exp_add]; simp
  linear_combination exp (-(eta L ω * (z - ω / 2))) * h - sigma L (z - ω) * this

end LSG.Weierstrass
