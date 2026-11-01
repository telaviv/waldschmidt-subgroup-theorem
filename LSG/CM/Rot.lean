/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.StatementVec
import LSG.Weierstrass.Legendre

/-!
# Rotations of a CM lattice: `ζ(αz) = α⁻¹ ζ(z)`, `℘(αz) = α⁻² ℘(z)`, `η(αλ) = α⁻¹ η(λ)`

For a unit `α` with `αΛ = Λ` (`IsLatUnit`), reindexing the lattice sums of `ζ` and `℘` along
`l ↦ α l` gives the rotation formulas (`zeta_mul`, `weierstrassP_mul`, `eta_mul`).

`CMData L α`: the period pair is `(ω₁, α ω₁)` with `αΛ = Λ`, `ᾱ = α⁻¹`, `Im α > 0`, `α ∈ ℚ̄`.
Then every lattice point is `(m + nα) ω₁`, `η((m + nα)ω₁) = (m + nᾱ) η(ω₁)` (`eta_eq_conj`), and
Legendre's relation reads `η(ω₁) ω₁ (α − α⁻¹) = 2πi` (`eta_one_mul`), so `η(ω₁) ≠ 0`.
-/

open Complex LSG.Weierstrass PeriodPair

namespace LSG.CM

variable (L : PeriodPair) {α : ℂ}

/-- `α` permutes the lattice. -/
structure IsLatUnit (L : PeriodPair) (α : ℂ) : Prop where
  ne : α ≠ 0
  mul_mem : ∀ x ∈ L.lattice, α * x ∈ L.lattice
  inv_mul_mem : ∀ x ∈ L.lattice, α⁻¹ * x ∈ L.lattice

/-- Multiplication by `α` as a permutation of the lattice. -/
noncomputable def latEquiv (h : IsLatUnit L α) : L.lattice ≃ L.lattice where
  toFun l := ⟨α * l, h.mul_mem _ l.2⟩
  invFun l := ⟨α⁻¹ * l, h.inv_mul_mem _ l.2⟩
  left_inv l := by ext; simp [← mul_assoc, inv_mul_cancel₀ h.ne]
  right_inv l := by ext; simp [← mul_assoc, mul_inv_cancel₀ h.ne]

lemma zetaSummand_mul (hα : α ≠ 0) (l z : ℂ) :
    zetaSummand (α * l) (α * z) = α⁻¹ * zetaSummand l z := by
  unfold zetaSummand
  rw [← mul_sub, mul_pow]
  simp only [mul_inv, div_eq_mul_inv]
  have : (α ^ 2)⁻¹ = α⁻¹ * α⁻¹ := by rw [sq, mul_inv]
  rw [this]
  field_simp

/-- **`ζ(αz) = α⁻¹ ζ(z)`** when `αΛ = Λ`. -/
theorem zeta_mul (h : IsLatUnit L α) (z : ℂ) : zeta L (α * z) = α⁻¹ * zeta L z := by
  calc zeta L (α * z) = ∑' l : L.lattice, zetaSummand ((latEquiv L h l : L.lattice) : ℂ) (α * z) :=
        ((latEquiv L h).tsum_eq (fun l : L.lattice => zetaSummand (l : ℂ) (α * z))).symm
    _ = ∑' l : L.lattice, α⁻¹ * zetaSummand (l : ℂ) z := by
        congr 1 with l
        exact zetaSummand_mul h.ne _ _
    _ = α⁻¹ * zeta L z := tsum_mul_left

/-- **`℘(αz) = α⁻² ℘(z)`** when `αΛ = Λ`. -/
theorem weierstrassP_mul (h : IsLatUnit L α) (z : ℂ) :
    L.weierstrassP (α * z) = (α ^ 2)⁻¹ * L.weierstrassP z := by
  unfold PeriodPair.weierstrassP
  calc ∑' l : L.lattice, (1 / (α * z - l) ^ 2 - 1 / (l : ℂ) ^ 2)
      = ∑' l : L.lattice, (1 / (α * z - ((latEquiv L h l : L.lattice) : ℂ)) ^ 2 -
          1 / ((latEquiv L h l : L.lattice) : ℂ) ^ 2) :=
        ((latEquiv L h).tsum_eq (fun l : L.lattice => 1 / (α * z - l) ^ 2 - 1 / (l : ℂ) ^ 2)).symm
    _ = ∑' l : L.lattice, (α ^ 2)⁻¹ * (1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2) := by
        congr 1 with l
        change 1 / (α * z - α * l) ^ 2 - 1 / (α * l) ^ 2 = _
        rw [← mul_sub, mul_pow, mul_pow]
        simp only [one_div, mul_inv]
        ring
    _ = _ := tsum_mul_left

/-- **`η(αλ) = α⁻¹ η(λ)`** on the lattice. -/
theorem eta_mul (h : IsLatUnit L α) {ω : ℂ} (hω : ω ∈ L.lattice) :
    eta L (α * ω) = α⁻¹ * eta L ω := by
  rw [← LSG.W88.Vec.zeta_of_mem_lattice L (h.mul_mem _ hω), ← LSG.W88.Vec.zeta_of_mem_lattice L hω,
    zeta_mul L h]

/-! ### CM data -/

/-- A period pair `(ω₁, α ω₁)` of a CM lattice with `αΛ = Λ`, `|α| = 1`, `Im α > 0`, `α ∈ ℚ̄`. -/
structure CMData (L : PeriodPair) (α : ℂ) : Prop where
  unit : IsLatUnit L α
  hω : L.ω₂ = α * L.ω₁
  conj_eq : starRingEnd ℂ α = α⁻¹
  im_pos : 0 < α.im
  alg : IsAlgebraic ℚ α

namespace CMData

variable {L} (hd : CMData L α)
include hd

set_option linter.unusedSectionVars false in
lemma ω₁_ne : L.ω₁ ≠ 0 := ω₁_ne_zero L

lemma ne_inv : α - α⁻¹ ≠ 0 := by
  rw [← hd.conj_eq, sub_ne_zero]
  intro h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith [hd.im_pos]

/-- Every lattice point is `(m + nα) ω₁`. -/
lemma mem_lattice_iff {x : ℂ} : x ∈ L.lattice ↔ ∃ m n : ℤ, x = (m + n * α) * L.ω₁ := by
  rw [PeriodPair.mem_lattice, hd.hω]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩

lemma div_eq {x : ℂ} (hx : x ∈ L.lattice) : ∃ m n : ℤ, x / L.ω₁ = m + n * α := by
  obtain ⟨m, n, rfl⟩ := hd.mem_lattice_iff.mp hx
  exact ⟨m, n, by field_simp [hd.ω₁_ne]⟩

lemma isAlgebraic_div {x : ℂ} (hx : x ∈ L.lattice) : IsAlgebraic ℚ (x / L.ω₁) := by
  obtain ⟨m, n, h⟩ := hd.div_eq hx
  rw [h]
  exact (isAlgebraic_intCast m).add ((isAlgebraic_intCast n).mul hd.alg)

/-- **`η((m + nα) ω₁) = (m + nᾱ) η(ω₁)`**: `η(x) = conj(x/ω₁) η(ω₁)` on the lattice. -/
theorem eta_eq_conj {x : ℂ} (hx : x ∈ L.lattice) :
    eta L x = starRingEnd ℂ (x / L.ω₁) * eta L L.ω₁ := by
  obtain ⟨m, n, hmn⟩ := hd.mem_lattice_iff.mp hx
  have h1 : x / L.ω₁ = m + n * α := by rw [hmn]; field_simp [hd.ω₁_ne]
  have hx' : x = (m : ℂ) * L.ω₁ + (n : ℂ) * (α * L.ω₁) := by rw [hmn]; ring
  have hm : (m : ℂ) * L.ω₁ ∈ L.lattice := intCast_mul_mem L L.ω₁_mem_lattice m
  have hαω : α * L.ω₁ ∈ L.lattice := hd.unit.mul_mem _ L.ω₁_mem_lattice
  have hn : (n : ℂ) * (α * L.ω₁) ∈ L.lattice := intCast_mul_mem L hαω n
  rw [h1, hx', eta_add L hm hn, eta_zsmul L L.ω₁_mem_lattice, eta_zsmul L hαω,
    eta_mul L hd.unit L.ω₁_mem_lattice, map_add, map_mul, map_intCast, map_intCast,
    hd.conj_eq]
  ring

/-- **Legendre for CM lattices**: `η(ω₁) ω₁ (α − α⁻¹) = 2πi`. -/
theorem eta_one_mul : eta L L.ω₁ * L.ω₁ * (α - α⁻¹) = 2 * Real.pi * I := by
  have hpos : 0 < (L.ω₂ / L.ω₁).im := by
    rw [hd.hω, mul_div_cancel_right₀ _ hd.ω₁_ne]; exact hd.im_pos
  have h := legendre_of_im_pos L hpos
  rw [hd.hω, eta_mul L hd.unit L.ω₁_mem_lattice] at h
  linear_combination h

lemma eta_one_ne : eta L L.ω₁ ≠ 0 := by
  intro h0
  have := hd.eta_one_mul
  rw [h0, zero_mul, zero_mul] at this
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  exact (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero) this.symm

lemma lattice_smul_mem {x : ℂ} (hx : x ∈ L.lattice) : α * x ∈ L.lattice := hd.unit.mul_mem x hx

end CMData

end LSG.CM
