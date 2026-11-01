/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.SubgroupHtil
import LSG.MEB.CosetGe

/-!
# The subgroup layer, assembled (A4.3, β″): `ObstrDataB.ofSubgroup` and `SubgroupData`

For a Zariski-closed subgroup `H` (`hH : IsSubgroupG H`, `hc : IsZClosed H`):

* **`ObstrDataB.ofSubgroup hH hc`**: `h0 = h0Of hH`, `U = UOf hH`, `t = tOf hH` (`SubgroupGraph`), `grp = H0 hH`.
  Simp lemmas `ofSubgroup_grp`, `ofSubgroup_h0`, `ofSubgroup_U`, `ofSubgroup_t`, **`ofSubgroup_tan`**
  (`O.tan = lieAlg hH`).
* **`ofSubgroup_tz`** (`TZProp`), **`ofSubgroup_hdim`** (the field `hdim`).
* `CosetGeB O cL`: the statement of the field `SubgroupData.coset_ge`.
* **`SubgroupData.ofSubgroup hH hc (hcg : CosetGeB (ObstrDataB.ofSubgroup hH hc) cL)`**: every field except
  `coset_ge` is built here; **`SubgroupData.ofLower`** takes α's `H0LowerBound` instead (constant
  `cH · nLaw B · 2^m`, via `coset_ge_of_lower`).
* **`mebInputs_of_lower`**: `MEBInputs` from a lower bound `H0LowerBound O cH` for every obstruction data `O`
  (`cH > 0` depending only on `B`), which is the form of α's `h0LowerBound`.
-/

open MvPolynomial Module
open StrongSix.M2 (hfun hdata)

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock} {H : Set (GPt d₀ d₁ B)}

theorem H0_eq_zcl_tanOf (hH : IsSubgroupG H) (hc : IsZClosed H) :
    H0 hH = zcl (expG d₀ d₁ B '' (tanOf (h0Of hH) (UOf hH) (tOf hH) : Set (Tan d₀ d₁ B))) := by
  rw [← lieAlg_eq_tanOf hH hc]; rfl

theorem lieAlg_H0_eq_tanOf (hH : IsSubgroupG H) (hc : IsZClosed H) :
    lieAlg (H0_isSubgroup hH) = tanOf (h0Of hH) (UOf hH) (tOf hH) := by
  rw [lieAlg_H0 hH hc, lieAlg_eq_tanOf hH hc]

/-- **The obstruction data of the identity component `H⁰`.** -/
noncomputable def ObstrDataB.ofSubgroup (hH : IsSubgroupG H) (hc : IsZClosed H) : ObstrDataB d₀ d₁ B where
  h0 := h0Of hH
  U := UOf hH
  t := tOf hH
  t_rat := isRatSub_tOf hH hc
  grp := H0 hH
  grp_eq := H0_eq_zcl_tanOf hH hc
  grp_sub := H0_isSubgroup hH
  grp_closed := isZClosed_H0 hH
  lie v := by
    rw [← lieAlg_H0_eq_tanOf hH hc]
    exact Iff.rfl
  htil u hu := htil_of_zcl (H0_eq_zcl_tanOf hH hc) (H0_isSubgroup hH)
    (fun z => by rw [lieAlg_H0 hH hc]; exact Iff.rfl) hu

namespace ObstrDataB

@[simp] theorem ofSubgroup_grp (hH : IsSubgroupG H) (hc : IsZClosed H) : (ofSubgroup hH hc).grp = H0 hH := rfl
@[simp] theorem ofSubgroup_h0 (hH : IsSubgroupG H) (hc : IsZClosed H) : (ofSubgroup hH hc).h0 = h0Of hH := rfl
@[simp] theorem ofSubgroup_U (hH : IsSubgroupG H) (hc : IsZClosed H) : (ofSubgroup hH hc).U = UOf hH := rfl
@[simp] theorem ofSubgroup_t (hH : IsSubgroupG H) (hc : IsZClosed H) : (ofSubgroup hH hc).t = tOf hH := rfl

/-- **`T_{H⁰} = lieAlg H`.** -/
@[simp] theorem ofSubgroup_tan (hH : IsSubgroupG H) (hc : IsZClosed H) : (ofSubgroup hH hc).tan = lieAlg hH :=
  (lieAlg_eq_tanOf hH hc).symm

/-- The field `SubgroupData.tz`. -/
theorem ofSubgroup_tz (hH : IsSubgroupG H) (hc : IsZClosed H) : TZProp (ofSubgroup hH hc) := by
  intro g u hu w h
  rw [ofSubgroup_tan]
  exact tz_le_lieAlg hH hc g u hu w h

/-- The field `SubgroupData.hdim`. -/
theorem ofSubgroup_hdim (hH : IsSubgroupG H) (hc : IsZClosed H) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (hdata blk D ℂ (vanish (ofSubgroup hH hc).grp)).1 = finrank ℂ (ofSubgroup hH hc).tan + m := by
  rw [ofSubgroup_tan]
  exact hdim_H0 hH hc D hD

end ObstrDataB

/-- The statement of the field `SubgroupData.coset_ge` (the sliced Hilbert lower bound on a coset of `O.grp`). -/
def CosetGeB (O : ObstrDataB d₀ d₁ B) (cL : ℕ) : Prop :=
  ∀ (α : Alpha B) (a : GPt d₀ d₁ B), (∀ k, lsl α k ∉ vanish (gtransl a O.grp)) →
    ∀ D₀ D₁ D₂ t : ℕ,
      (t * D₀ / finrank ℂ O.h0 + 1) ^ finrank ℂ O.h0 *
          (t * D₁ / (d₁ - finrank ℚ O.U) + 1) ^ (d₁ - finrank ℚ O.U) *
          (t * D₂ + 1) ^ finrank ℂ O.t ≤
        cL * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanishP Finset.univ α (gtransl a O.grp)) (2 * t)

/-- **`SubgroupData` for `H`, given the field `coset_ge`.** -/
noncomputable def SubgroupData.ofSubgroup (hH : IsSubgroupG H) (hc : IsZClosed H) {cL : ℕ}
    (hcg : CosetGeB (ObstrDataB.ofSubgroup hH hc) cL) : SubgroupData d₀ d₁ B cL H where
  O := ObstrDataB.ofSubgroup hH hc
  grp_le := H0_subset hH hc
  cosets := finite_cosets_H0 hH hc
  hdim := ObstrDataB.ofSubgroup_hdim hH hc
  coset_ge := hcg
  tz := ObstrDataB.ofSubgroup_tz hH hc

@[simp] theorem SubgroupData.ofSubgroup_O (hH : IsSubgroupG H) (hc : IsZClosed H) {cL : ℕ}
    (hcg : CosetGeB (ObstrDataB.ofSubgroup hH hc) cL) :
    (SubgroupData.ofSubgroup hH hc hcg).O = ObstrDataB.ofSubgroup hH hc := rfl

/-- **`SubgroupData` for `H`, given α's unsliced lower bound for `H⁰`** (constant `cH · nLaw B · 2^m`). -/
noncomputable def SubgroupData.ofLower (hH : IsSubgroupG H) (hc : IsZClosed H) {cH : ℕ}
    (hlow : H0LowerBound (ObstrDataB.ofSubgroup hH hc) cH) :
    SubgroupData d₀ d₁ B (cH * nLaw B * 2 ^ m) H :=
  SubgroupData.ofSubgroup hH hc (coset_ge_of_lower hlow)

/-- **`MEBInputs` from a uniform unsliced lower bound** (α's `h0LowerBound : H0LowerBound O (cHB B)` has this form,
with `cH = cHB B ≥ 1`). -/
theorem mebInputs_of_lower
    (hlow : ∀ (d₀ d₁ m : ℕ) (B : Fin m → AbBlock), ∃ cH : ℕ, 0 < cH ∧
      ∀ O : ObstrDataB d₀ d₁ B, H0LowerBound O cH) : MEBInputs := by
  intro d₀ d₁ m B
  obtain ⟨cH, hcH, h⟩ := hlow d₀ d₁ m B
  refine ⟨cH * nLaw B * 2 ^ m, by have := nLaw_pos (B := B); positivity, fun H hH hc => ?_⟩
  exact ⟨SubgroupData.ofLower hH hc (h _)⟩

end LSG.MEB
