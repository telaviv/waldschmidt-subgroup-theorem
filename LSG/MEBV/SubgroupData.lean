/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.CosetGe

/-!
# The subgroup layer: `MEBVInputs` (M2.5 β′; template `LSG.MEB.SubgroupData`)

For a Zariski-closed subgroup `H ⊆ G̃`:
* **`ObstrDataGV.ofSubgroupV hH hc`**: `U = UOf H`, `t = tOf H` (rational, `isRatSub_tOf`), `Γ = gamOf H`,
  `grp = H⁰`; `grp_eq` and `lie` from the classification `lieAlg H = tanOfV Γ U t` (`lieAlg_eq_tanV`) and
  `lieAlg_H0`; `htil` from `htil_H0`. **`ofSubgroupV_tan`**: `O.tan = lieAlg H`.
* **`SubgroupDataV.ofSubgroupV hH hc`**: every field (`grp_le`, `cosets`, `lie_le`, `hdim`, `coset_ge`, `tz`),
  constant `cL = cCG B (cHV B)` (depends only on `d₀, d₁, B`).
* **`mebvInputs : MEBVInputs`**.
-/

open MvPolynomial Module
open StrongSix.M2 (hdata)

namespace LSG.MEBV

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock} {H : Set (GPt d₀ d₁ B)}

theorem H0_eq_zcl_tanOfV (hH : IsSubgroupG H) (hc : IsZClosed H) :
    H0 hH = zcl (expG d₀ d₁ B '' (tanOfV d₀ d₁ B (gamOf hH) (UOf hH) (tOf hH) : Set (Tan d₀ d₁ B))) := by
  rw [← lieAlg_eq_tanV hH hc]; rfl

/-- **The obstruction data of the identity component of `H`.** -/
noncomputable def ObstrDataGV.ofSubgroupV (hH : IsSubgroupG H) (hc : IsZClosed H) : ObstrDataGV d₀ d₁ B where
  U := UOf hH
  t := tOf hH
  t_rat := isRatSub_tOf hH hc
  gam := gamOf hH
  grp := H0 hH
  grp_eq := H0_eq_zcl_tanOfV hH hc
  grp_sub := H0_isSubgroup hH
  grp_closed := isZClosed_H0 hH
  lie v := by
    rw [← lieAlg_eq_tanV hH hc, ← lieAlg_H0 hH hc]
    exact Iff.rfl
  htil u hu := by
    have := htil_H0 hH hc hu
    rwa [lieAlg_eq_tanV hH hc] at this

@[simp] theorem ofSubgroupV_grp (hH : IsSubgroupG H) (hc : IsZClosed H) :
    (ObstrDataGV.ofSubgroupV hH hc).grp = H0 hH := rfl

theorem ofSubgroupV_tan (hH : IsSubgroupG H) (hc : IsZClosed H) :
    (ObstrDataGV.ofSubgroupV hH hc).tan = lieAlg hH :=
  (lieAlg_eq_tanV hH hc).symm

/-- **The subgroup layer for `H`.** -/
noncomputable def SubgroupDataV.ofSubgroupV (hH : IsSubgroupG H) (hc : IsZClosed H) :
    SubgroupDataV d₀ d₁ B (cCG (d₀ := d₀) (d₁ := d₁) B (cHV B)) H where
  O := ObstrDataGV.ofSubgroupV hH hc
  grp_le := H0_subset hH hc
  cosets := finite_cosets_H0 hH hc
  lie_le v hv := by
    rw [ofSubgroupV_tan]
    exact hv
  hdim D hD := by
    rw [ofSubgroupV_tan]
    exact hdim_H0 hH hc D hD
  coset_ge := coset_ge_of_lowerV (h0LowerBoundV _)
  tz g u hu w h := by
    rw [ofSubgroupV_tan]
    exact tz_le_lieAlg hH hc g u hu w h

/-- **The inputs of the assembly** (the subgroup layer), for every family of blocks. -/
theorem mebvInputs : MEBVInputs := fun d₀ d₁ _ B =>
  ⟨cCG (d₀ := d₀) (d₁ := d₁) B (cHV B), cCG_pos one_le_cHV,
    fun _ hH hc => ⟨SubgroupDataV.ofSubgroupV hH hc⟩⟩

end LSG.MEBV
