/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.MainAux
import LSG.MEB.MainGrp
import LSG.MEB.WustAlgB

/-!
# The inputs of the assembly that are not yet proved (A4.5, α): subgroup layer and Wüstholz

`LSG.MEB.Main` proves `MultEstB` from `MEBInputs`. These are **explicit hypotheses, not axioms**: the statements β's
subgroup layer (A4.3) and the sliced Wüstholz lemma (A4.4) must deliver, in exactly the form the assembly consumes.
STAGE_A4 §7.2 lists them with owners. ME analogues in brackets.

For a Zariski-closed subgroup `H` (in the assembly, the stabiliser `stabG V`), `SubgroupData cL H` bundles:
* `O : ObstrDataB`, whose `O.grp` is the identity component `H⁰` [`ObstrData.ofSubgroup`, `H0`];
* `grp_le : H⁰ ⊆ H` [`H0_subset`], `cosets`: finitely many cosets of `H⁰` cover `H` [`finite_cosets_H0`].
  Not inputs: irreducibility of `H⁰` (ME's `vanish_H0_isPrime`) is `MainGrp.vanish_grp_isPrime`, and properness
  (ME's `ObstrData.ofSubgroup_proper`) follows from `grp_le` and `ObstrDataB.expG_mem`;
* `hdim : hdim I(H⁰) = dim T_{H⁰} + m` [`hdim_H0`];
* `coset_ge`: the sliced Hilbert lower bound for a coset of `H⁰`, constant `cL` [`hfun_P_coset_ge`, `4^m`];
* `tz`: the tangent-space bound `TZProp O` at every point of every coset of `H⁰` [`mem_TZ_iff`]; the sliced
  Wüstholz lemma [`wustholz_cosets_sl`] follows from it (`LSG.MEB.wust_of_tz`).

`MEBInputs`: for every family `B` a constant `cL > 0` (independent of `H`) and `SubgroupData cL H` for every
Zariski-closed subgroup `H`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata)

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

variable (d₀ d₁ B) in
/-- **The subgroup layer for one Zariski-closed subgroup `H`** (inputs of the assembly). -/
structure SubgroupData (cL : ℕ) (H : Set (GPt d₀ d₁ B)) where
  /-- the obstruction data of the identity component `H⁰ = O.grp` -/
  O : ObstrDataB d₀ d₁ B
  grp_le : O.grp ⊆ H
  cosets : ∃ Rc : Finset (GPt d₀ d₁ B), (∀ c ∈ Rc, c ∈ H) ∧ H ⊆ ⋃ c ∈ Rc, gtransl c O.grp
  /-- the Hilbert dimension of the multi-cone of `H⁰` -/
  hdim : ∀ D : Blk m → ℕ, (∀ i, 1 ≤ D i) → (hdata blk D ℂ (vanish O.grp)).1 = finrank ℂ O.tan + m
  /-- the sliced Hilbert lower bound for a coset of `H⁰` -/
  coset_ge : ∀ (α : Alpha B) (a : GPt d₀ d₁ B), (∀ k, lsl α k ∉ vanish (gtransl a O.grp)) →
    ∀ D₀ D₁ D₂ t : ℕ,
      (t * D₀ / finrank ℂ O.h0 + 1) ^ finrank ℂ O.h0 *
          (t * D₁ / (d₁ - finrank ℚ O.U) + 1) ^ (d₁ - finrank ℚ O.U) *
          (t * D₂ + 1) ^ finrank ℂ O.t ≤
        cL * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanishP Finset.univ α (gtransl a O.grp)) (2 * t)
  /-- the tangent-space bound at every point of every coset of `H⁰` (gives Wüstholz, `WustCosetB.wust_of_tz`) -/
  tz : TZProp O

/-- **The inputs of the assembly** (β's subgroup layer and the Wüstholz lemma), for every family of blocks. -/
def MEBInputs : Prop :=
  ∀ (d₀ d₁ m : ℕ) (B : Fin m → AbBlock), ∃ cL : ℕ, 0 < cL ∧
    ∀ H : Set (GPt d₀ d₁ B), IsSubgroupG H → IsZClosed H → Nonempty (SubgroupData d₀ d₁ B cL H)

end LSG.MEB
