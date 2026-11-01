/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.StmtG
import LSG.MEBV.SliceDim

/-!
# The inputs of the assembly that are not proved in the α core: the subgroup layer (M2.5 α; template
`LSG.MEB.MainHyp`)

`LSG.MEBV.Main` proves `MultEstGV` (hence, by `MainPush`, `MultEstV`) from `MEBVInputs`. These are **explicit
hypotheses, not axioms**: the statements the subgroup layer (β′) must deliver, in exactly the form the assembly
consumes. ME/MEB analogues in brackets.

For a Zariski-closed subgroup `H` (in the assembly, the stabiliser `stabG V`), `SubgroupDataV cL H` bundles:
* `O : ObstrDataGV`, whose `O.grp` is the identity component `H⁰` [`ObstrData.ofSubgroup`, `H0`];
* `grp_le : H⁰ ⊆ H`, `cosets`: finitely many cosets of `H⁰` cover `H` [`H0_subset`, `finite_cosets_H0`];
* **`lie_le`**: every one-parameter subgroup `exp(ℂ v) ⊆ H` has `v ∈ T_{H⁰}` [`lieAlg_H0`]. New compared with MEB:
  the assembly uses it for the symmetries `Kv ⊆ T_{H⁰}` (`MultEstGV`, the push-out);
* `hdim : hdim I(H⁰) = dim T_{H⁰} + m` [`hdim_H0`];
* `coset_ge`: the sliced Hilbert lower bound for a coset of `H⁰`, constant `cL`, with W88's projection exponents
  `t₀ = ex0 T′`, `t₁ = d₁ − dim U`, `t₂ = ex2 T′` [`hfun_P_coset_ge`];
* `tz`: the tangent-space bound `TZPropV O` at every point of every coset of `H⁰` [`mem_TZ_iff`]; the sliced
  Wüstholz lemma follows from it (β's `wust_of_tz`, as `LSG.MEB.wust_of_tz`).

Irreducibility of `H⁰` is not an input (`MainGrp.vanish_grp_isPrime`), nor is properness.

`MEBVInputs`: for every family `B` a constant `cL > 0` (independent of `H`) and `SubgroupDataV cL H` for every
Zariski-closed subgroup `H`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata)

namespace LSG.MEBV

open LSG.MEB (Blk DfunB)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- **The tangent-space bound** at every point of every coset of `O.grp`: a direction `w` along which every
multihomogeneous polynomial vanishing on `g + O.grp` has zero derivative at a lift `u` of `g` lies in `O.tan`. -/
def TZPropV (O : ObstrDataGV d₀ d₁ B) : Prop :=
  ∀ (g : GPt d₀ d₁ B) (u : Tan d₀ d₁ B), expG d₀ d₁ B u = g → ∀ w : Tan d₀ d₁ B,
    (∀ (P : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ), IsHomV P d →
      P ∈ vanish (gtransl g O.grp) → deriv (fun r : ℂ => eval (liftV (u + r • w)) P) 0 = 0) →
    w ∈ O.tan

variable (d₀ d₁ B) in
/-- **The subgroup layer for one Zariski-closed subgroup `H`** (inputs of the assembly). -/
structure SubgroupDataV (cL : ℕ) (H : Set (GPt d₀ d₁ B)) where
  /-- the obstruction data of the identity component `H⁰ = O.grp` -/
  O : ObstrDataGV d₀ d₁ B
  grp_le : O.grp ⊆ H
  cosets : ∃ Rc : Finset (GPt d₀ d₁ B), (∀ c ∈ Rc, c ∈ H) ∧ H ⊆ ⋃ c ∈ Rc, gtransl c O.grp
  /-- one-parameter subgroups of `H` lie in `H⁰` (the Lie algebra of `H` is `T_{H⁰}`) -/
  lie_le : ∀ v : Tan d₀ d₁ B, (∀ c : ℂ, expG d₀ d₁ B (c • v) ∈ H) → v ∈ O.tan
  /-- the Hilbert dimension of the multi-cone of `H⁰` -/
  hdim : ∀ D : Blk m → ℕ, (∀ i, 1 ≤ D i) → (hdata blk D ℂ (vanish O.grp)).1 = finrank ℂ O.tan + m
  /-- the sliced Hilbert lower bound for a coset of `H⁰` -/
  coset_ge : ∀ (α : Alpha B) (a : GPt d₀ d₁ B), (∀ k, lsl α k ∉ vanish (gtransl a O.grp)) →
    ∀ D₀ D₁ D₂ t : ℕ,
      (t * D₀ / ex0 O.tan + 1) ^ ex0 O.tan *
          (t * D₁ / (d₁ - finrank ℚ O.U) + 1) ^ (d₁ - finrank ℚ O.U) *
          (t * D₂ + 1) ^ ex2 O.tan ≤
        cL * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanishP Finset.univ α (gtransl a O.grp)) (2 * t)
  /-- the tangent-space bound at every point of every coset of `H⁰` (gives Wüstholz) -/
  tz : TZPropV O

/-- **The inputs of the assembly** (the subgroup layer), for every family of blocks. -/
def MEBVInputs : Prop :=
  ∀ (d₀ d₁ m : ℕ) (B : Fin m → VBlock), ∃ cL : ℕ, 0 < cL ∧
    ∀ H : Set (GPt d₀ d₁ B), IsSubgroupG H → IsZClosed H → Nonempty (SubgroupDataV d₀ d₁ B cL H)

end LSG.MEBV
