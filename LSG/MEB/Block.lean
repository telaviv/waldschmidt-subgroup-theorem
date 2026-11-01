/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Abelian blocks: the interface of the generic multiplicity estimate (STAGE_A4 §1.2, §2.1, frozen in A4.0)

An **abelian block** is a complex torus `ℂ^g ⧸ per` with an explicit projective model in `ℙ^{N−1}`, given through
the data the multiplicity estimate of `LSG.MEB` consumes. The block is described *semantically*:
* an entire, nowhere-zero lift `θ : ℂ^g → ℂ^N ∖ 0` of the exponential, landing on the explicit model;
* a finite family of addition laws of bidegree `(2, 2)` that are correct and complete **on the image of `θ`**;
* chart flows that `θ` satisfies (for Wüstholz's polynomial derivations).

On the model side it carries two certificates in projective form, which are all the Bézout layer needs:
* a Hilbert certificate (B6: `S_n = (y)·S_{n−1} + I_n` from degree `hilb_deg` on);
* a local-complete-intersection certificate (B5: local systems `(S_i, F_i)` with a cover).

The fields are grouped as in STAGE_A4 §2.1. The A-block (`Jac(y² = 4x⁵ + 1)`) instance is `LSG.JacBlock.aBlock`
(stage A4.6). `LSG.MEB.Sanity.pointBlock` checks that the interface is satisfiable.

* `IsRatSub Λ t`: `t ∩ Λ` spans `t` over `ℝ` (W88's `IsAbelianTangent` for an arbitrary lattice).
* `biW N`: the bidegree weights on `Fin N ⊕ Fin N` (first copy `(1,0)`, second copy `(0,1)`).
* `evalLaw L X Y`: the value of a law `L` at `(X, Y)`.
* `AbBlock`: the structure.
-/

open MvPolynomial

namespace LSG.MEB

/-- **Rationality for a lattice**: `t ∩ Λ` spans `t` over `ℝ` (for `Λ` a lattice, `t` is then the tangent space of a
complex subtorus). -/
def IsRatSub {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
    (Λ : AddSubgroup V) (t : Submodule ℂ V) : Prop :=
  (t.restrictScalars ℝ : Submodule ℝ V) = Submodule.span ℝ {z | z ∈ t ∧ z ∈ Λ}

/-- The bidegree weights on the variables `Fin N ⊕ Fin N` of an addition law. -/
def biW (N : ℕ) : Fin N ⊕ Fin N → ℕ × ℕ := Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))

/-- The value of a law `L = (L_k)_k` at `(X, Y)`. -/
noncomputable def evalLaw {N : ℕ} (L : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℂ) (X Y : Fin N → ℂ) :
    Fin N → ℂ :=
  fun k => eval (Sum.elim X Y) (L k)

/-- **An abelian block** (STAGE_A4 §1.2). -/
structure AbBlock where
  /-- the dimension of the torus -/
  g : ℕ
  /-- the number of projective coordinates of the model -/
  N : ℕ
  -- The explicit model
  /-- homogeneous generators of the explicit ideal `I^expl` (A-block: 9 quadrics and 3 cubics) -/
  gens : List (MvPolynomial (Fin N) ℂ)
  gens_hom : ∀ Q ∈ gens, ∃ d, 1 ≤ d ∧ Q.IsHomogeneous d
  -- Uniformisation
  /-- the entire lift of the exponential (A-block: `θ_N`, `LSG.JacAn.ThetaData.thetaN`) -/
  θ : (Fin g → ℂ) → Fin N → ℂ
  θ_analytic : ∀ z, AnalyticAt ℂ θ z
  θ_ne : ∀ z, θ z ≠ 0
  θ_model : ∀ z, ∀ Q ∈ gens, eval (θ z) Q = 0
  /-- the kernel of the exponential (A-block: `LSG.JacAn.kerE`) -/
  per : AddSubgroup (Fin g → ℂ)
  per_discrete : DiscreteTopology per
  per_span : Submodule.span ℝ (per : Set (Fin g → ℂ)) = ⊤
  θ_per : ∀ ω ∈ per, ∀ z, ∃ c : ℂ, c ≠ 0 ∧ θ (z + ω) = c • θ z
  θ_ker : ∀ z w, (∃ c : ℂ, θ w = c • θ z) → w - z ∈ per
  -- Surjectivity: the zero set of `gens` is the cone over the image (STAGE_A4 §2.2)
  surj : ∀ X : Fin N → ℂ, X ≠ 0 → (∀ Q ∈ gens, eval X Q = 0) → ∃ z, ∃ c : ℂ, X = c • θ z
  -- Addition laws, correct and complete on the image
  /-- the number of laws (A-block: 9, the columns of `A32`) -/
  nL : ℕ
  law : Fin nL → Fin N → MvPolynomial (Fin N ⊕ Fin N) ℂ
  law_hom : ∀ i k, (law i k).IsWeightedHomogeneous (biW N) ((2, 2) : ℕ × ℕ)
  law_eq : ∀ i u v, ∃ κ : ℂ, evalLaw (law i) (θ u) (θ v) = κ • θ (u + v)
  law_complete : ∀ u v, ∃ i, evalLaw (law i) (θ u) (θ v) ≠ 0
  -- Chart flows (Wüstholz derivations, Zariski tangent spaces)
  /-- the charts used (A-block: `{0, 4, 8}`) -/
  charts : Finset (Fin N)
  chart_cover : ∀ X : Fin N → ℂ, X ≠ 0 → (∀ Q ∈ gens, eval X Q = 0) → ∃ c ∈ charts, X c ≠ 0
  /-- the chart-`c` field: `W c j` is the `j`-th invariant vector field in the chart `X_c = 1` -/
  W : Fin N → Fin g → Fin N → MvPolynomial (Fin N) ℂ
  W_hom : ∀ c j l, (W c j l).IsHomogeneous 2
  W_chart : ∀ c j, W c j c = 0
  /-- the projective flow equation `θ_c ∂_jθ_l − θ_l ∂_jθ_c = W_{cjl}(θ)` -/
  θ_flow : ∀ c ∈ charts, ∀ (j : Fin g) (l : Fin N) (z : Fin g → ℂ),
    θ z c * fderiv ℂ θ z (Pi.single j 1) l - θ z l * fderiv ℂ θ z (Pi.single j 1) c =
      eval (θ z) (W c j l)
  -- Independent coordinates at the identity (Hilbert lower bound, transversality)
  i₀ : Fin N
  is : Fin g → Fin N
  θ_i₀ : θ 0 i₀ ≠ 0
  coords_locInv : ∃ f' : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ),
    HasFDerivAt (fun z j => θ z (is j) / θ z i₀) (f' : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) 0
  -- Simplicity as a complex torus
  simple : ∀ t : Submodule ℂ (Fin g → ℂ), IsRatSub per t → t = ⊥ ∨ t = ⊤
  -- B6: Hilbert certificate `S_n = (y_0, …, y_g)·S_{n−1} + I_n` for `n = hilb_deg`
  hilb_y : Fin (g + 1) → Fin N
  hilb_deg : ℕ
  hilb : ∀ M : MvPolynomial (Fin N) ℂ, M.IsHomogeneous hilb_deg →
    M ∈ Ideal.span {Q | Q ∈ gens} ⊔ Ideal.span (Set.range fun a => (X (hilb_y a) : MvPolynomial (Fin N) ℂ))
  -- B5: local complete intersection in projective form
  lci_s : ℕ
  lci_S : Fin lci_s → MvPolynomial (Fin N) ℂ
  lci_F : Fin lci_s → List (MvPolynomial (Fin N) ℂ)
  lci_len : ∀ i, (lci_F i).length + g + 1 = N
  lci_F_le : ∀ i, Ideal.ofList (lci_F i) ≤ Ideal.span {Q | Q ∈ gens}
  lci_mem : ∀ i, ∀ Q ∈ gens, lci_S i * Q ∈ Ideal.ofList (lci_F i)
  lci_cover : ∀ v : Fin N, ∃ e : ℕ,
    (X v : MvPolynomial (Fin N) ℂ) ^ e ∈ Ideal.span {Q | Q ∈ gens} ⊔ Ideal.span (Set.range lci_S)

end LSG.MEB
