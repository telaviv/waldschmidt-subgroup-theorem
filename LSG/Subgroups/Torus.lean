/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Subgroups.TorusLattice
import LSG.W88.Statement

/-!
# Closed subgroups of a product of complex tori

For period pairs `Ls j` (`j < m`) let `Λ = Λ₁ × ⋯ × Λ_m ⊂ ℂ^m` (`periodLattice Ls`). A closed
subgroup of the torus `ℂ^m / Λ` is given by its preimage `S ⊂ ℂ^m`: a closed additive subgroup
containing `Λ`. If its linear part is a complex subspace (e.g. if `S / Λ` is the group of complex
points of an algebraic subgroup), we obtain its tangent space `t`:

* `linPartC`: the linear part of `S` as a `ℂ`-subspace, under the hypothesis
  `∀ v, (∀ s : ℝ, s • v ∈ S) → ∀ c : ℂ, c • v ∈ S`;
* `periodLattice_discrete`, `span_periodLattice`: `Λ` is a full lattice in `ℂ^m`;
* `exists_abelianTangent`: `t` satisfies `LSG.W88.IsAbelianTangent Ls t` (its lattice points span
  it over `ℝ`), `t = linPart S` over `ℝ`, and `S` is a finite union of cosets of `t + Λ`.
-/

open Module

namespace LSG.Subgroups

variable {m : ℕ}

section Complex

variable (S : AddSubgroup (Fin m → ℂ))

/-- The linear part of `S ⊂ ℂ^m` as a complex subspace, when it is stable under `ℂ`. -/
def linPartC (hC : ∀ v, (∀ s : ℝ, s • v ∈ S) → ∀ c : ℂ, c • v ∈ S) :
    Submodule ℂ (Fin m → ℂ) where
  carrier := linPart S
  add_mem' := (linPart S).add_mem
  zero_mem' := (linPart S).zero_mem
  smul_mem' c v hv := fun s => by
    rw [← smul_assoc]
    exact hC v hv _

theorem restrictScalars_linPartC (hC : ∀ v, (∀ s : ℝ, s • v ∈ S) → ∀ c : ℂ, c • v ∈ S) :
    (linPartC S hC).restrictScalars ℝ = linPart S :=
  Submodule.ext fun _ => Iff.rfl

/-- **Complex structure.** If real lines in `S` are complex lines in `S`, the linear part of `S` is
a complex subspace. -/
theorem exists_complex_linPart (hC : ∀ v, (∀ s : ℝ, s • v ∈ S) → ∀ c : ℂ, c • v ∈ S) :
    ∃ t : Submodule ℂ (Fin m → ℂ), t.restrictScalars ℝ = linPart S :=
  ⟨linPartC S hC, restrictScalars_linPartC S hC⟩

end Complex

section Period

variable (Ls : Fin m → PeriodPair)

/-- The period lattice `Λ₁ × ⋯ × Λ_m ⊂ ℂ^m`. -/
def periodLattice : Submodule ℤ (Fin m → ℂ) :=
  Submodule.pi Set.univ fun j => (Ls j).lattice

theorem mem_periodLattice {z : Fin m → ℂ} : z ∈ periodLattice Ls ↔ ∀ j, z j ∈ (Ls j).lattice := by
  simp [periodLattice, Submodule.mem_pi]

instance periodLattice_discrete : DiscreteTopology (periodLattice Ls) :=
  DiscreteTopology.of_continuous_injective
    (f := fun z : periodLattice Ls => fun j => (⟨z.1 j, (mem_periodLattice Ls).mp z.2 j⟩ :
      (Ls j).lattice))
    (continuous_pi fun j => ((continuous_apply j).comp continuous_subtype_val).subtype_mk _)
    (fun x y h => Subtype.ext (funext fun j => by simpa using congrFun h j))

/-- `Λ₁ × ⋯ × Λ_m` spans `ℂ^m` over `ℝ`. -/
theorem span_periodLattice : Submodule.span ℝ (periodLattice Ls : Set (Fin m → ℂ)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basis fun j => (Ls j).basis).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨⟨j, k⟩, rfl⟩
  rw [Pi.basis_apply, SetLike.mem_coe, mem_periodLattice]
  intro i
  by_cases hij : i = j
  · subst hij
    rw [Pi.single_eq_same, (Ls i).lattice_eq_span_range_basis]
    exact Submodule.subset_span ⟨k, rfl⟩
  · rw [Pi.single_eq_of_ne hij]
    exact (Ls i).lattice.zero_mem

/-- **Closed subgroups of `E₁ × ⋯ × E_m` give abelian tangent spaces.** Let `S ⊂ ℂ^m` be a closed
additive subgroup containing `Λ₁ × ⋯ × Λ_m` whose real lines are complex lines. Then there is a
complex subspace `t` with: the lattice points of `t` span `t` over `ℝ` (`IsAbelianTangent`), `t` is
the linear part of `S`, and `S` is a finite union of cosets of `t + Λ`. -/
theorem exists_abelianTangent (S : AddSubgroup (Fin m → ℂ)) (hS : IsClosed (S : Set (Fin m → ℂ)))
    (hΛ : ∀ z : Fin m → ℂ, (∀ j, z j ∈ (Ls j).lattice) → z ∈ S)
    (hC : ∀ v, (∀ s : ℝ, s • v ∈ S) → ∀ c : ℂ, c • v ∈ S) :
    ∃ t : Submodule ℂ (Fin m → ℂ), LSG.W88.IsAbelianTangent Ls t ∧
      t.restrictScalars ℝ = linPart S ∧
      ∃ F : Finset (Fin m → ℂ), (F : Set (Fin m → ℂ)) ⊆ S ∧
        ∀ x ∈ S, ∃ f ∈ F, ∃ v ∈ t, ∃ l : Fin m → ℂ, (∀ j, l j ∈ (Ls j).lattice) ∧
          x = f + v + l := by
  have hLS : (periodLattice Ls : Set (Fin m → ℂ)) ⊆ S := fun z hz =>
    hΛ z ((mem_periodLattice Ls).mp hz)
  refine ⟨linPartC S hC, ?_, restrictScalars_linPartC S hC, ?_⟩
  · unfold LSG.W88.IsAbelianTangent
    rw [restrictScalars_linPartC]
    have hset : {z | z ∈ linPartC S hC ∧ ∀ j, z j ∈ (Ls j).lattice} =
        (linPart S : Set (Fin m → ℂ)) ∩ periodLattice Ls := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, mem_periodLattice]
      rfl
    rw [hset, span_linPart_inter_lattice _ S (span_periodLattice Ls) hS hLS]
  · obtain ⟨F, hFS, hF⟩ :=
      exists_finset_cosets (periodLattice Ls) S (span_periodLattice Ls) hS hLS
    refine ⟨F, hFS, fun x hx => ?_⟩
    obtain ⟨f, hf, v, hv, l, hl, rfl⟩ := hF x hx
    exact ⟨f, hf, v, hv, l, (mem_periodLattice Ls).mp hl, rfl⟩

end Period

end LSG.Subgroups
