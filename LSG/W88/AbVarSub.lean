/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.StatementAbVar

/-!
# `λ ≠ 0` on nonzero abelian tangents, without the CM classification (the `sub` condition of `lean_mstar`'s `gmA`)

`lean_mstar`'s frame model `gmF` lists as subgroups `(torSub L).prod h` with `h = ⊥ ∨ ∃ x ∈ h, λ x ≠ 0`, where
`λ(q) = Σ_j b_j q(s₀, j)` and `θ(j, e) = ζ^e b_j` is `ℚ`-linearly independent (`IsAdaptedBasisD.indep`). The
soundness note of `gmA` (ThmA.lean header) derives `λ ≠ 0` from the CM classification (`T(B) = ⊕_s σ_s(S) ⊗ ℂ`).
For the slot `s₀ = 0` (`κ s₀ = 1`) the classification is not needed:

* a nonzero `t` with `IsAbelianTangentA t` contains a nonzero lattice point `z ∈ Λ^r` (`exists_lattice_point`);
* `z_j = Σ_e n_{je} perVec e` with `n ∈ ℤ`, so `Σ_j b_j z_j(0) = cJ₀ Σ_{j,e} n_{je} ζ^e b_j`, which is `0` only if
  `n = 0`, by `ℚ`-independence of `θ` (**`lam_ne_zero_of_abelian`**).
-/

open Complex Module

namespace LSG.W88

open LSG.JacAn LSG.JacAn.Beta

variable {r : ℕ}

/-- A nonzero abelian tangent contains a nonzero lattice point. -/
theorem exists_lattice_point {t : Submodule ℂ (Fin r → Fin 2 → ℂ)} (ht : IsAbelianTangentA t) (hne : t ≠ ⊥) :
    ∃ z ∈ t, z ≠ 0 ∧ ∀ j, z j ∈ latt := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hsub : {z | z ∈ t ∧ ∀ j, z j ∈ latt} ⊆ ({0} : Set (Fin r → Fin 2 → ℂ)) := fun z hz => by
    by_contra h0
    obtain ⟨j, hj⟩ := hcon z hz.1 h0
    exact hj (hz.2 j)
  have hspan : Submodule.span ℝ {z | z ∈ t ∧ ∀ j, z j ∈ latt} = ⊥ := by
    rw [eq_bot_iff, Submodule.span_le]
    intro z hz
    have := hsub hz
    simp only [Set.mem_singleton_iff] at this
    simp [this]
  rw [eq_bot_iff]
  intro z hz
  have hz' : z ∈ (t.restrictScalars ℝ : Submodule ℝ (Fin r → Fin 2 → ℂ)) := hz
  rw [ht, hspan] at hz'
  simpa using hz'

/-- **`λ ≠ 0` on every nonzero abelian tangent** (slot `0`), for `θ(j, e) = ζ^e b_j` `ℚ`-linearly independent. -/
theorem lam_ne_zero_of_abelian {t : Submodule ℂ (Fin r → Fin 2 → ℂ)} (ht : IsAbelianTangentA t) (hne : t ≠ ⊥)
    {b : Fin r → ℂ} (hb : LinearIndependent ℚ (fun p : Fin r × Fin 4 => zetaN 5 ^ (p.2 : ℕ) * b p.1)) :
    ∃ z ∈ t, ∑ j, b j * z j 0 ≠ 0 := by
  obtain ⟨z, hzt, hz0, hzl⟩ := exists_lattice_point ht hne
  refine ⟨z, hzt, fun hsum => hz0 ?_⟩
  choose n hn using fun j => AddSubgroup.exists_of_mem_closure_range (fun e : Fin 4 => perVec (e : ℕ)) (z j) (hzl j)
  have hz0j : ∀ j, z j 0 = cJ 0 * ∑ e : Fin 4, (n j e : ℂ) * zetaN 5 ^ (e : ℕ) := fun j => by
    rw [hn j, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Pi.smul_apply, zsmul_eq_mul, perVec_eq]
    simp; ring
  have hc : cJ 0 ≠ 0 := cJ_ne_zero (by norm_num)
  have hrel : ∑ p : Fin r × Fin 4, ((n p.1 p.2 : ℚ)) • (zetaN 5 ^ (p.2 : ℕ) * b p.1) = 0 := by
    have : ∑ j, b j * z j 0 = cJ 0 * ∑ p : Fin r × Fin 4, ((n p.1 p.2 : ℚ)) • (zetaN 5 ^ (p.2 : ℕ) * b p.1) := by
      simp only [hz0j, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun e _ => ?_
      rw [Rat.smul_def]; push_cast; ring
    rw [this] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left hc
  have hn0 := Fintype.linearIndependent_iff.mp hb _ hrel
  funext j
  rw [hn j]
  refine Finset.sum_eq_zero fun e _ => ?_
  have : (n j e : ℚ) = 0 := hn0 (j, e)
  have : n j e = 0 := by exact_mod_cast this
  simp [this]

end LSG.W88
