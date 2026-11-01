/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Waldschmidt's subgroup theorem with period term (W88 Thm 4.1): the statement

This file only *states* the target theorem, as a `Prop`, in coordinates. No algebraic-group theory
appears: the group, its logarithms of algebraic points, its periods and its connected algebraic
subgroups are all written in terms of the tangent space `ℂ^{d₀} × ℂ^{d₁} × ℂ^m`.

## The group

`G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, where `E_j` is the elliptic curve
`y² = 4x³ − g₂(Λ_j) x − g₃(Λ_j)` attached to a period pair `Ls j` with algebraic invariants. The
exponential map is `(a, b, z) ↦ (a, e^{b}, (℘_j(z_j), ℘_j'(z_j)))`.

* `Lam` (the logarithms of algebraic points, `Λ(G) = exp_G⁻¹ G(ℚ̄)`): `a ∈ ℚ̄^{d₀}`, every `e^{b_i}`
  algebraic, and every `z_j` either a period of `E_j` or a point with `℘_j(z_j)` algebraic.
  (Then `℘_j'(z_j)` is algebraic too, by the Weierstrass equation.)
* `Per` (the periods, `Ω(G) = ker exp_G`): `0 × 2πiℤ^{d₁} × Λ₁ × ⋯ × Λ_m`.

## Connected algebraic subgroups

A connected algebraic subgroup of `G` defined over `ℚ̄` is a product `G' = H₀ × T_U × B` with
* `H₀ ⊂ G_a^{d₀}` a `ℚ̄`-rational subspace `h₀`;
* `T_U ⊂ G_m^{d₁}` the subtorus with Lie algebra `U^⊥ = {v : Σ φⱼ vⱼ = 0 ∀ φ ∈ U}`, `U ⊂ ℚ^{d₁}`;
* `B ⊂ E₁ × ⋯ × E_m` an abelian subvariety, given by its tangent space `t ⊂ ℂ^m`, characterised
  by: `t ∩ (Λ₁ × ⋯ × Λ_m)` spans `t` over `ℝ` (so `B = t / (t ∩ Λ)` is a compact subtorus; complex
  subtori of abelian varieties are abelian subvarieties, and conversely).
Its tangent space is `h₀ × U^⊥ × t`, and `exp_G⁻¹(G') = T_{G'} + Ω(G)`.

## The theorem (W88, Thm 4.1, pp. 385–386; with the extra hypothesis (NR), under which W88 Prop. 6.1 holds via Lemma U (M* paper, Appendix A))

Let `V ⊂ T_G` have dimension `N < d`, `W ⊂ V` be `ℚ̄`-rational, and `Y ⊂ V ∩ Λ(G)` a finitely
generated subgroup; `κ = rk_ℤ (Y ∩ Ω(G))`. Assume `2N ≥ d₁ + 2d₀ + κ`. Then there is
`G' = H₀ × T_U × B ≠ G` with `δ > τ` and
`(λ + δ₁ + 2δ₂)(d − N) ≤ (δ − τ)(d₁ + 2d₂ − κ)`, where `δ = codim G'`, `δ₀ = d₀ − dim h₀`,
`δ₁ = dim U`, `δ₂ = m − dim t`, `λ = rk_ℤ Y / (Y ∩ (T_{G'} + Ω(G)))` and
`τ = dim W − dim (W ∩ T_{G'})`.

Here `G₂ = E₁ × ⋯ × E_m` (W88 allows any commutative `G₂`; the vector extensions needed for
MG♮, MX, MX′ are added in a later version of this file). The theorem is stated for arbitrary
curves; the M* applications only use CM curves.
-/

open Complex Module

namespace LSG.W88

/-- The tangent space `ℂ^{d₀} × ℂ^{d₁} × ℂ^m` of `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`. -/
abbrev Tan (d0 d1 m : ℕ) := (Fin d0 → ℂ) × (Fin d1 → ℂ) × (Fin m → ℂ)

variable {d0 d1 m : ℕ}

/-- A vector with algebraic coordinates. -/
def AlgVec {n : ℕ} (u : Fin n → ℂ) : Prop := ∀ i, IsAlgebraic ℚ (u i)

/-- A `ℂ`-subspace of `ℂ^n` is *rational over `ℚ̄`* if it is spanned by vectors with algebraic
coordinates. -/
def RationalOverQbar {n : ℕ} (W : Submodule ℂ (Fin n → ℂ)) : Prop :=
  W = Submodule.span ℂ {w | w ∈ W ∧ AlgVec w}

/-- `ℚ̄`-rationality for subspaces of the full tangent space (all coordinates algebraic). -/
def RationalOverQbarTan (W : Submodule ℂ (Tan d0 d1 m)) : Prop :=
  W = Submodule.span ℂ {w | w ∈ W ∧ AlgVec w.1 ∧ AlgVec w.2.1 ∧ AlgVec w.2.2}

/-- The logarithms of algebraic points `Λ(G) = exp_G⁻¹ G(ℚ̄)`. -/
def Lam (Ls : Fin m → PeriodPair) : Set (Tan d0 d1 m) :=
  {p | AlgVec p.1 ∧ (∀ i, IsAlgebraic ℚ (Complex.exp (p.2.1 i))) ∧
    ∀ j, p.2.2 j ∈ (Ls j).lattice ∨ IsAlgebraic ℚ ((Ls j).weierstrassP (p.2.2 j))}

/-- The period group `Ω(G) = ker exp_G = 0 × 2πiℤ^{d₁} × Λ₁ × ⋯ × Λ_m`. -/
def Per (Ls : Fin m → PeriodPair) : AddSubgroup (Tan d0 d1 m) where
  carrier := {p | p.1 = 0 ∧ (∀ i, ∃ k : ℤ, p.2.1 i = 2 * Real.pi * I * k) ∧
    ∀ j, p.2.2 j ∈ (Ls j).lattice}
  add_mem' {p q} hp hq := by
    refine ⟨by simp [hp.1, hq.1], fun i => ?_, fun j => ?_⟩
    · obtain ⟨k, hk⟩ := hp.2.1 i
      obtain ⟨l, hl⟩ := hq.2.1 i
      exact ⟨k + l, by
        show p.2.1 i + q.2.1 i = _
        rw [hk, hl]; push_cast; ring⟩
    · exact (Ls j).lattice.add_mem (hp.2.2 j) (hq.2.2 j)
  zero_mem' := ⟨rfl, fun _ => ⟨0, by simp⟩, fun j => (Ls j).lattice.zero_mem⟩
  neg_mem' {p} hp := by
    refine ⟨by simp [hp.1], fun i => ?_, fun j => ?_⟩
    · obtain ⟨k, hk⟩ := hp.2.1 i
      exact ⟨-k, by
        show -p.2.1 i = _
        rw [hk]; push_cast; ring⟩
    · exact (Ls j).lattice.neg_mem (hp.2.2 j)

/-- The Lie algebra `U^⊥` of the subtorus `T_U ⊂ G_m^{d₁}`, `U ⊂ ℚ^{d₁}`. -/
def torusLie (U : Submodule ℚ (Fin d1 → ℚ)) : Submodule ℂ (Fin d1 → ℂ) where
  carrier := {v | ∀ φ ∈ U, ∑ j, (φ j : ℂ) * v j = 0}
  add_mem' {a b} ha hb φ hφ := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' φ _ := by simp
  smul_mem' c v hv φ hφ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ j, (φ j : ℂ) * (c * v j)) = c * ∑ j, (φ j : ℂ) * v j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hv φ hφ, mul_zero]

/-- `t ⊂ ℂ^m` is the tangent space of an abelian subvariety of `E₁ × ⋯ × E_m`: its intersection with
the period lattice `Λ₁ × ⋯ × Λ_m` spans it over `ℝ`. -/
def IsAbelianTangent (Ls : Fin m → PeriodPair) (t : Submodule ℂ (Fin m → ℂ)) : Prop :=
  (t.restrictScalars ℝ : Submodule ℝ (Fin m → ℂ)) =
    Submodule.span ℝ {z | z ∈ t ∧ ∀ j, z j ∈ (Ls j).lattice}

/-- Data of a connected algebraic subgroup `G' = H₀ × T_U × B` of `G`. -/
structure SubgroupData (Ls : Fin m → PeriodPair) where
  /-- the additive part, a `ℚ̄`-rational subspace of `ℂ^{d₀}` -/
  h0 : Submodule ℂ (Fin d0 → ℂ)
  /-- the character space of the toric part -/
  U : Submodule ℚ (Fin d1 → ℚ)
  /-- the tangent space of the abelian part -/
  t : Submodule ℂ (Fin m → ℂ)
  h0_rat : RationalOverQbar h0
  t_ab : IsAbelianTangent Ls t

namespace SubgroupData

variable {Ls : Fin m → PeriodPair} (H : SubgroupData (d0 := d0) (d1 := d1) Ls)

/-- The tangent space `T_{G'} = h₀ × U^⊥ × t`. -/
def tan : Submodule ℂ (Tan d0 d1 m) := H.h0.prod ((torusLie H.U).prod H.t)

/-- `δ₀ = codim h₀`. -/
noncomputable def δ0 : ℕ := d0 - finrank ℂ H.h0
/-- `δ₁ = dim U = codim T_U`. -/
noncomputable def δ1 : ℕ := finrank ℚ H.U
/-- `δ₂ = codim t`. -/
noncomputable def δ2 : ℕ := m - finrank ℂ H.t
/-- `δ = codim G'`. -/
noncomputable def δ : ℕ := H.δ0 + H.δ1 + H.δ2

/-- `G' ≠ G`. -/
def Proper : Prop := H.δ ≠ 0

end SubgroupData

/-- `rk_ℤ` of an additive subgroup of a `ℚ`-vector space, as the dimension of its `ℚ`-span. -/
noncomputable def rk {E : Type*} [AddCommGroup E] [Module ℚ E] (Y : AddSubgroup E) : ℕ :=
  finrank ℚ (Submodule.span ℚ (Y : Set E))

/-- **W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, under (NR).** -/
def Theorem41Abelian : Prop :=
  ∀ (d0 d1 m : ℕ) (Ls : Fin m → PeriodPair),
    (∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) →
    ∀ (V W : Submodule ℂ (Tan d0 d1 m)) (Y : AddSubgroup (Tan d0 d1 m)),
      finrank ℂ V < d0 + d1 + m → W ≤ V → RationalOverQbarTan W →
      Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ Lam Ls) →
      -- (NR)
      d1 + 2 * d0 + rk (Y ⊓ Per Ls) ≤ 2 * finrank ℂ V →
      ∃ H : SubgroupData (d0 := d0) (d1 := d1) Ls, H.Proper ∧
        finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) < H.δ ∧
        (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) + H.δ1 + 2 * H.δ2 : ℕ) : ℤ) *
            ((d0 + d1 + m : ℕ) - finrank ℂ V : ℤ) ≤
          ((H.δ : ℤ) - (finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ)) *
            ((d1 + 2 * m : ℕ) - rk (Y ⊓ Per Ls) : ℤ))

end LSG.W88
