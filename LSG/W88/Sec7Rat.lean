/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7Count

/-!
# `ℚ̄`-rationality of the additive part (W88 §7, item 3)

The multiplicity estimate produces obstruction data `O` over `ℂ`, whose additive part `h₀` need
not be `ℚ̄`-rational. We replace `h₀` by its `ℚ̄`-rational part
`h₀″ = span_ℂ {a ∈ h₀ : a algebraic}` (`ratPart`), keeping `U` and `t`:

* `λ` does not change: the `G_a` coordinates of points of `Y ⊂ Λ(G)` are algebraic, so
  `y ∈ T_{G′} + Ω ⇒ y ∈ T″ + Ω` (`inf_tanPer_eq`);
* `δ″ − τ″ ≥ δ − τ`: `δ` grows by `e = dim h₀ − dim h₀″` and `τ` by at most `e`
  (`finrank_inf_add_le`, `finrank_tan_add`).

So W88's inequality and `δ > τ` transfer from `O` to the `SubgroupData` (`exists_subgroupData_rat`);
no descent from `ℂ` to `ℚ̄` is needed.
-/

open LSG.ME Module

noncomputable section

namespace LSG.W88

variable {d0 d1 m : ℕ} {Ls : Fin m → PeriodPair}

/-- The `ℚ̄`-rational part of a subspace of `ℂ^n`. -/
def ratPart {n : ℕ} (h : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ {a | a ∈ h ∧ AlgVec a}

theorem ratPart_le {n : ℕ} (h : Submodule ℂ (Fin n → ℂ)) : ratPart h ≤ h :=
  Submodule.span_le.mpr fun _ ha => ha.1

theorem rationalOverQbar_ratPart {n : ℕ} (h : Submodule ℂ (Fin n → ℂ)) :
    RationalOverQbar (ratPart h) :=
  le_antisymm (Submodule.span_mono fun _ ha => ⟨Submodule.subset_span ha, ha.2⟩)
    (Submodule.span_le.mpr fun _ ha => ha.1)

theorem mem_ratPart {n : ℕ} {h : Submodule ℂ (Fin n → ℂ)} {a : Fin n → ℂ} (ha : a ∈ h)
    (halg : AlgVec a) : a ∈ ratPart h :=
  Submodule.subset_span ⟨ha, halg⟩

/-- **The `ℚ̄`-rational subgroup data** attached to `O`. -/
def ratData (O : ObstrData d0 d1 Ls) : SubgroupData (d0 := d0) (d1 := d1) Ls where
  h0 := ratPart O.h0
  U := O.U
  t := O.t
  h0_rat := rationalOverQbar_ratPart _
  t_ab := O.t_ab

theorem ratData_tan_le (O : ObstrData d0 d1 Ls) : (ratData O).tan ≤ O.tan :=
  fun _ hu => ⟨ratPart_le _ hu.1, hu.2⟩

theorem inf_tanPer_eq (O : ObstrData d0 d1 Ls) (Y : AddSubgroup (Tan d0 d1 m))
    (hY : ∀ y ∈ Y, y ∈ Lam Ls) :
    Y ⊓ ((ratData O).tan.toAddSubgroup ⊔ Per Ls) = Y ⊓ tanPer O := by
  apply le_antisymm
  · exact inf_le_inf_left _ (sup_le_sup_right (fun u hu => ratData_tan_le O hu) _)
  · rintro y ⟨hyY, hy⟩
    refine ⟨hyY, ?_⟩
    obtain ⟨a, ha, p, hp, rfl⟩ := AddSubgroup.mem_sup.mp hy
    refine AddSubgroup.mem_sup.mpr ⟨a, ?_, p, hp, rfl⟩
    have halg : AlgVec (a + p).1 := (hY _ hyY).1
    have hp1 : p.1 = 0 := hp.1
    rw [Prod.fst_add, hp1, add_zero] at halg
    exact ⟨mem_ratPart ha.1 halg, ha.2⟩

/-- For `A′ ≤ A`: `dim (W ∩ A) + dim A′ ≤ dim (W ∩ A′) + dim A`. -/
theorem finrank_inf_add_le {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W A A' : Submodule ℂ V) (h : A' ≤ A) :
    finrank ℂ ↥(W ⊓ A) + finrank ℂ A' ≤ finrank ℂ ↥(W ⊓ A') + finrank ℂ A := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ A) A'
  have h2 : (W ⊓ A) ⊓ A' = W ⊓ A' := by
    rw [inf_assoc, inf_eq_right.mpr h]
  have h3 : finrank ℂ ↥((W ⊓ A) ⊔ A') ≤ finrank ℂ A :=
    Submodule.finrank_mono (sup_le inf_le_right h)
  rw [h2] at h1
  omega

theorem finrank_tan_add (O : ObstrData d0 d1 Ls) :
    finrank ℂ O.tan + finrank ℂ (ratPart O.h0) = finrank ℂ (ratData O).tan + finrank ℂ O.h0 := by
  set f : Tan d0 d1 m →ₗ[ℂ] (Fin d0 → ℂ) := LinearMap.fst ℂ _ _
  have hmapO : O.tan.map f = O.h0 := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩; exact hu.1
    · intro a ha
      exact ⟨(a, 0, 0), ⟨ha, Submodule.zero_mem _, Submodule.zero_mem _⟩, rfl⟩
  have hmapH : (ratData O).tan.map f = ratPart O.h0 := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩; exact hu.1
    · intro a ha
      exact ⟨(a, 0, 0), ⟨ha, Submodule.zero_mem _, Submodule.zero_mem _⟩, rfl⟩
  have hker : (ratData O).tan ⊓ LinearMap.ker f = O.tan ⊓ LinearMap.ker f := by
    apply le_antisymm
    · exact inf_le_inf_right _ (ratData_tan_le O)
    · rintro u ⟨hu, hk⟩
      have hu1 : u.1 = 0 := hk
      refine ⟨⟨?_, hu.2⟩, hk⟩
      rw [hu1]; exact Submodule.zero_mem _
  have e1 := StrongSix.Roy.finrank_map_add_inf_ker f O.tan
  have e2 := StrongSix.Roy.finrank_map_add_inf_ker f (ratData O).tan
  rw [hmapO] at e1
  rw [hmapH, hker] at e2
  omega

/-- **The `ℚ̄`-rational subgroup data**: same `λ`, `δ₁`, `δ₂`, and `δ − τ` does not decrease. -/
theorem exists_subgroupData_rat (O : ObstrData d0 d1 Ls) (W : Submodule ℂ (Tan d0 d1 m))
    (Y : AddSubgroup (Tan d0 d1 m)) (hY : ∀ y ∈ Y, y ∈ Lam Ls) :
    ∃ H : SubgroupData (d0 := d0) (d1 := d1) Ls,
      rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) = rk (Y ⊓ tanPer O) ∧
      H.δ1 = finrank ℚ O.U ∧ H.δ2 = m - finrank ℂ O.t ∧
      ((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (m - finrank ℂ O.t) : ℕ) : ℤ) -
          ((finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan) : ℕ) : ℤ) ≤
        (H.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ) : ℤ) := by
  refine ⟨ratData O, by rw [inf_tanPer_eq O Y hY], rfl, rfl, ?_⟩
  have hA := finrank_inf_add_le W O.tan (ratData O).tan (ratData_tan_le O)
  have hB := finrank_tan_add O
  have hW1 : finrank ℂ ↥(W ⊓ O.tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
  have hW2 : finrank ℂ ↥(W ⊓ (ratData O).tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
  have hh0 : finrank ℂ O.h0 ≤ d0 := by
    simpa using Submodule.finrank_le O.h0
  have hr0 : finrank ℂ (ratPart O.h0) ≤ finrank ℂ O.h0 := Submodule.finrank_mono (ratPart_le _)
  simp only [SubgroupData.δ, SubgroupData.δ0, SubgroupData.δ1, SubgroupData.δ2]
  change ((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (m - finrank ℂ O.t) : ℕ) : ℤ) -
      ((finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan) : ℕ) : ℤ) ≤
    ((d0 - finrank ℂ (ratPart O.h0) + finrank ℚ O.U + (m - finrank ℂ O.t) : ℕ) : ℤ) -
      ((finrank ℂ W - finrank ℂ ↥(W ⊓ (ratData O).tan) : ℕ) : ℤ)
  push_cast [hW1, hW2, hh0, hr0.trans hh0]
  omega

end LSG.W88
