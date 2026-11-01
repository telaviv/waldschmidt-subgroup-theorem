/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.CM.Rot
import LSG.AuxFunV.AlgV

/-!
# `ζ` is `ℤ[α]`-semilinear modulo `ℚ̄` at algebraic points

For a period pair with algebraic `g₂, g₃`, the **multipliers** (`multRing`) are the algebraic `β`
such that for every algebraic point `u` of `E` (a lattice point or `℘(u) ∈ ℚ̄`, `AlgPtE`), `βu` is
again algebraic and `ζ(βu) − β̄ ζ(u) ∈ ℚ̄`. They form a subring of `ℂ` (the `ζ` addition theorem
`isAlgebraic_zeta_defect`, oddness of `ζ`), which contains `α` for CM data (`ζ(αz) = ᾱζ(z)`), hence
`ℤ[α]` (`intComb_mem`). Consequence (`sum_mem`): `ζ(Σ βᵢ uᵢ) − Σ β̄ᵢ ζ(uᵢ) ∈ ℚ̄`.
-/

open Complex LSG.Weierstrass PeriodPair LSG.AuxV

namespace LSG.CM

lemma isAlgebraic_conj {x : ℂ} (h : IsAlgebraic ℚ x) : IsAlgebraic ℚ (starRingEnd ℂ x) :=
  h.algHom (Complex.conjAe.toAlgHom.restrictScalars ℚ)

variable (L : PeriodPair)

/-- `β` is a multiplier: algebraic, and `u ↦ βu` preserves algebraic points with
`ζ(βu) − β̄ζ(u) ∈ ℚ̄`. -/
def IsMult (β : ℂ) : Prop :=
  IsAlgebraic ℚ β ∧ ∀ u, AlgPtE L u →
    AlgPtE L (β * u) ∧ IsAlgebraic ℚ (zeta L (β * u) - starRingEnd ℂ β * zeta L u)

variable {L}

/-- **The multipliers form a subring.** -/
noncomputable def multRing (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) : Subring ℂ where
  carrier := {β | IsMult L β}
  mul_mem' {β γ} hβ hγ := by
    refine ⟨hβ.1.mul hγ.1, fun u hu => ?_⟩
    obtain ⟨h1, h2⟩ := hγ.2 u hu
    obtain ⟨h3, h4⟩ := hβ.2 _ h1
    rw [mul_assoc]
    refine ⟨h3, ?_⟩
    have : zeta L (β * (γ * u)) - starRingEnd ℂ (β * γ) * zeta L u =
        (zeta L (β * (γ * u)) - starRingEnd ℂ β * zeta L (γ * u)) +
          starRingEnd ℂ β * (zeta L (γ * u) - starRingEnd ℂ γ * zeta L u) := by
      rw [map_mul]; ring
    rw [this]
    exact h4.add ((isAlgebraic_conj hβ.1).mul h2)
  one_mem' := ⟨isAlgebraic_one, fun u hu => by simpa using ⟨hu, isAlgebraic_zero⟩⟩
  add_mem' {β γ} hβ hγ := by
    refine ⟨hβ.1.add hγ.1, fun u hu => ?_⟩
    obtain ⟨h1, h2⟩ := hβ.2 u hu
    obtain ⟨h3, h4⟩ := hγ.2 u hu
    obtain ⟨h5, h6⟩ := isAlgebraic_zeta_defect L hg₂ hg₃ h1 h3
    rw [add_mul]
    refine ⟨h5, ?_⟩
    have : zeta L (β * u + γ * u) - starRingEnd ℂ (β + γ) * zeta L u =
        (zeta L (β * u) - starRingEnd ℂ β * zeta L u) +
          (zeta L (γ * u) - starRingEnd ℂ γ * zeta L u) -
          (zeta L (β * u) + zeta L (γ * u) - zeta L (β * u + γ * u)) := by
      rw [map_add]; ring
    rw [this]
    exact (h2.add h4).sub h6
  zero_mem' := ⟨isAlgebraic_zero, fun u _ => ⟨by simp [AlgPtE, L.lattice.zero_mem],
    by simpa [LSG.W88.Vec.zeta_zero] using isAlgebraic_zero⟩⟩
  neg_mem' {β} hβ := by
    refine ⟨hβ.1.neg, fun u hu => ?_⟩
    obtain ⟨h1, h2⟩ := hβ.2 u hu
    rw [neg_mul]
    refine ⟨algPtE_neg L h1, ?_⟩
    have : zeta L (-(β * u)) - starRingEnd ℂ (-β) * zeta L u =
        -(zeta L (β * u) - starRingEnd ℂ β * zeta L u) := by
      rw [zeta_neg, map_neg]; ring
    rw [this]
    exact h2.neg

variable (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)

lemma mem_multRing {β : ℂ} : β ∈ multRing hg₂ hg₃ ↔ IsMult L β := Iff.rfl

variable {α : ℂ}

/-- The CM unit is a multiplier. -/
lemma alpha_mem (hd : CMData L α) : α ∈ multRing hg₂ hg₃ := by
  refine ⟨hd.alg, fun u hu => ⟨?_, ?_⟩⟩
  · rcases hu with hu | hu
    · exact Or.inl (hd.unit.mul_mem u hu)
    · right
      rw [weierstrassP_mul L hd.unit]
      exact ((hd.alg.pow 2).inv).mul hu
  · rw [zeta_mul L hd.unit, hd.conj_eq, sub_self]
    exact isAlgebraic_zero

lemma intComb_mem (hd : CMData L α) (m n : ℤ) : ((m : ℂ) + n * α) ∈ multRing hg₂ hg₃ :=
  add_mem (intCast_mem _ m) (mul_mem (intCast_mem _ n) (alpha_mem hg₂ hg₃ hd))

lemma div_mem (hd : CMData L α) {x : ℂ} (hx : x ∈ L.lattice) : x / L.ω₁ ∈ multRing hg₂ hg₃ := by
  obtain ⟨m, n, h⟩ := hd.div_eq hx
  rw [h]; exact intComb_mem hg₂ hg₃ hd m n

/-- **Semilinearity modulo `ℚ̄`**: `Σ βᵢ uᵢ` is algebraic and `ζ(Σ βᵢ uᵢ) − Σ β̄ᵢ ζ(uᵢ) ∈ ℚ̄`. -/
theorem sum_mem {ι : Type*} (s : Finset ι) (β u : ι → ℂ)
    (hβ : ∀ i ∈ s, β i ∈ multRing hg₂ hg₃) (hu : ∀ i ∈ s, AlgPtE L (u i)) :
    AlgPtE L (∑ i ∈ s, β i * u i) ∧
      IsAlgebraic ℚ (zeta L (∑ i ∈ s, β i * u i) -
        ∑ i ∈ s, starRingEnd ℂ (β i) * zeta L (u i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, LSG.W88.Vec.zeta_zero, sub_zero]
    exact ⟨Or.inl L.lattice.zero_mem, isAlgebraic_zero⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hβ i (Finset.mem_insert_of_mem hi))
      (fun i hi => hu i (Finset.mem_insert_of_mem hi))
    obtain ⟨h3, h4⟩ := (hβ a (Finset.mem_insert_self a s)).2 _ (hu a (Finset.mem_insert_self a s))
    obtain ⟨h5, h6⟩ := isAlgebraic_zeta_defect L hg₂ hg₃ h3 h1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨h5, ?_⟩
    have : zeta L (β a * u a + ∑ i ∈ s, β i * u i) -
        (starRingEnd ℂ (β a) * zeta L (u a) + ∑ i ∈ s, starRingEnd ℂ (β i) * zeta L (u i)) =
        (zeta L (β a * u a) - starRingEnd ℂ (β a) * zeta L (u a)) +
          (zeta L (∑ i ∈ s, β i * u i) - ∑ i ∈ s, starRingEnd ℂ (β i) * zeta L (u i)) -
          (zeta L (β a * u a) + zeta L (∑ i ∈ s, β i * u i) -
            zeta L (β a * u a + ∑ i ∈ s, β i * u i)) := by ring
    rw [this]
    exact (h4.add h2).sub h6

end LSG.CM
