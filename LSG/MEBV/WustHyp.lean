/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.MainHyp
import LSG.MEBV.Ord

/-!
# The sliced Wüstholz lemma as the assembly consumes it (M2.5 α; the statement of `LSG.MEB.wust_of_tz`)

* `homOrd W n E`: the ideal spanned by the multihomogeneous elements of β's `ordIdealB W n E` (MEB's `WustAlgB`
  definition), `mem_homOrd_of`, `IGsem_le_homOrd`.
* **`WustPropV O`**: the sliced Wüstholz lemma for finite unions of distinct cosets of `O.grp`, in exactly the form
  `Main` consumes (the conclusion of MEB's `wust_of_tz`).

β's Wüstholz files deliver `wust_of_tz : TZPropV O → WustPropV O` (M2.md, α/β interface). Until then `Main` takes
this implication as an explicit hypothesis.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata)

namespace LSG.MEBV

open LSG.MEB (Blk)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- The ideal spanned by the multihomogeneous elements of `ordIdealB W n E`. -/
noncomputable def homOrd (W : Submodule ℂ (Tan d₀ d₁ B)) (n : ℕ) (E : Set (GPt d₀ d₁ B)) :
    Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  Ideal.span {Q | Q ∈ ordIdealB W n E ∧ ∃ d, IsHomV Q d}

theorem mem_homOrd_of {W : Submodule ℂ (Tan d₀ d₁ B)} {n : ℕ} {E : Set (GPt d₀ d₁ B)}
    {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    (h : Q ∈ ordIdealB W n E) : Q ∈ homOrd W n E :=
  Ideal.subset_span ⟨h, d, hQ⟩

/-- `IGsem ≤ homOrd` (multihomogeneous components of `IGsem` stay in `IGsem`). -/
theorem IGsem_le_homOrd (W : Submodule ℂ (Tan d₀ d₁ B)) (n : ℕ) (E : Set (GPt d₀ d₁ B)) :
    IGsem d₀ d₁ B ≤ homOrd W n E := by
  intro P hP
  obtain ⟨s, hs⟩ := sum_multiComp P
  rw [hs]
  refine Ideal.sum_mem _ fun d _ => ?_
  have hd := isHomV_iff_wV.mpr (weightedHomogeneousComponent_isWeightedHomogeneous (w := wV) d P)
  exact mem_homOrd_of hd (IGsem_le_ordIdealB n E (multiComp_mem_vanish d hP))

/-- **The sliced Wüstholz lemma** for the cosets of `O.grp`: for distinct cosets `a + O.grp` (`a ∈ R`) and good
chart forms `α`, there is `c0` such that every ideal `A` spanned by multihomogeneous elements of order `> S0`
along `W` on `E = ⋃_{a ∈ R} (a + O.grp)` satisfies, for `ℓ = dim W − dim (W ∩ O.tan)` and `ℓ k ≤ S0`,
`(k + 1)^ℓ · H(sl α I(E); t) ≤ H(sl α A; t + S0 c0)`. -/
def WustPropV (O : ObstrDataGV d₀ d₁ B) : Prop :=
  ∀ (W : Submodule ℂ (Tan d₀ d₁ B)) (R : Finset (GPt d₀ d₁ B)),
    (∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ O.grp) → ∀ D : Blk m → ℕ, (∀ i, 1 ≤ D i) →
    ∀ α : Alpha B, (∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a O.grp)) →
    ∃ c0 : ℕ, ∀ (A : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) (S0 k : ℕ),
      (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * k ≤ S0 →
      A ≤ homOrd W S0 (⋃ a ∈ R, gtransl a O.grp) → ∀ t,
      (k + 1) ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) *
          hfun blk D ℂ (sl α (vanish (⋃ a ∈ R, gtransl a O.grp))) t ≤
        hfun blk D ℂ (sl α A) (t + S0 * c0)

variable (d₀ d₁ B) in
/-- The Wüstholz input for one family: `TZPropV O → WustPropV O` for all obstruction data (β's
`wust_of_tz`). -/
def WustInput : Prop := ∀ O : ObstrDataGV d₀ d₁ B, TZPropV O → WustPropV O

end LSG.MEBV
