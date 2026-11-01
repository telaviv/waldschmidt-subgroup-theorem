/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn4.Affine

/-!
# A4.1b: surjectivity onto the model

**`ThetaData.surjA`**: for every base, germ radius and `θ`-datum, every nonzero model point is `c • θ_N z`:
`∀ X ≠ 0, A.OnQ X → ∃ z c, X = c • θ_N z`, from `SurjFacts`.

* `ThetaData.imgCone_transfer`: the cone does not depend on the base (`expP_base_indep`, `expP_eq_thetaN`);
* at the anchored base: affine points (`affine_mem`), then boundary points (`boundary_mem`).
-/

noncomputable section

namespace LSG.JacAn

variable {A : A1Facts}

/-- **The cone is base independent.** -/
theorem ThetaData.imgCone_transfer {B₁ B₂ B₁' B₂' : LocalBranch f₅ 2} {p p' : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂}
    {hx : p.1 ≠ p.2} {hp' : p' ∈ dom2 B₁' B₂'} {hx' : p'.1 ≠ p'.2} {G : GermRad A hp hx}
    {G' : GermRad A hp' hx'} (D : ThetaData G) (D' : ThetaData G') {X : P9} (hX : X ∈ D.imgCone) :
    X ∈ D'.imgCone := by
  rcases hX with h | ⟨z, c, rfl⟩
  · exact Or.inl h
  · have h := (D.expP_eq_thetaN z).symm.trans ((congrFun (expP_base_indep G G') z).trans
      (D'.expP_eq_thetaN z))
    rw [Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨a, ha⟩ := h
    right
    exact ⟨z, c * a, by rw [← ha, smul_smul]⟩

/-- **Surjectivity onto the model** (`MEB.AbBlock.surj` for the A-block). -/
theorem ThetaData.surjA (SF : SurjFacts A) {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂}
    {hx : p.1 ≠ p.2} {G : GermRad A hp hx} (D : ThetaData G) :
    ∀ X : P9, X ≠ 0 → A.OnQ X → ∃ z : Fin 2 → ℂ, ∃ c : ℂ, X = c • D.thetaN z := by
  intro X hX0 hX
  obtain ⟨B₁', B₂', p', hp', hx', G₀, hanc⟩ := exists_anchored_base SF
  obtain ⟨D₀⟩ := exists_thetaData G₀
  have hP₀ := hanc G₀ D₀
  have haff : ∀ Y, A.OnQ Y → Y 0 ≠ 0 → Y ∈ D₀.imgCone := fun Y hY hY0 => D₀.affine_mem SF hP₀ hY hY0
  have hmem : X ∈ D₀.imgCone := by
    by_cases h0 : X 0 = 0
    · exact D₀.boundary_mem SF haff hX h0
    · exact haff X hX h0
  rcases D₀.imgCone_transfer D hmem with h | h
  · exact absurd h hX0
  · exact h

end LSG.JacAn
