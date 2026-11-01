/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn4.FlowExit

/-!
# A4.1b (S-b): the anchored base

**`exists_anchored_base`**: from `SurjFacts.anchor` there is a generic base `(0, −1) + (α, 3)` with a germ radius such
that, for every `θ`-datum over it, `P₀ ∈` cone (`ThetaData.anchor_mem`). With `ThetaData.generic_mem` every generic
Grant point is then in the cone.
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

variable {A : A1Facts}

lemma mumfordPts_eq' (x₁ y₁ x₂ y₂ : ℂ) : mumfordPts x₁ y₁ x₂ y₂ = mumfordPts' x₁ y₁ x₂ y₂ := rfl

/-- **The anchored base.** -/
theorem exists_anchored_base (SF : SurjFacts A) : ∃ (B₁ B₂ : LocalBranch f₅ 2) (p : ℂ × ℂ)
    (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2) (_ : GermRad A hp hx),
    ∀ (G : GermRad A hp hx) (D : ThetaData G), baseP hp hx ∈ D.imgCone := by
  obtain ⟨α, hα, hspec, x₁, y₁, x₂, y₂, h1, h2, hx12, hy1, hy2, lam, hlam, hD₂⟩ := SF.anchor
  obtain ⟨B₁, h1x, h1y⟩ := LocalBranch.exists_of_mem (f := f₅) (g := 2) (x₀ := 0) (y₀ := -1)
    (by rw [f₅_eval]; norm_num) (by norm_num)
  obtain ⟨B₂, h2x, h2y⟩ := LocalBranch.exists_of_mem (f := f₅) (g := 2) (x₀ := α) (y₀ := 3)
    (by rw [f₅_eval, hα]; norm_num) (by norm_num)
  have hp : ((0 : ℂ), α) ∈ dom2 B₁ B₂ := by
    refine ⟨?_, ?_⟩
    · change (0 : ℂ) ∈ ball B₁.x₀ B₁.r
      rw [h1x]; exact mem_ball_self B₁.r_pos
    · change α ∈ ball B₂.x₀ B₂.r
      rw [h2x]; exact mem_ball_self B₂.r_pos
  have hα0 : α ≠ 0 := by rintro rfl; norm_num at hα
  have hx : ((0 : ℂ), α).1 ≠ ((0 : ℂ), α).2 := fun h => hα0 h.symm
  have hbase : baseP hp hx = P0of α := by
    simp only [baseP, psiJ, localExp_abel2_self, mumford, P0of, mumfordPts', h1y, h2y]
  have hP₀ : A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 ≠ 0 := by rw [hbase]; exact hspec
  obtain ⟨G₀⟩ := exists_germRad hP₀
  refine ⟨B₁, B₂, _, hp, hx, G₀, fun G D => ?_⟩
  refine D.anchor_mem (x₁ := x₁) (y₁ := y₁) (x₂ := x₂) (y₂ := y₂) h1 h2 hx12 hy1 hy2 hlam ?_
  rw [hbase, mumfordPts_eq']; exact hD₂

end LSG.JacAn
