/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlockV.Inst
import LSG.JacBlock.Packages
import LSG.AuxFunAV.Package
import LSG.JacAnV.GrowthT
import LSG.JacAnV.Rank3

/-!
# M2.6 input: the analytic package `aBlockVAn : VBlockAn aBlockV`

* `an = aBlockAnD D` (the base package, `lat = latt`);
* `growthT` from `ThetaData.fibT_growth` (`T_t = fibT (fc t)`, `fibOf_eq`);
* **`span_perV`**: the periods `(perVec e, η̄(perVec e))`, `e = 0, 1, 2`, lie in `perV` with `perVec e ∈ latt`, and
  are linearly independent by `ThetaData.period_det_ne_zero` (N6), so they span `ℂ² × ℂ`.
-/

noncomputable section

open MvPolynomial LSG.JacAn LSG.Jac LSG.JacAnV LSG.AuxAV LSG.JacAn.Beta

namespace LSG.JacBlockV

open LSG.JacBlock

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad a1Facts hp hx} (D : ThetaData G)

lemma T_aBlockVD (z : Fin 2 → ℂ) (w : ℂ) (t : Fin 3) : (aBlockVD D).T z w t = D.fibT (fcV t) z w :=
  fibOf_eq D z w t

lemma growthT_ex : ∃ c : ℝ, 0 ≤ c ∧ ∀ (z : Fin 2 → ℂ) (w : ℂ) (t : Fin 3),
    ‖(aBlockVD D).T z w t‖ ≤ (1 + ‖w‖) * Real.exp (c * (1 + ‖z‖) ^ 2) := by
  obtain ⟨c, hc, h⟩ := D.fibT_growth
  exact ⟨c, hc, fun z w t => by rw [T_aBlockVD]; exact h _ z w⟩

/-- The three counted periods `(perVec e, η̄(perVec e))`. -/
def perV3 (e : Fin 3) : (Fin 2 → ℂ) × ℂ := (perVec (e : ℕ), D.etaB (perVec (e : ℕ)))

lemma perVec_mem_latt3 (e : Fin 3) : perVec (e : ℕ) ∈ latt :=
  AddSubgroup.subset_closure ⟨⟨e, by omega⟩, rfl⟩

lemma perV3_linInd : LinearIndependent ℂ (perV3 D) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrArg (fun q : (Fin 2 → ℂ) × ℂ => q.1 0) hg
  have h1 := congrArg (fun q : (Fin 2 → ℂ) × ℂ => q.1 1) hg
  have h2 := congrArg (fun q : (Fin 2 → ℂ) × ℂ => q.2) hg
  simp only [Fin.sum_univ_three, perV3, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Fin.val_zero,
    Fin.val_one, Fin.val_two] at h0 h1 h2
  by_contra hne
  push_neg at hne
  obtain ⟨i, hi⟩ := hne
  refine D.period_det_ne_zero surjFacts (Matrix.exists_vecMul_eq_zero_iff.mp ⟨g, fun h => hi (by simp [h]), ?_⟩)
  funext col
  fin_cases col <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;>
    first | linear_combination h0 | linear_combination h1 | linear_combination h2

theorem span_perV_aBlockVD :
    Submodule.span ℂ {q : (Fin 2 → ℂ) × ℂ | q ∈ (aBlockVD D).perV ∧ q.1 ∈ (aBlockAnD D).lat} = ⊤ := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℂ ((Fin 2 → ℂ) × ℂ) := by
    simp [Module.finrank_prod, Module.finrank_fin_fun]
  have htop := (perV3_linInd D).span_eq_top_of_card_eq_finrank hcard
  refine eq_top_iff.mpr (htop.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨e, rfl⟩
  have hl := perVec_mem_latt3 e
  exact ⟨⟨LSG.W88.latt_le_kerE G hl, rfl⟩, hl⟩

/-- **The analytic package of `A_σ̄^♮`** (any `θ`-datum). -/
def aBlockVAnD : VBlockAn (aBlockVD D) where
  an := aBlockAnD D
  cT := (growthT_ex D).choose
  cT_nonneg := (growthT_ex D).choose_spec.1
  growthT := (growthT_ex D).choose_spec.2
  span_perV := span_perV_aBlockVD D

/-- **The analytic package of `aBlockV`.** -/
def aBlockVAn : VBlockAn aBlockV := aBlockVAnD stdPkg.D

example : aBlockVAn.an = aBlockAn := rfl

end LSG.JacBlockV
