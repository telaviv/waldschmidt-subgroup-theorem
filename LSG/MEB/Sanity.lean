/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Stmt

/-!
# Sanity checks for the frozen interface (A4.0)

* **`pointBlock : AbBlock`**: the trivial block (`g = 0`, `N = 1`, `θ ≡ 1`, no generators, one law `X₀² Y₀²`). It shows
  that the field list of `AbBlock` is satisfiable. It exercises the certificate fields (`hilb`, `lci_*`) and the law
  fields, but not the analytic ones (`ℂ⁰` is a point).
* `notMem_IGsem_one`: the statement-side definitions instantiate on `G_a^{d₀} × G_m^{d₁} × pt^m`, and `1 ∉ IGsem`
  (through `notMem_IGsem_of_eval_ne`).

The elliptic instance was not built: see STAGE_A4.md §6.4.
-/

open MvPolynomial

namespace LSG.MEB.Sanity

open LSG.MEB

/-- The law `X₀² Y₀²` of the point block. -/
noncomputable def pointLaw : Fin 1 → Fin 1 → MvPolynomial (Fin 1 ⊕ Fin 1) ℂ :=
  fun _ _ => X (Sum.inl 0) ^ 2 * X (Sum.inr 0) ^ 2

theorem pointLaw_hom (i k : Fin 1) :
    (pointLaw i k).IsWeightedHomogeneous (biW 1) ((2, 2) : ℕ × ℕ) := by
  have h1 : (X (Sum.inl 0) : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ).IsWeightedHomogeneous (biW 1) (1, 0) :=
    isWeightedHomogeneous_X ℂ (biW 1) (Sum.inl 0)
  have h2 : (X (Sum.inr 0) : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ).IsWeightedHomogeneous (biW 1) (0, 1) :=
    isWeightedHomogeneous_X ℂ (biW 1) (Sum.inr 0)
  have := (h1.pow 2).mul (h2.pow 2)
  simpa [pointLaw] using this

theorem eq_smul_one (X : Fin 1 → ℂ) : X = X 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
  funext i; fin_cases i; simp

/-- **The point block.** -/
noncomputable def pointBlock : AbBlock where
  g := 0
  N := 1
  gens := []
  gens_hom := by simp
  θ := fun _ _ => 1
  θ_analytic := fun _ => analyticAt_const
  θ_ne := fun _ h => by simpa using congrFun h 0
  θ_model := by simp
  per := ⊥
  per_discrete := inferInstance
  per_span := Subsingleton.elim _ _
  θ_per := fun _ _ _ => ⟨1, one_ne_zero, by simp⟩
  θ_ker := fun z w _ => by simp [Subsingleton.elim (w - z) 0]
  surj := fun X hX _ => ⟨0, X 0, eq_smul_one X⟩
  nL := 1
  law := pointLaw
  law_hom := pointLaw_hom
  law_eq := fun _ _ _ => ⟨1, by funext k; simp [evalLaw, pointLaw]⟩
  law_complete := fun _ _ => ⟨0, fun h => by simpa [evalLaw, pointLaw] using congrFun h 0⟩
  charts := {0}
  chart_cover := fun X hX _ => ⟨0, by simp, fun h0 => hX (by funext i; fin_cases i; exact h0)⟩
  W := fun _ _ _ => 0
  W_hom := fun _ _ _ => isHomogeneous_zero _ _ _
  W_chart := fun _ _ => rfl
  θ_flow := fun _ _ j => j.elim0
  i₀ := 0
  is := Fin.elim0
  θ_i₀ := one_ne_zero
  coords_locInv := ⟨ContinuousLinearEquiv.refl ℂ _, by
    rw [Subsingleton.elim (ContinuousLinearEquiv.refl ℂ (Fin 0 → ℂ) : (Fin 0 → ℂ) →L[ℂ] (Fin 0 → ℂ)) 0]
    exact (hasFDerivAt_const (0 : Fin 0 → ℂ) 0).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _)⟩
  simple := fun t _ => Or.inl (Subsingleton.elim _ _)
  hilb_y := fun _ => 0
  hilb_deg := 1
  hilb := fun M hM => by
    have hM' : M ∈ Ideal.span ((X : Fin 1 → MvPolynomial (Fin 1) ℂ) '' Set.univ) := by
      rw [mem_ideal_span_X_image]
      intro d hd
      refine ⟨0, Set.mem_univ _, ?_⟩
      have h := hM (mem_support_iff.mp hd)
      simp [Finsupp.weight_apply, Finsupp.sum_fintype] at h
      omega
    refine Ideal.mem_sup_right (Ideal.span_mono ?_ hM')
    rintro _ ⟨i, -, rfl⟩
    exact ⟨0, by fin_cases i; rfl⟩
  lci_s := 1
  lci_S := fun _ => 1
  lci_F := fun _ => []
  lci_len := fun _ => rfl
  lci_F_le := fun _ => by simp [Ideal.ofList]
  lci_mem := by simp
  lci_cover := fun v => ⟨0, by simp⟩

/-- `1 ∉ IGsem` on `G_a^{d₀} × G_m^{d₁} × pt^m`. -/
theorem notMem_IGsem_one (d₀ d₁ m : ℕ) :
    (1 : MvPolynomial (Var d₀ d₁ fun _ : Fin m => pointBlock) ℂ) ∉
      IGsem d₀ d₁ (fun _ : Fin m => pointBlock) :=
  notMem_IGsem_of_eval_ne (u := 0) (by simp)

end LSG.MEB.Sanity
