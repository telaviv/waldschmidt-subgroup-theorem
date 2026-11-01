/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# M2.4b: generic `MvPolynomial` lemmas for the `aBlockV` instance

* `isWH_rename`: renaming along a weight-preserving map preserves weighted homogeneity;
* `isWH_rename_hom`: a homogeneous polynomial renamed into variables of constant weight `u` is weighted homogeneous
  of degree `n • u`;
* **`isWH_pderiv`**: `pderiv i` lowers the weighted degree by `w i`;
* `isWH_sub`, `isWH_of_eq`;
* `eval_smul_of_isHomogeneous`: `φ(c • x) = cⁿ φ(x)`.
-/

noncomputable section

open MvPolynomial

namespace LSG.JacBlockV

variable {σ τ M : Type*}

lemma isWH_of_eq [AddCommMonoid M] {w : σ → M} {φ : MvPolynomial σ ℂ} {n n' : M}
    (h : φ.IsWeightedHomogeneous w n) (e : n = n') : φ.IsWeightedHomogeneous w n' := e ▸ h

lemma isWH_sub [AddCommMonoid M] {w : σ → M} {φ ψ : MvPolynomial σ ℂ} {n : M}
    (hφ : φ.IsWeightedHomogeneous w n) (hψ : ψ.IsWeightedHomogeneous w n) :
    (φ - ψ).IsWeightedHomogeneous w n :=
  (mem_weightedHomogeneousSubmodule ℂ w n _).mp
    (Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule ℂ w n _).mpr hφ)
      ((mem_weightedHomogeneousSubmodule ℂ w n _).mpr hψ))

lemma isWH_rename [AddCommMonoid M] {w : σ → M} {w' : τ → M} {f : σ → τ} (hw : ∀ i, w' (f i) = w i)
    {φ : MvPolynomial σ ℂ} {n : M} (h : φ.IsWeightedHomogeneous w n) :
    (rename f φ).IsWeightedHomogeneous w' n := by
  rw [← φ.support_sum_monomial_coeff, map_sum]
  simp_rw [rename_monomial]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => isWeightedHomogeneous_monomial _ _ _ ?_
  rw [← h (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • w' i) (fun _ => zero_smul ℕ _)
      (fun _ _ _ => add_smul _ _ _)]
  simp [hw]

lemma isWH_rename_hom [AddCommMonoid M] {w' : τ → M} {f : σ → τ} {u : M} (hw : ∀ i, w' (f i) = u)
    {φ : MvPolynomial σ ℂ} {n : ℕ} (h : φ.IsHomogeneous n) :
    (rename f φ).IsWeightedHomogeneous w' (n • u) := by
  rw [← φ.support_sum_monomial_coeff, map_sum]
  simp_rw [rename_monomial]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => isWeightedHomogeneous_monomial _ _ _ ?_
  have hn := h (mem_support_iff.mp hd)
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • w' i) (fun _ => zero_smul ℕ _)
    (fun _ _ _ => add_smul _ _ _)]
  simp only [hw]
  rw [← hn, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_smul]
  simp

/-- **`pderiv i` lowers the weighted degree by `w i`.** -/
theorem isWH_pderiv [AddCancelCommMonoid M] {w : σ → M} {φ : MvPolynomial σ ℂ} {d d' : M}
    (h : φ.IsWeightedHomogeneous w d) (i : σ) (hd : d' + w i = d) :
    (pderiv i φ).IsWeightedHomogeneous w d' := by
  classical
  rw [← φ.support_sum_monomial_coeff, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  rw [pderiv_monomial]
  by_cases hsi : s i = 0
  · rw [hsi, Nat.cast_zero, mul_zero, monomial_zero]
    exact isWeightedHomogeneous_zero _ _ _
  · apply isWeightedHomogeneous_monomial
    have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hsi)
    have e : Finsupp.weight w (s - Finsupp.single i 1) + w i = Finsupp.weight w s := by
      rw [← one_nsmul (w i), ← Finsupp.weight_single, ← map_add, tsub_add_cancel_of_le hle]
    have hs' := h (mem_support_iff.mp hs)
    exact add_right_cancel (e.trans (hs'.trans hd.symm))

/-- `φ(c • x) = cⁿ φ(x)` for `φ` homogeneous of degree `n`. -/
theorem eval_smul_of_isHomogeneous {φ : MvPolynomial σ ℂ} {n : ℕ} (h : φ.IsHomogeneous n) (c : ℂ)
    (x : σ → ℂ) : eval (c • x) φ = c ^ n * eval x φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := h (mem_support_iff.mp hs)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finsupp.prod_mul, ← hd]
  have : (s.prod fun _ e => c ^ e) = c ^ Finsupp.weight 1 s := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum]
    simp
  rw [this]; ring

end LSG.JacBlockV
