/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Polarization: vanishing along finitely many directions of a grid (Stage 3, D3)

* `iteratedDeriv_line`: `d^k/ds^k f(y + s v) |_{s=s₀} = D^k f(y + s₀ v)(v, …, v)`.
* **`iteratedDeriv_line_eq_zero_of_grid`**: if the `k`-th derivative of `s ↦ f(y + s Σ cᵢ wᵢ)` at `0`
  vanishes for all `c ∈ {0, …, k}^τ`, it vanishes for all `c ∈ ℂ^τ` (the derivative is a
  homogeneous polynomial of degree `k` in `c`; Alon's combinatorial Nullstellensatz,
  `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`).
* `iteratedDeriv_line_eq_zero_of_span`: the same for all `v` in the span of the `wᵢ`.
-/

open Finset
open scoped ContDiff

namespace LSG.Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Iterated derivatives along a line. -/
theorem iteratedDeriv_line {f : E → ℂ} (hf : ContDiff ℂ ∞ f) (y v : E) (k : ℕ) (s₀ : ℂ) :
    iteratedDeriv k (fun s : ℂ => f (y + s • v)) s₀ =
      iteratedFDeriv ℂ k f (y + s₀ • v) (fun _ => v) := by
  induction k generalizing s₀ with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv k (fun s : ℂ => f (y + s • v)) =
        fun s => iteratedFDeriv ℂ k f (y + s • v) (fun _ => v) := funext ih
    rw [hfun]
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k f) (y + s₀ • v) :=
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) _
    have hline : HasDerivAt (fun s : ℂ => y + s • v) v s₀ := by
      simpa using ((hasDerivAt_id s₀).smul_const v).const_add y
    have h1 := (hd.hasFDerivAt.comp_hasDerivAt s₀ hline)
    have h2 := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => E) ℂ
      (fun _ => v)).hasFDerivAt.comp_hasDerivAt s₀ h1
    have h3 : (fun s : ℂ => iteratedFDeriv ℂ k f (y + s • v) (fun _ => v)) =
        (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => E) ℂ (fun _ => v)) ∘
          (iteratedFDeriv ℂ k f ∘ fun s => y + s • v) := rfl
    rw [h3, h2.deriv, iteratedFDeriv_succ_apply_left]
    rfl

/-- **Polarization on a grid.** -/
theorem iteratedDeriv_line_eq_zero_of_grid {f : E → ℂ} (hf : ContDiff ℂ ∞ f) (y : E) {τ : ℕ}
    (w : Fin τ → E) (k : ℕ)
    (h : ∀ c : Fin τ → ℕ, (∀ i, c i ≤ k) →
      iteratedDeriv k (fun s : ℂ => f (y + s • ∑ i, (c i : ℂ) • w i)) 0 = 0)
    (c : Fin τ → ℂ) : iteratedDeriv k (fun s : ℂ => f (y + s • ∑ i, c i • w i)) 0 = 0 := by
  classical
  set A := iteratedFDeriv ℂ k f y
  -- the derivative as a polynomial in `c`
  have hexp : ∀ c : Fin τ → ℂ, A (fun _ => ∑ i, c i • w i) =
      ∑ r : Fin k → Fin τ, (∏ j, c (r j)) * A (fun j => w (r j)) := by
    intro c
    rw [A.map_sum (fun _ i => c i • w i)]
    refine sum_congr rfl fun r _ => ?_
    rw [A.map_smul_univ (fun j => c (r j)) (fun j => w (r j)), smul_eq_mul]
  set Q : MvPolynomial (Fin τ) ℂ :=
    ∑ r : Fin k → Fin τ, MvPolynomial.C (A (fun j => w (r j))) * ∏ j, MvPolynomial.X (r j)
  have hQ : ∀ c, MvPolynomial.eval c Q = A (fun _ => ∑ i, c i • w i) := by
    intro c
    rw [hexp]
    simp only [Q, map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine sum_congr rfl fun r _ => by ring
  have hline : ∀ c : Fin τ → ℂ, iteratedDeriv k (fun s : ℂ => f (y + s • ∑ i, c i • w i)) 0 =
      A (fun _ => ∑ i, c i • w i) := by
    intro c
    rw [iteratedDeriv_line hf y _ k 0, zero_smul, add_zero]
  have hdeg : ∀ i, MvPolynomial.degreeOf i Q < ((range (k + 1)).image (fun n : ℕ => (n : ℂ))).card := by
    intro i
    rw [card_image_of_injective _ Nat.cast_injective, card_range]
    have htot : Q.totalDegree ≤ k := by
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun r _ => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      simp [MvPolynomial.totalDegree_X]
    exact Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_totalDegree Q i).trans htot)
  have hQ0 : Q = 0 := by
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q (fun _ => (range (k + 1)).image
      (fun n : ℕ => (n : ℂ))) hdeg fun x hx => ?_
    choose n hn hxn using fun i => mem_image.mp (hx i)
    have hx' : x = fun i => ((n i : ℕ) : ℂ) := funext fun i => (hxn i).symm
    rw [hQ, ← hline, hx']
    exact h n fun i => Nat.lt_succ_iff.mp (mem_range.mp (hn i))
  rw [hline, ← hQ, hQ0, map_zero]

/-- Polarization for all vectors of a span. -/
theorem iteratedDeriv_line_eq_zero_of_span {f : E → ℂ} (hf : ContDiff ℂ ∞ f) (y : E) {τ : ℕ}
    (w : Fin τ → E) (k : ℕ)
    (h : ∀ c : Fin τ → ℕ, (∀ i, c i ≤ k) →
      iteratedDeriv k (fun s : ℂ => f (y + s • ∑ i, (c i : ℂ) • w i)) 0 = 0)
    {v : E} (hv : v ∈ Submodule.span ℂ (Set.range w)) :
    iteratedDeriv k (fun s : ℂ => f (y + s • v)) 0 = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp hv
  exact iteratedDeriv_line_eq_zero_of_grid hf y w k h c

end LSG.Aux
