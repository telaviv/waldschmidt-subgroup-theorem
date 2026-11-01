/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The Euler–Jacobi identity

For distinct nodes `v i` (`i ∈ s`) in a field and a polynomial `p` with `deg p + 2 ≤ #s`,

  `∑_{i ∈ s} p(v i) / ∏_{j ≠ i} (v i − v j) = 0`        (`sum_nodalWeight_mul_eval_eq_zero`).

Proof: the left side is the coefficient of `X^{#s−1}` of the Lagrange interpolant of `p`, which is `p` itself.

In derivative form (`eulerJacobi_roots`): if `R` has `#s = deg R` distinct roots `v i`, then
`∑_i q(v i) / R'(v i) = 0` whenever `deg q ≤ deg R − 2`. This is the algebraic core of Abel's theorem (ABVAR §2.2 a2).
-/

noncomputable section

open Polynomial Finset Lagrange

namespace LSG.JacAn

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- The top coefficient (degree `#s − 1`) of the Lagrange interpolant. -/
theorem coeff_interpolate_card_sub_one (s : Finset ι) (v : ι → F) (r : ι → F) :
    (interpolate s v r).coeff (#s - 1) = ∑ i ∈ s, nodalWeight s v i * r i := by
  rw [interpolate_apply, finsetSum_coeff]
  refine sum_congr rfl fun i hi => ?_
  rw [basis_eq_prod_sub_inv_mul_nodal_div hi, ← nodal_erase_eq_nodal_div hi, ← mul_assoc, ← C_mul,
    coeff_C_mul]
  have : #s - 1 = (nodal (s.erase i) v).natDegree := by rw [natDegree_nodal, card_erase_of_mem hi]
  rw [this, nodal_monic.coeff_natDegree, mul_one, mul_comm]

/-- **Euler–Jacobi, nodal-weight form.** -/
theorem sum_nodalWeight_mul_eval_eq_zero {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) {p : F[X]}
    (hp : p.natDegree + 2 ≤ #s) : ∑ i ∈ s, nodalWeight s v i * p.eval (v i) = 0 := by
  have hdeg : p.degree < #s :=
    lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (by omega : p.natDegree < #s))
  have h := coeff_interpolate_card_sub_one s v (fun i => p.eval (v i))
  rw [← eq_interpolate hvs hdeg] at h
  rw [← h]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Euler–Jacobi, product form**: `∑_i p(v i) / ∏_{j ≠ i} (v i − v j) = 0` for `deg p + 2 ≤ #s`. -/
theorem sum_eval_div_prod_eq_zero {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) {p : F[X]}
    (hp : p.natDegree + 2 ≤ #s) :
    ∑ i ∈ s, p.eval (v i) / ∏ j ∈ s.erase i, (v i - v j) = 0 := by
  rw [← sum_nodalWeight_mul_eval_eq_zero hvs hp]
  refine sum_congr rfl fun i _ => ?_
  rw [nodalWeight, prod_inv_distrib, div_eq_mul_inv, mul_comm]

omit [DecidableEq ι] in
/-- A polynomial with `#s = deg R` distinct roots `v i` is `lc(R) · ∏ (X − v i)`. -/
theorem eq_C_leadingCoeff_mul_nodal {R : F[X]} {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s)
    (hdeg : R.natDegree = #s) (hroot : ∀ i ∈ s, R.eval (v i) = 0) :
    R = C R.leadingCoeff * nodal s v := by
  by_cases hR : R = 0
  · simp [hR]
  have hlc : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  refine eq_of_degree_sub_lt_of_eval_index_eq s hvs ?_ ?_
  · have h1 : R.degree = #s := by rw [degree_eq_natDegree hR, hdeg]
    have h2 : (C R.leadingCoeff * nodal s v).degree = R.degree := by
      rw [degree_C_mul hlc, degree_nodal, h1]
    rw [← h1]
    refine degree_sub_lt_left h2.symm hR ?_
    rw [leadingCoeff_mul, leadingCoeff_C, nodal_monic.leadingCoeff, mul_one]
  · intro i hi
    rw [hroot i hi, eval_mul, eval_nodal_at_node hi, mul_zero]

/-- `R'(v i) = lc(R) ∏_{j ≠ i} (v i − v j)` at a root, for `R` with `#s = deg R` distinct roots. -/
theorem eval_derivative_eq_of_roots {R : F[X]} {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s)
    (hdeg : R.natDegree = #s) (hroot : ∀ j ∈ s, R.eval (v j) = 0) {i : ι} (hi : i ∈ s) :
    (derivative R).eval (v i) = R.leadingCoeff * ∏ j ∈ s.erase i, (v i - v j) := by
  conv_lhs => rw [eq_C_leadingCoeff_mul_nodal hvs hdeg hroot]
  rw [derivative_C_mul, eval_mul, eval_C, eval_nodal_derivative_eval_node_eq hi, eval_nodal]

omit [DecidableEq ι] in
/-- At a simple root, `R' ≠ 0`. -/
theorem eval_derivative_ne_zero_of_roots {R : F[X]} (hR : R ≠ 0) {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) (hdeg : R.natDegree = #s) (hroot : ∀ j ∈ s, R.eval (v j) = 0) {i : ι}
    (hi : i ∈ s) : (derivative R).eval (v i) ≠ 0 := by
  classical
  rw [eval_derivative_eq_of_roots hvs hdeg hroot hi]
  refine mul_ne_zero (leadingCoeff_ne_zero.mpr hR) (prod_ne_zero_iff.mpr fun j hj => ?_)
  rcases mem_erase.mp hj with ⟨hij, hj⟩
  exact sub_ne_zero_of_ne (mt (hvs.eq_iff hi hj).mp hij.symm)

omit [DecidableEq ι] in
/-- **Euler–Jacobi, derivative form.** If `R` has `#s = deg R` distinct roots `v i` and `deg q + 2 ≤ deg R`, then
`∑_i q(v i) / R'(v i) = 0`. -/
theorem eulerJacobi_roots {R q : F[X]} {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s)
    (hdeg : R.natDegree = #s) (hroot : ∀ j ∈ s, R.eval (v j) = 0) (hq : q.natDegree + 2 ≤ #s) :
    ∑ i ∈ s, q.eval (v i) / (derivative R).eval (v i) = 0 := by
  classical
  have h : ∀ i ∈ s, q.eval (v i) / (derivative R).eval (v i) =
      R.leadingCoeff⁻¹ * (q.eval (v i) / ∏ j ∈ s.erase i, (v i - v j)) := by
    intro i hi
    rw [eval_derivative_eq_of_roots hvs hdeg hroot hi, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  rw [sum_congr rfl h, ← mul_sum, sum_eval_div_prod_eq_zero hvs hq, mul_zero]

end LSG.JacAn
