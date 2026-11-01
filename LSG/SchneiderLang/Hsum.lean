/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The house-length of a polynomial over a ring of integers

For a polynomial `P` with coefficients in the ring of integers `𝓞 K` of a number field `K` we set

  `hsum P = ∑_α house (coeff α P)`.

It is subadditive and submultiplicative, `hsum (∂ᵢ P) ≤ deg P · hsum P`, and it bounds values:
`house (P(y)) ≤ hsum P · Y ^ deg P` when `house yᵢ ≤ Y`, `1 ≤ Y`.
-/

open NumberField Finset MvPolynomial

namespace LSG.SL

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem house_zero' : house (0 : K) = 0 := by
  simpa using house_intCast (K := K) 0

theorem house_one' : house (1 : K) = 1 := by
  simpa using house_intCast (K := K) 1

theorem house_natCast' (n : ℕ) : house (n : K) = n := by
  simpa using house_intCast (K := K) n

theorem house_sum_le' {ι : Type*} (s : Finset ι) (g : ι → K) :
    house (∑ i ∈ s, g i) ≤ ∑ i ∈ s, house (g i) := house_sum_le_sum_house s g

theorem house_prod_le' {ι : Type*} (s : Finset ι) (g : ι → K) :
    house (∏ i ∈ s, g i) ≤ ∏ i ∈ s, house (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [house_one']
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (house_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (house_nonneg _))

/-- The house-length of a polynomial with algebraic integer coefficients. -/
noncomputable def hsum (P : MvPolynomial σ (𝓞 K)) : ℝ :=
  ∑ α ∈ P.support, house ((P.coeff α : 𝓞 K) : K)

theorem hsum_nonneg (P : MvPolynomial σ (𝓞 K)) : 0 ≤ hsum P :=
  sum_nonneg fun _ _ => house_nonneg _

theorem hsum_eq_of_subset (P : MvPolynomial σ (𝓞 K)) {s : Finset (σ →₀ ℕ)}
    (hs : P.support ⊆ s) : hsum P = ∑ α ∈ s, house ((P.coeff α : 𝓞 K) : K) := by
  unfold hsum
  refine sum_subset hs fun α _ hα => ?_
  rw [notMem_support_iff.mp hα]
  simpa using (house_zero' (K := K))

theorem hsum_zero : hsum (0 : MvPolynomial σ (𝓞 K)) = 0 := by
  simp [hsum]

theorem hsum_add_le (P Q : MvPolynomial σ (𝓞 K)) : hsum (P + Q) ≤ hsum P + hsum Q := by
  classical
  have h1 : hsum (P + Q) ≤ ∑ α ∈ P.support ∪ Q.support,
      house (((P + Q).coeff α : 𝓞 K) : K) := by
    unfold hsum
    exact sum_le_sum_of_subset_of_nonneg support_add fun _ _ _ => house_nonneg _
  rw [hsum_eq_of_subset P subset_union_left, hsum_eq_of_subset Q subset_union_right,
    ← sum_add_distrib]
  refine h1.trans (sum_le_sum fun α _ => ?_)
  rw [show (P + Q).coeff α = P.coeff α + Q.coeff α from by simp]
  simp only [RingOfIntegers.coe_eq_algebraMap, map_add]
  exact house_add_le _ _

theorem hsum_sum_le {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ (𝓞 K)) :
    hsum (∑ i ∈ s, P i) ≤ ∑ i ∈ s, hsum (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hsum_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (hsum_add_le _ _).trans (by linarith)

theorem hsum_monomial_le (α : σ →₀ ℕ) (c : 𝓞 K) :
    hsum (monomial α c) ≤ house (c : K) := by
  classical
  rw [hsum_eq_of_subset _ (support_monomial_subset (a := c) (s := α)), sum_singleton,
    coeff_monomial]
  simp

theorem hsum_mul_le (P Q : MvPolynomial σ (𝓞 K)) : hsum (P * Q) ≤ hsum P * hsum Q := by
  classical
  have hPQ : P * Q = ∑ α ∈ P.support, ∑ β ∈ Q.support,
      monomial (α + β) (P.coeff α * Q.coeff β) := by
    conv_lhs => rw [P.as_sum, Q.as_sum]
    rw [sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [hPQ]
  refine (hsum_sum_le _ _).trans ?_
  unfold hsum
  rw [sum_mul_sum]
  refine sum_le_sum fun α _ => (hsum_sum_le _ _).trans (sum_le_sum fun β _ => ?_)
  refine (hsum_monomial_le _ _).trans ?_
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
  exact house_mul_le _ _

theorem hsum_pderiv_le [DecidableEq σ] (i : σ) (P : MvPolynomial σ (𝓞 K)) :
    hsum (pderiv i P) ≤ P.totalDegree * hsum P := by
  have hP : pderiv i P = ∑ α ∈ P.support, monomial (α - Finsupp.single i 1)
      (P.coeff α * (α i : 𝓞 K)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    simp only [pderiv_monomial]
  rw [hP]
  refine (hsum_sum_le _ _).trans ?_
  unfold hsum
  rw [mul_sum]
  refine sum_le_sum fun α hα => (hsum_monomial_le _ _).trans ?_
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
  refine (house_mul_le _ _).trans ?_
  rw [house_natCast', mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (house_nonneg _)
  have h1 : α i ≤ α.degree := by
    rw [Finsupp.degree]
    by_cases hi : i ∈ α.support
    · exact single_le_sum (f := fun j => α j) (fun _ _ => Nat.zero_le _) hi
    · rw [Finsupp.notMem_support_iff.mp hi]; exact Nat.zero_le _
  have h2 : α.degree ≤ P.totalDegree := le_totalDegree hα
  exact_mod_cast h1.trans h2

theorem hsum_X_pow_le (i : σ) (a : ℕ) : hsum (X i ^ a : MvPolynomial σ (𝓞 K)) ≤ 1 := by
  rw [X_pow_eq_monomial]
  refine (hsum_monomial_le _ _).trans ?_
  simp only [map_one, house_one', le_refl]

/-- Values of polynomials. -/
theorem house_eval_le [Fintype σ] (P : MvPolynomial σ (𝓞 K)) (y : σ → 𝓞 K) {Y : ℝ}
    (hY1 : 1 ≤ Y) (hY : ∀ i, house ((y i : 𝓞 K) : K) ≤ Y) {D : ℕ} (hD : P.totalDegree ≤ D) :
    house ((eval y P : 𝓞 K) : K) ≤ hsum P * Y ^ D := by
  rw [eval_eq']
  simp only [map_sum, map_mul, map_prod, map_pow]
  refine (house_sum_le' _ _).trans ?_
  unfold hsum
  rw [sum_mul]
  refine sum_le_sum fun α hα => ?_
  refine (house_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (house_nonneg _))
  refine (house_prod_le' _ _).trans ?_
  have h1 : ∏ i, house ((algebraMap (𝓞 K) K (y i)) ^ α i) ≤ ∏ i, Y ^ α i := by
    refine prod_le_prod₀ (fun _ _ => house_nonneg _) fun i _ => ?_
    rw [house_pow]
    exact pow_le_pow_left₀ (house_nonneg _) (hY i) _
  refine h1.trans ?_
  rw [prod_pow_eq_pow_sum]
  refine pow_le_pow_right₀ hY1 ?_
  have h2 : ∑ i, α i = α.degree := by
    rw [Finsupp.degree]
    exact (sum_subset (subset_univ _) fun i _ hi => Finsupp.notMem_support_iff.mp hi).symm
  rw [h2]
  exact (le_totalDegree hα).trans hD

end LSG.SL
