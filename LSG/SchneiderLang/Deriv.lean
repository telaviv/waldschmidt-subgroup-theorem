/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.SchneiderLang.Hsum

/-!
# Derivatives of polynomial expressions

Let `u : ℂ → ℂ^N` with `u_i' = c · Q̂_i(u)` on an open set `U`, where `Q̂_i` are polynomials over a
ring `R` (mapped to `ℂ` by `φ`). With the derivation `Dop Q̂ = ∑ᵢ Q̂ᵢ ∂ᵢ` on `R[X₁, …, X_N]`,

  `(d/dz)^k P(u(z)) = c^k · (Dop^k P)(u(z))`   on `U`.

Over `R = 𝓞 K` we bound the degree and the house-length of `Dop^k P`.

We also rescale a system with coefficients in a number field `K` to one with algebraic integer
coefficients (`exists_scaled`) and produce common denominators (`exists_common_denom`).
-/

open MvPolynomial Finset NumberField Filter Topology

namespace LSG.SL

section Generic

variable {R : Type*} [CommRing R] {N : ℕ}

/-- Chain rule for polynomial expressions in differentiable functions. -/
theorem hasDerivAt_eval₂ (φ : R →+* ℂ) (P : MvPolynomial (Fin N) R) {u : ℂ → Fin N → ℂ}
    {u' : Fin N → ℂ} {z : ℂ} (hu : ∀ i, HasDerivAt (fun x => u x i) (u' i) z) :
    HasDerivAt (fun x => eval₂ φ (u x) P) (∑ i, eval₂ φ (u z) (pderiv i P) * u' i) z := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [pderiv_C] using hasDerivAt_const z (φ a)
  | add p q hp hq =>
    convert hp.add hq using 1
    · funext x; simp [eval₂_add]
    · simp [eval₂_add, map_add, add_mul, sum_add_distrib]
  | mul_X p j hp =>
    have h := hp.mul (hu j)
    simp only [eval₂_mul, eval₂_X]
    convert h using 1
    have h2 : ∀ i, eval₂ φ (u z) (pderiv i (p * X j)) * u' i =
        eval₂ φ (u z) (pderiv i p) * u' i * u z j +
          (if j = i then eval₂ φ (u z) p * u' j else 0) := by
      intro i
      rw [pderiv_mul, eval₂_add, eval₂_mul, eval₂_mul, eval₂_X]
      by_cases hij : j = i
      · subst hij; simp; ring
      · rw [pderiv_X_of_ne hij]; simp [hij]; ring
    simp only [h2, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, sum_mul]

/-- The derivation `∑ᵢ Q̂ᵢ ∂ᵢ`. -/
noncomputable def Dop (Qh : Fin N → MvPolynomial (Fin N) R) : Module.End R (MvPolynomial (Fin N) R) :=
  ∑ i, LinearMap.mulRight R (Qh i) ∘ₗ (pderiv i).toLinearMap

theorem Dop_apply (Qh : Fin N → MvPolynomial (Fin N) R) (P : MvPolynomial (Fin N) R) :
    Dop Qh P = ∑ i, pderiv i P * Qh i := by
  simp [Dop]

theorem hasDerivAt_Dop (φ : R →+* ℂ) (Qh : Fin N → MvPolynomial (Fin N) R) {u : ℂ → Fin N → ℂ}
    {z c : ℂ} (hu : ∀ i, HasDerivAt (fun x => u x i) (c * eval₂ φ (u z) (Qh i)) z)
    (P : MvPolynomial (Fin N) R) :
    HasDerivAt (fun x => eval₂ φ (u x) P) (c * eval₂ φ (u z) (Dop Qh P)) z := by
  convert hasDerivAt_eval₂ φ P hu using 1
  rw [Dop_apply, eval₂_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval₂_mul]
  ring

/-- Iterated derivatives of polynomial expressions. -/
theorem iteratedDeriv_eval₂_Dop (φ : R →+* ℂ) (Qh : Fin N → MvPolynomial (Fin N) R)
    {u : ℂ → Fin N → ℂ} {U : Set ℂ} (hU : IsOpen U) (c : ℂ)
    (hu : ∀ z ∈ U, ∀ i, HasDerivAt (fun x => u x i) (c * eval₂ φ (u z) (Qh i)) z)
    (P : MvPolynomial (Fin N) R) (k : ℕ) :
    ∀ z ∈ U, iteratedDeriv k (fun x => eval₂ φ (u x) P) z =
      c ^ k * eval₂ φ (u z) ((Dop Qh ^ k) P) := by
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun x => eval₂ φ (u x) P) =ᶠ[𝓝 z]
        fun x => c ^ k * eval₂ φ (u x) ((Dop Qh ^ k) P) := by
      filter_upwards [hU.mem_nhds hz] with x hx using ih x hx
    rw [heq.deriv_eq]
    rw [((hasDerivAt_Dop φ Qh (hu z hz) ((Dop Qh ^ k) P)).const_mul (c ^ k)).deriv,
      pow_succ' (Dop Qh) k, Module.End.mul_apply]
    ring

theorem pderiv_eq_sum (i : Fin N) (P : MvPolynomial (Fin N) R) :
    pderiv i P = ∑ α ∈ P.support, monomial (α - Finsupp.single i 1) (P.coeff α * (α i : R)) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  simp only [pderiv_monomial]

theorem totalDegree_pderiv_le (i : Fin N) (P : MvPolynomial (Fin N) R) :
    (pderiv i P).totalDegree ≤ P.totalDegree := by
  rw [pderiv_eq_sum]
  refine totalDegree_finsetSum_le fun α hα => (totalDegree_monomial_le _ _).trans ?_
  exact (Finsupp.degree_mono tsub_le_self).trans (le_totalDegree hα)

theorem totalDegree_Dop_le (Qh : Fin N → MvPolynomial (Fin N) R) {δ : ℕ}
    (hδ : ∀ i, (Qh i).totalDegree ≤ δ) (P : MvPolynomial (Fin N) R) :
    (Dop Qh P).totalDegree ≤ P.totalDegree + δ := by
  rw [Dop_apply]
  refine totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans ?_
  exact add_le_add (totalDegree_pderiv_le i P) (hδ i)

theorem totalDegree_Dop_pow_le (Qh : Fin N → MvPolynomial (Fin N) R) {δ : ℕ}
    (hδ : ∀ i, (Qh i).totalDegree ≤ δ) (P : MvPolynomial (Fin N) R) (k : ℕ) :
    ((Dop Qh ^ k) P).totalDegree ≤ P.totalDegree + k * δ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    refine (totalDegree_Dop_le Qh hδ _).trans ?_
    rw [add_mul, one_mul, ← add_assoc]
    exact add_le_add_left ih δ

end Generic

section Integral

variable {K : Type*} [Field K] [NumberField K] {N : ℕ}

theorem hsum_Dop_le (Qh : Fin N → MvPolynomial (Fin N) (𝓞 K)) {B : ℝ}
    (hB : ∀ i, hsum (Qh i) ≤ B) (P : MvPolynomial (Fin N) (𝓞 K)) :
    hsum (Dop Qh P) ≤ N * P.totalDegree * hsum P * B := by
  rw [Dop_apply]
  refine (hsum_sum_le _ _).trans ?_
  have : ∀ i ∈ (univ : Finset (Fin N)), hsum (pderiv i P * Qh i) ≤ P.totalDegree * hsum P * B := by
    intro i _
    refine (hsum_mul_le _ _).trans ?_
    exact mul_le_mul (hsum_pderiv_le i P) (hB i) (hsum_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hsum_nonneg _))
  refine (sum_le_sum this).trans ?_
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  rfl

theorem hsum_Dop_pow_le (Qh : Fin N → MvPolynomial (Fin N) (𝓞 K)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i, hsum (Qh i) ≤ B) {δ : ℕ} (hδ : ∀ i, (Qh i).totalDegree ≤ δ)
    (P : MvPolynomial (Fin N) (𝓞 K)) {D : ℕ} (hD : P.totalDegree ≤ D) (k : ℕ) :
    hsum ((Dop Qh ^ k) P) ≤ (N * B * (D + k * δ)) ^ k * hsum P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    refine (hsum_Dop_le Qh hB _).trans ?_
    have hdeg : (((Dop Qh ^ k) P).totalDegree : ℝ) ≤ D + (k + 1) * δ := by
      have := totalDegree_Dop_pow_le Qh hδ P k
      have h2 : ((Dop Qh ^ k) P).totalDegree ≤ D + (k + 1) * δ := by nlinarith
      exact_mod_cast h2
    have hmono : (N * B * (D + k * δ) : ℝ) ≤ N * B * (D + (k + 1) * δ) := by
      have : (D + k * δ : ℝ) ≤ D + (k + 1) * δ := by nlinarith [(Nat.cast_nonneg δ : (0:ℝ) ≤ δ)]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hX0 : (0 : ℝ) ≤ N * B * (D + k * δ) := by positivity
    calc (N : ℝ) * ((Dop Qh ^ k) P).totalDegree * hsum ((Dop Qh ^ k) P) * B
        = (N * B * ((Dop Qh ^ k) P).totalDegree) * hsum ((Dop Qh ^ k) P) := by ring
      _ ≤ (N * B * (D + (k + 1) * δ)) * ((N * B * (D + k * δ)) ^ k * hsum P) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hdeg (by positivity)) ih
            (hsum_nonneg _) (by positivity)
      _ ≤ (N * B * (D + (k + 1) * δ)) * ((N * B * (D + (k + 1) * δ)) ^ k * hsum P) := by
          have := hsum_nonneg P
          gcongr
      _ = (N * B * (D + ((k + 1 : ℕ) : ℝ) * δ)) ^ (k + 1) * hsum P := by
          push_cast; ring

/-- House of the values of `Dop^k P`. -/
theorem house_eval_Dop_pow_le (Qh : Fin N → MvPolynomial (Fin N) (𝓞 K)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i, hsum (Qh i) ≤ B) {δ : ℕ} (hδ : ∀ i, (Qh i).totalDegree ≤ δ)
    (P : MvPolynomial (Fin N) (𝓞 K)) {D : ℕ} (hD : P.totalDegree ≤ D) (k : ℕ)
    (y : Fin N → 𝓞 K) {Y : ℝ} (hY1 : 1 ≤ Y) (hY : ∀ i, house ((y i : 𝓞 K) : K) ≤ Y) :
    house ((eval y ((Dop Qh ^ k) P) : 𝓞 K) : K) ≤
      (N * B * (D + k * δ)) ^ k * hsum P * Y ^ (D + k * δ) := by
  refine (house_eval_le _ y hY1 hY ((totalDegree_Dop_pow_le Qh hδ P k).trans
    (add_le_add_left hD _))).trans ?_
  -- note: the degree bound is `P.totalDegree + k δ ≤ D + k δ`
  exact mul_le_mul_of_nonneg_right (hsum_Dop_pow_le Qh hB0 hB hδ P hD k) (by positivity)

omit [NumberField K] in
/-- Rescaling to algebraic integer coefficients: `Q̂(d₀ x) = d₀^{δ+1} Q(x)`. -/
theorem exists_scaled (σ : K →+* ℂ) (Q : MvPolynomial (Fin N) K) (d₀ : ℕ)
    (hd : ∀ α, IsIntegral ℤ ((d₀ : K) * Q.coeff α)) {δ : ℕ} (hδ : Q.totalDegree ≤ δ) :
    ∃ Qh : MvPolynomial (Fin N) (𝓞 K), Qh.totalDegree ≤ δ ∧ ∀ x : Fin N → ℂ,
      eval₂ (σ.comp (algebraMap (𝓞 K) K)) (fun i => (d₀ : ℂ) * x i) Qh =
        (d₀ : ℂ) ^ (δ + 1) * eval₂ σ x Q := by
  classical
  have hint : ∀ α, IsIntegral ℤ ((d₀ : K) ^ (δ - α.degree) * ((d₀ : K) * Q.coeff α)) :=
    fun α => ((show IsIntegral ℤ (d₀ : K) from by
      simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (d₀ : ℤ))).pow _).mul (hd α)
  let lift : (Fin N →₀ ℕ) → 𝓞 K := fun α => ⟨_, hint α⟩
  refine ⟨∑ α ∈ Q.support, monomial α (lift α), ?_, fun x => ?_⟩
  · refine totalDegree_finsetSum_le fun α hα => (totalDegree_monomial_le _ _).trans ?_
    exact (le_totalDegree hα).trans hδ
  · conv_rhs => rw [Q.as_sum]
    rw [eval₂_sum, eval₂_sum, mul_sum]
    refine sum_congr rfl fun α hα => ?_
    rw [eval₂_monomial, eval₂_monomial]
    have hdeg : α.degree ≤ δ := (le_totalDegree hα).trans hδ
    have hlift : (σ.comp (algebraMap (𝓞 K) K)) (lift α) =
        (d₀ : ℂ) ^ (δ - α.degree) * ((d₀ : ℂ) * σ (Q.coeff α)) := by
      change σ ((d₀ : K) ^ (δ - α.degree) * ((d₀ : K) * Q.coeff α)) = _
      simp only [map_mul, map_pow, map_natCast]
    have hprod : (α.prod fun n e => ((d₀ : ℂ) * x n) ^ e) =
        (d₀ : ℂ) ^ α.degree * α.prod fun n e => x n ^ e := by
      simp only [Finsupp.prod, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]
      rfl
    rw [hlift, hprod]
    have : (d₀ : ℂ) ^ (δ + 1) = (d₀ : ℂ) ^ (δ - α.degree) * (d₀ : ℂ) * (d₀ : ℂ) ^ α.degree := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega
    rw [this]
    ring

/-- A common denominator for a finite set of elements of a number field. -/
theorem exists_common_denom (s : Finset K) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ x ∈ s, IsIntegral ℤ ((d₀ : K) * x) := by
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨m.natAbs, Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm0), fun x hx => ?_⟩
  have hmem := hm x hx
  rw [zsmul_eq_mul] at hmem
  rcases Int.natAbs_eq m with h | h
  · have : ((m.natAbs : ℕ) : K) = (m : K) := by rw [← Int.cast_natCast, ← h]
    rw [this]; exact hmem
  · have : ((m.natAbs : ℕ) : K) = -(m : K) := by
      rw [← Int.cast_natCast]
      have h' : (m.natAbs : ℤ) = -m := by omega
      rw [h']; push_cast; ring
    rw [this, neg_mul]; exact hmem.neg

end Integral

end LSG.SL
