/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.BetaPeriods

/-!
# a5 (rank part): the four periods `z([ζᵉ]γ)`, `e = 0, 1, 2, 3`, are `ℝ`-linearly independent

`perVec e = (∫_{[ζᵉ]γ} dX/Y, ∫_{[ζᵉ]γ} X dX/Y) ∈ ℂ²`. By `curveIntegral_cycleE`, `perVec e j = c_j · (ζ^{j+1})ᵉ` with
`c_j = ((−1)^j/5)(1 − ζ^{j+1}) B((j+1)/5, (j+1)/5) ≠ 0`. A real relation `Σ gₑ perVec e = 0` gives
`Σ gₑ xᵉ = 0` at `x = ζ, ζ²`, hence (real coefficients, complex conjugation) also at `ζ⁴, ζ³`: a polynomial of degree
`≤ 3` with 4 distinct roots vanishes (**`linearIndependent_perVec`**). So the periods span a lattice of rank 4 in
`ℂ² ≅ ℝ⁴` (a Vandermonde argument; ABVAR §2.1).
-/

noncomputable section

open Complex Polynomial

namespace LSG.JacAn.Beta

/-- The period vector of `[ζᵉ]γ`. -/
def perVec (e : ℕ) : Fin 2 → ℂ := fun j => ∫ᶜ p in cycleE e, omegaJ j p

/-- `c_j = ((−1)^j/5)(1 − ζ^{j+1}) B((j+1)/5, (j+1)/5)`. -/
def cJ (j : ℕ) : ℂ :=
  (-1) ^ j / 5 * (1 - zetaN 5 ^ (j + 1)) * betaIntegral (((j : ℂ) + 1) / 5) (((j : ℂ) + 1) / 5)

lemma perVec_eq (e : ℕ) (j : Fin 2) : perVec e j = cJ j * (zetaN 5 ^ ((j : ℕ) + 1)) ^ e := by
  rw [perVec, curveIntegral_cycleE, cJ]
  rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm ((j : ℕ) + 1) e,
    show (e + 1) * ((j : ℕ) + 1) = e * ((j : ℕ) + 1) + ((j : ℕ) + 1) by ring, pow_add]
  ring

lemma cJ_ne_zero {j : ℕ} (hj : j < 4) : cJ j ≠ 0 := by
  have hζ := zetaN_prim 5 (by norm_num)
  refine mul_ne_zero (mul_ne_zero (div_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)) ?_) ?_
  · intro h
    exact hζ.pow_ne_one_of_pos_of_lt (l := j + 1) (by omega) (by omega) (by linear_combination -h)
  · rw [← betaG_eq]
    have hre : 0 < (((j : ℂ) + 1) / 5).re := by
      rw [show ((j : ℂ) + 1) / 5 = (((j : ℝ) + 1) / 5 : ℝ) by push_cast; ring, Complex.ofReal_re]
      positivity
    have hre2 : 0 < (((j : ℂ) + 1) / 5 + ((j : ℂ) + 1) / 5).re := by simp only [add_re]; linarith
    exact div_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hre) (Complex.Gamma_ne_zero_of_re_pos hre))
      (Complex.Gamma_ne_zero_of_re_pos hre2)

lemma conj_zetaN5 : (starRingEnd ℂ) (zetaN 5) = zetaN 5 ^ 4 := by
  have hζ := zetaN_prim 5 (by norm_num)
  have h5 : zetaN 5 ^ 5 = 1 := hζ.pow_eq_one
  have hne : zetaN 5 ≠ 0 := hζ.ne_zero (by norm_num)
  have hc : (starRingEnd ℂ) (zetaN 5) = (zetaN 5)⁻¹ := by
    rw [zetaN, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [Complex.conj_ofReal, map_div₀, map_ofNat]
    ring
  rw [hc]
  exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h5])).symm

/-- **The four periods are `ℝ`-linearly independent.** -/
theorem linearIndependent_perVec : LinearIndependent ℝ (fun e : Fin 4 => perVec e) := by
  have hζ := zetaN_prim 5 (by norm_num)
  set ζ := zetaN 5
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- the polynomial `P = Σ gₑ Xᵉ` vanishes at `ζ^{j+1}`, `j = 0, 1`
  set P : ℂ[X] := ∑ e : Fin 4, C ((g e : ℝ) : ℂ) * X ^ (e : ℕ)
  have hev : ∀ x : ℂ, P.eval x = ∑ e : Fin 4, (g e : ℂ) * x ^ (e : ℕ) := fun x => by
    simp [P, eval_finsetSum]
  have hroot : ∀ j : Fin 2, P.eval (ζ ^ ((j : ℕ) + 1)) = 0 := by
    intro j
    have h := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, perVec_eq, Complex.real_smul] at h
    have hc := cJ_ne_zero (j := j) (by omega)
    rw [hev]
    have : cJ j * ∑ e : Fin 4, (g e : ℂ) * (ζ ^ ((j : ℕ) + 1)) ^ (e : ℕ) = 0 := by
      rw [Finset.mul_sum, ← h]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    exact (mul_eq_zero.mp this).resolve_left hc
  -- conjugate roots
  have hconj : ∀ x : ℂ, P.eval ((starRingEnd ℂ) x) = (starRingEnd ℂ) (P.eval x) := fun x => by
    rw [hev, hev, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [Complex.conj_ofReal]
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have r1 : P.eval ζ = 0 := by simpa using hroot 0
  have r2 : P.eval (ζ ^ 2) = 0 := by simpa using hroot 1
  have r4 : P.eval (ζ ^ 4) = 0 := by rw [← conj_zetaN5, hconj, r1, map_zero]
  have r3 : P.eval (ζ ^ 3) = 0 := by
    have : (starRingEnd ℂ) (ζ ^ 2) = ζ ^ 3 := by
      rw [map_pow, conj_zetaN5, ← pow_mul]
      calc ζ ^ (4 * 2) = ζ ^ 5 * ζ ^ 3 := by rw [← pow_add]
        _ = ζ ^ 3 := by rw [h5, one_mul]
    rw [← this, hconj, r2, map_zero]
  have hinj : Function.Injective (fun i : Fin 4 => ζ ^ ((i : ℕ) + 1)) := by
    intro a b hab
    have := hζ.pow_inj (by omega : (a : ℕ) + 1 < 5) (by omega : (b : ℕ) + 1 < 5) hab
    exact Fin.ext (by omega)
  have hP : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj (fun i => ?_) ?_
    · fin_cases i
      · simpa using r1
      · simpa using r2
      · simpa using r3
      · simpa using r4
    · have : P.natDegree ≤ 3 := by
        refine natDegree_sum_le_of_forall_le _ _ fun e _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
        exact Nat.lt_succ_iff.mp e.2
      simp only [Fintype.card_fin]; omega
  intro i
  have h := congrArg (fun q : ℂ[X] => q.coeff (i : ℕ)) hP
  simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at h
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro b _ hb
    have : (i : ℕ) ≠ (b : ℕ) := fun h' => hb (Fin.ext h'.symm)
    simp [this]
  · simp

end LSG.JacAn.Beta
