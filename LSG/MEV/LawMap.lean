import Mathlib
import LSG.Elliptic.NaturalLaws
import StrongSix.M2.WustholzGen

/-!
# Generic tools for the `E^♮` laws

* `NLaw_map`: the eight laws commute with ring homomorphisms (they are integer polynomials).
* `Fn_map`, `Gn_map`.
* `scw w`: rescaling the variables `v` by `2^{w v}`; `coeff_scw`; **`isWH_of_scw`**
  (characteristic `0`): `scw w f = 2ⁿ f` ⇒ `f` is weighted homogeneous of degree `n`.
* **`mem_FLE_of_isWH`**: a polynomial that is weighted homogeneous of degree `n` for the weight of
  a block `b` and of degree `0` for the weight of the other blocks lies in `FLE (single b n)`.
-/

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (FLE S bdeg)

namespace LSG.MEV

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

set_option maxHeartbeats 1600000 in
-- unfolding the sixteen fibre corrections
theorem NLaw_map (g₂ g₃ : R) (i j k : Fin 2) (P Q : Fin 5 → R) (l : Fin 5) :
    f (NLaw g₂ g₃ i j k P Q l) = NLaw (f g₂) (f g₃) i j k (f ∘ P) (f ∘ Q) l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [NLaw, lawSel, mult, tcoord, kapW, kapV, Pe, law₁, law₂, law₁U, law₁V, law₁W, law₂U,
      law₂V, law₂W, kapW₁VV, kapW₁VW, kapW₁WV, kapW₁WW, kapW₂VV, kapW₂VW, kapW₂WV, kapW₂WW,
      kapV₁VV, kapV₁VW, kapV₁WV, kapV₁WW, kapV₂VV, kapV₂VW, kapV₂WV, kapV₂WW, map_ofNat]

theorem Fn_map (g₂ g₃ : R) (P : Fin 5 → R) : f (Fn g₂ g₃ P) = Fn (f g₂) (f g₃) (f ∘ P) := by
  simp [Fn, F, map_ofNat]

theorem Gn_map (P : Fin 5 → R) : f (Gn P) = Gn (f ∘ P) := by
  simp [Gn, Gfib, map_ofNat]

end Map

section Scale

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K]

/-- Rescaling the variable `v` by `2^{w v}`. -/
noncomputable def scw (w : σ → ℕ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun v => C ((2 : K) ^ w v) * X v

theorem scw_monomial (w : σ → ℕ) (n : σ →₀ ℕ) (c : K) :
    scw w (monomial n c) = monomial n (c * 2 ^ Finsupp.weight w n) := by
  classical
  rw [scw, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [show (∏ v, ((2 : K) ^ w v) ^ n v) = 2 ^ (∑ v, n v • w v) by
    rw [← Finset.prod_pow_eq_pow_sum]; exact Finset.prod_congr rfl fun v _ => by
      rw [← pow_mul, smul_eq_mul, mul_comm]]
  rw [monomial_eq, algebraMap_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), C_mul]
  ring

theorem coeff_scw (w : σ → ℕ) (f : MvPolynomial σ K) (s : σ →₀ ℕ) :
    (scw w f).coeff s = 2 ^ Finsupp.weight w s * f.coeff s := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  rw [coeff_sum]
  simp only [scw_monomial, coeff_monomial]
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (fun h => by
    simp [MvPolynomial.notMem_support_iff.mp h])]
  simp [mul_comm]

/-- **Homogeneity from the scaling by `2`.** -/
theorem isWH_of_scw [CharZero K] {w : σ → ℕ} {f : MvPolynomial σ K} {n : ℕ}
    (h : scw w f = C ((2 : K) ^ n) * f) : f.IsWeightedHomogeneous w n := by
  intro s hs
  have hc := congrArg (fun q => q.coeff s) h
  simp only [coeff_scw, coeff_C_mul] at hc
  have h2 : (2 : K) ^ Finsupp.weight w s = 2 ^ n := mul_right_cancel₀ hs hc
  have : ((2 ^ Finsupp.weight w s : ℕ) : K) = ((2 ^ n : ℕ) : K) := by push_cast; exact h2
  exact Nat.pow_right_injective le_rfl (Nat.cast_injective this)

end Scale

section Block

variable {σ ι : Type*} [Fintype σ] [DecidableEq ι] {K : Type*} [Field K] {β : σ → ι}

/-- The weight of the block `b`. -/
def wb (β : σ → ι) (b : ι) : σ → ℕ := fun v => if β v = b then 1 else 0

/-- The weight of the other blocks. -/
def wo (β : σ → ι) (b : ι) : σ → ℕ := fun v => if β v = b then 0 else 1

theorem bdeg_eq_weight (s : σ →₀ ℕ) (b : ι) : bdeg β s b = Finsupp.weight (wb β b) s := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), bdeg]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [wb, smul_eq_mul]
  split_ifs <;> simp

theorem bdeg_le_weight_wo (s : σ →₀ ℕ) {b b' : ι} (h : b' ≠ b) :
    bdeg β s b' ≤ Finsupp.weight (wo β b) s := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), bdeg]
  refine Finset.sum_le_sum fun v _ => ?_
  simp only [wo, smul_eq_mul]
  split_ifs with h1 h2 <;> simp_all

/-- **Block degrees from weighted homogeneity.** -/
theorem mem_FLE_of_isWH {f : MvPolynomial σ K} {b : ι} {n : ℕ}
    (h1 : f.IsWeightedHomogeneous (wb β b) n) (h0 : f.IsWeightedHomogeneous (wo β b) 0) :
    f ∈ FLE K β (Pi.single b n) := by
  classical
  rw [FLE, mem_restrictSupport_iff]
  intro s hs
  have hs' : f.coeff s ≠ 0 := mem_support_iff.mp hs
  intro b'
  by_cases hb : b' = b
  · subst hb; rw [bdeg_eq_weight, h1 hs']; simp
  · have := bdeg_le_weight_wo (β := β) s hb
    rw [h0 hs'] at this
    simp only [nonpos_iff_eq_zero] at this
    rw [this]; exact Nat.zero_le _

end Block

end LSG.MEV
