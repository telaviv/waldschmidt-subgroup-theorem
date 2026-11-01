/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.FpolyV
import LSG.AuxFun.MonoIndep

/-!
# `P ∘ exp_G ≢ 0` for the class `𝒞` (Stage 5, phase 2)

Monomials whose elliptic part is `(σ³)^{D−Φ−a_j}(σ³℘)^{a_j}` (`γ_{j,2} = 0`) times fibre forms
`Π S_i^{φ_i}` are linearly independent as functions on `T_G`: off the lattices
`M(x) = Π_j σ_j(z_j)^{3D} · aᵅ (e^b)^β ℘(z)^{a} τ^φ` with `τ = s − M ζ(z)` (`fibF_eq_off`), and for
fixed `z` the map `s ↦ τ` is a translation of `ℂ^r`, so the reduced polynomial vanishes on a
product of large finite sets.

* **`exists_PsiV_ne_zero`**: `p ≠ 0` and injective reduced exponents ⇒ `∃ x, Ψ(x) ≠ 0`.
-/

open Complex Finset LSG.Weierstrass LSG.W88 LSG.W88.Vec PeriodPair
open LSG.Aux (ellW ellW_eq_off)

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m r D : ℕ}

/-- The variables of the reduced polynomial. -/
abbrev RVarV (d0 d1 m r : ℕ) := Fin d0 ⊕ Fin d1 ⊕ Fin m ⊕ Fin r

/-- Reduced exponent vector. -/
def MonoV.rexp (μ : MonoV d0 d1 m r D) : RVarV d0 d1 m r → ℕ
  | .inl i => μ.α i
  | .inr (.inl i) => μ.β i
  | .inr (.inr (.inl j)) => μ.γ j 1
  | .inr (.inr (.inr i)) => μ.φ i

/-- Evaluation off the lattices. -/
lemma MonoV.eval_off (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (μ : MonoV d0 d1 m r D) (hμ : ∀ j, μ.γ j 2 = 0) (x : TanV d0 d1 m r)
    (hx : ∀ j, x.2.2.1 j ∉ (Ls j).lattice) :
    μ.eval Ls M x = (∏ j, sigma (Ls j) (x.2.2.1 j) ^ (3 * D)) *
      ((∏ i, x.1 i ^ μ.α i) * (∏ i, exp (x.2.1 i) ^ μ.β i) *
        (∏ j, ℘[Ls j] (x.2.2.1 j) ^ μ.γ j 1) *
        ∏ i, (x.2.2.2 i - M.mulVec (zetaV Ls x.2.2.1) i) ^ μ.φ i) := by
  unfold MonoV.eval
  set Φ := ∑ i, μ.φ i
  have hj : ∀ j, ∏ t, ellW (Ls j) t (x.2.2.1 j) ^ μ.γ j t =
      sigma (Ls j) (x.2.2.1 j) ^ (3 * (D - Φ)) * ℘[Ls j] (x.2.2.1 j) ^ μ.γ j 1 := by
    intro j
    rw [Fin.prod_univ_three, hμ j, pow_zero, mul_one, (ellW_eq_off (Ls j) (hx j)).1]
    have hs := μ.hγ j
    simp only [Fin.sum_univ_three, hμ j, add_zero] at hs
    have e0 : ellW (Ls j) 0 (x.2.2.1 j) = sigma (Ls j) (x.2.2.1 j) ^ 3 := rfl
    rw [e0, mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
    congr 2
    omega
  have hF : ∀ i, fibF Ls M i x.2.2.1 x.2.2.2 =
      (∏ j, sigma (Ls j) (x.2.2.1 j) ^ 3) * (x.2.2.2 i - M.mulVec (zetaV Ls x.2.2.1) i) := by
    intro i; rw [fibF_eq_off Ls M i hx]; rfl
  have hΦ : Φ ≤ D := μ.hφ
  have hE : ∏ j, ∏ t, ellW (Ls j) t (x.2.2.1 j) ^ μ.γ j t =
      (∏ j, sigma (Ls j) (x.2.2.1 j) ^ (3 * (D - Φ))) * ∏ j, ℘[Ls j] (x.2.2.1 j) ^ μ.γ j 1 := by
    rw [← prod_mul_distrib]; exact prod_congr rfl fun j _ => hj j
  have hFF : ∏ i, fibF Ls M i x.2.2.1 x.2.2.2 ^ μ.φ i =
      (∏ i, (∏ j, sigma (Ls j) (x.2.2.1 j) ^ 3) ^ μ.φ i) *
        ∏ i, (x.2.2.2 i - M.mulVec (zetaV Ls x.2.2.1) i) ^ μ.φ i := by
    rw [← prod_mul_distrib]; exact prod_congr rfl fun i _ => by rw [hF i, mul_pow]
  have hσ : (∏ j, sigma (Ls j) (x.2.2.1 j) ^ (3 * (D - Φ))) *
      ∏ i, (∏ j, sigma (Ls j) (x.2.2.1 j) ^ 3) ^ μ.φ i =
      ∏ j, sigma (Ls j) (x.2.2.1 j) ^ (3 * D) := by
    rw [prod_pow_eq_pow_sum, ← prod_pow, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_add]
    congr 1
    change 3 * (D - Φ) + 3 * Φ = 3 * D
    omega
  rw [hE, hFF, ← hσ]
  ring

/-- **Nonvanishing of `Ψ` for the class `𝒞`.** -/
theorem exists_PsiV_ne_zero (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (hμ : ∀ l j, (μs l).γ j 2 = 0)
    (hinj : Function.Injective fun l => (μs l).rexp) (p : Fin L → ℤ) (hp : p ≠ 0) :
    ∃ x, PsiV Ls M μs p x ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  let ex : Fin L → (RVarV d0 d1 m r →₀ ℕ) := fun l => Finsupp.equivFunOnFinite.symm (μs l).rexp
  have hex : Function.Injective ex := fun a b h => hinj (by
    have := congrArg Finsupp.equivFunOnFinite h; simpa [ex] using this)
  let Q : MvPolynomial (RVarV d0 d1 m r) ℂ := ∑ l, MvPolynomial.monomial (ex l) (p l : ℂ)
  set N : ℕ := ∑ l, ∑ v, (μs l).rexp v
  have hdeg : ∀ v, MvPolynomial.degreeOf v Q ≤ N := by
    intro v
    refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun l _ => ?_)
    have hm : MvPolynomial.degreeOf v (MvPolynomial.monomial (ex l) (p l : ℂ)) ≤
        (μs l).rexp v := by
      by_cases h0 : (p l : ℂ) = 0
      · rw [h0, map_zero]; simp
      · rw [MvPolynomial.degreeOf_monomial_eq _ _ h0]; simp [ex]
    refine hm.trans ?_
    exact (single_le_sum (f := fun v => (μs l).rexp v) (fun _ _ => Nat.zero_le _)
      (mem_univ v)).trans (single_le_sum (f := fun l => ∑ v, (μs l).rexp v)
        (fun _ _ => Nat.zero_le _) (mem_univ l))
  have hinf : ∀ j, (℘[Ls j] '' ((Ls j).lattice : Set ℂ)ᶜ).Infinite :=
    fun j => infinite_image_weierstrassP (Ls j)
  choose Zs hZs hZcard using fun j => (hinf j).exists_subset_card_eq (N + 1)
  let Sv : RVarV d0 d1 m r → Finset ℂ := fun v => match v with
    | .inl _ => (range (N + 1)).image (fun n : ℕ => (n : ℂ))
    | .inr (.inl _) => (range (N + 1)).image (fun n : ℕ => ((n + 1 : ℕ) : ℂ))
    | .inr (.inr (.inl j)) => Zs j
    | .inr (.inr (.inr _)) => (range (N + 1)).image (fun n : ℕ => (n : ℂ))
  have hcard : ∀ v, MvPolynomial.degreeOf v Q < (Sv v).card := by
    intro v
    have h1 := hdeg v
    rcases v with i | i | j | i
    · simp only [Sv]; rw [card_image_of_injective _ Nat.cast_injective, card_range]; omega
    · simp only [Sv]
      rw [card_image_of_injective _ (fun a b h => by
        have := Nat.cast_injective (R := ℂ) h; omega), card_range]; omega
    · simp only [Sv]; rw [hZcard j]; omega
    · simp only [Sv]; rw [card_image_of_injective _ Nat.cast_injective, card_range]; omega
  have hQ0 : Q = 0 := by
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q Sv hcard fun x hx => ?_
    have hz : ∀ j, ∃ z, z ∉ (Ls j).lattice ∧ ℘[Ls j] z = x (.inr (.inr (.inl j))) := by
      intro j
      obtain ⟨z, hz, hzx⟩ := hZs j (hx (.inr (.inr (.inl j))))
      exact ⟨z, hz, hzx⟩
    choose z hzΛ hzx using hz
    have hb : ∀ i, x (.inr (.inl i)) ≠ 0 := by
      intro i
      obtain ⟨n, -, hn⟩ := mem_image.mp (hx (.inr (.inl i)))
      rw [← hn]; exact_mod_cast Nat.succ_ne_zero n
    let pt : TanV d0 d1 m r := (fun i => x (.inl i), fun i => Complex.log (x (.inr (.inl i))), z,
      fun i => x (.inr (.inr (.inr i))) + M.mulVec (zetaV Ls z) i)
    have hpt := hall pt
    unfold PsiV at hpt
    have hσ : ∏ j, sigma (Ls j) (z j) ^ (3 * D) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (sigma_ne_zero (Ls j) (hzΛ j))
    simp_rw [MonoV.eval_off Ls M _ (hμ _) pt hzΛ] at hpt
    have hpt' : (∏ j, sigma (Ls j) (z j) ^ (3 * D)) * MvPolynomial.eval x Q = 0 := by
      rw [← hpt]
      simp only [Q, map_sum, MvPolynomial.eval_monomial, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [ex, Finsupp.coe_equivFunOnFinite_symm, MonoV.rexp, pt,
        Complex.exp_log (hb _), hzx, add_sub_cancel_right]
      ring_nf
    exact (mul_eq_zero.mp hpt').resolve_left hσ
  apply hp
  funext l
  have hc := congrArg (fun q : MvPolynomial (RVarV d0 d1 m r) ℂ => q.coeff (ex l)) hQ0
  simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hc
  rw [sum_eq_single l (fun b _ hb => by
    simp only [show ¬ ex b = ex l from fun h => hb (hex h), ↓reduceIte]) (by simp)] at hc
  simp only [↓reduceIte] at hc
  simpa using hc

end LSG.AuxV
