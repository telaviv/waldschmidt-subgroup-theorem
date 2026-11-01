/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LemmaUId
import LSG.Weierstrass.Basic

/-!
# `P ∘ exp_G ≢ 0` for distinct `(W, U)`-monomials (Stage 3, D3c)

Monomials whose elliptic part is `(σ³)^{D−a_j} (σ³℘)^{a_j}` (`γ_{j,2} = 0`) are linearly
independent as functions on `T_G`: off the lattices,
`M(x) = Π_j σ_j(z_j)^{3D} · aᵅ (e^b)^β ℘(z)^{γ_{·,1}}`, and a polynomial vanishing on a product of
large finite sets is zero (`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`); the sets are
`{0, …, N}` (`G_a`), `{1, …, N+1} = exp(log …)` (`G_m`) and `N+1` values of `℘_j`
(`infinite_image_weierstrassP`).

* **`exists_Psi_ne_zero`**: `p ≠ 0` and injective exponent data ⇒ `∃ x, Ψ(x) ≠ 0`.
-/

open Complex Finset LSG.Weierstrass LSG.W88 PeriodPair

noncomputable section

namespace LSG.Aux

variable {d0 d1 m D : ℕ}

/-- The variables of the reduced polynomial. -/
abbrev RVar (d0 d1 m : ℕ) := Fin d0 ⊕ Fin d1 ⊕ Fin m

/-- Exponent vector of a `(W, U)`-monomial in the reduced variables. -/
def Mono.rexp (μ : Mono d0 d1 m D) : RVar d0 d1 m → ℕ
  | .inl i => μ.α i
  | .inr (.inl i) => μ.β i
  | .inr (.inr j) => μ.γ j 1

lemma Mono.rexp_injective {μ ν : Mono d0 d1 m D} (hμ : ∀ j, μ.γ j 2 = 0) (hν : ∀ j, ν.γ j 2 = 0)
    (h : μ.rexp = ν.rexp) : μ.α = ν.α ∧ μ.β = ν.β ∧ μ.γ = ν.γ := by
  refine ⟨funext fun i => congrFun h (.inl i), funext fun i => congrFun h (.inr (.inl i)),
    funext fun j => funext fun c => ?_⟩
  have h1 : μ.γ j 1 = ν.γ j 1 := congrFun h (.inr (.inr j))
  have hs := μ.hγ j
  have ht := ν.hγ j
  simp only [Fin.sum_univ_three] at hs ht
  fin_cases c
  · simp only [Fin.zero_eta]; have := hμ j; have := hν j; omega
  · exact h1
  · simp only [Fin.reduceFinMk]; rw [hμ j, hν j]

/-- The evaluation of a monomial off the lattices. -/
lemma Mono.eval_off (Ls : Fin m → PeriodPair) (μ : Mono d0 d1 m D) (hμ : ∀ j, μ.γ j 2 = 0)
    (x : Tan d0 d1 m) (hx : ∀ j, x.2.2 j ∉ (Ls j).lattice) :
    μ.eval Ls x = (∏ j, sigma (Ls j) (x.2.2 j) ^ (3 * D)) *
      ((∏ i, x.1 i ^ μ.α i) * (∏ i, exp (x.2.1 i) ^ μ.β i) *
        ∏ j, ℘[Ls j] (x.2.2 j) ^ μ.γ j 1) := by
  unfold Mono.eval
  have hj : ∀ j, ∏ t, ellW (Ls j) t (x.2.2 j) ^ μ.γ j t =
      sigma (Ls j) (x.2.2 j) ^ (3 * D) * ℘[Ls j] (x.2.2 j) ^ μ.γ j 1 := by
    intro j
    rw [Fin.prod_univ_three, hμ j, pow_zero, mul_one, (ellW_eq_off (Ls j) (hx j)).1]
    have hs := μ.hγ j
    simp only [Fin.sum_univ_three, hμ j, add_zero] at hs
    have e0 : ellW (Ls j) 0 (x.2.2 j) = sigma (Ls j) (x.2.2 j) ^ 3 := rfl
    rw [e0, mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
    congr 2
    omega
  simp_rw [hj, prod_mul_distrib]
  ring

/-- **Nonvanishing of `Ψ`.** -/
theorem exists_Psi_ne_zero (Ls : Fin m → PeriodPair) {L : ℕ} (μs : Fin L → Mono d0 d1 m D)
    (hμ : ∀ l j, (μs l).γ j 2 = 0) (hinj : Function.Injective fun l => (μs l).rexp)
    (p : Fin L → ℤ) (hp : p ≠ 0) : ∃ x, Psi Ls μs p x ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  -- the reduced polynomial
  let ex : Fin L → (RVar d0 d1 m →₀ ℕ) := fun l => Finsupp.equivFunOnFinite.symm (μs l).rexp
  have hex : Function.Injective ex := fun a b h => hinj (by
    have := congrArg Finsupp.equivFunOnFinite h; simpa [ex] using this)
  let Q : MvPolynomial (RVar d0 d1 m) ℂ := ∑ l, MvPolynomial.monomial (ex l) (p l : ℂ)
  -- degree bound
  set N : ℕ := ∑ l, ∑ v, (μs l).rexp v
  have hdeg : ∀ v, MvPolynomial.degreeOf v Q ≤ N := by
    intro v
    refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun l _ => ?_)
    have hm : MvPolynomial.degreeOf v (MvPolynomial.monomial (ex l) (p l : ℂ)) ≤ (μs l).rexp v := by
      by_cases h0 : (p l : ℂ) = 0
      · rw [h0, map_zero]; simp
      · rw [MvPolynomial.degreeOf_monomial_eq _ _ h0]; simp [ex]
    refine hm.trans ?_
    exact (single_le_sum (f := fun v => (μs l).rexp v) (fun _ _ => Nat.zero_le _)
      (mem_univ v)).trans (single_le_sum (f := fun l => ∑ v, (μs l).rexp v)
        (fun _ _ => Nat.zero_le _) (mem_univ l))
  -- the evaluation sets
  have hinf : ∀ j, (℘[Ls j] '' ((Ls j).lattice : Set ℂ)ᶜ).Infinite :=
    fun j => infinite_image_weierstrassP (Ls j)
  choose Zs hZs hZcard using fun j => (hinf j).exists_subset_card_eq (N + 1)
  let Sv : RVar d0 d1 m → Finset ℂ := fun v => match v with
    | .inl _ => (range (N + 1)).image (fun n : ℕ => (n : ℂ))
    | .inr (.inl _) => (range (N + 1)).image (fun n : ℕ => ((n + 1 : ℕ) : ℂ))
    | .inr (.inr j) => Zs j
  have hcard : ∀ v, MvPolynomial.degreeOf v Q < (Sv v).card := by
    intro v
    have h1 := hdeg v
    rcases v with i | i | j
    · simp only [Sv]; rw [card_image_of_injective _ Nat.cast_injective, card_range]; omega
    · simp only [Sv]
      rw [card_image_of_injective _ (fun a b h => by
        have := Nat.cast_injective (R := ℂ) h; omega), card_range]; omega
    · simp only [Sv]; rw [hZcard j]; omega
  have hQ0 : Q = 0 := by
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q Sv hcard fun x hx => ?_
    -- a point of `T_G` above `x`
    have hz : ∀ j, ∃ z, z ∉ (Ls j).lattice ∧ ℘[Ls j] z = x (.inr (.inr j)) := by
      intro j
      have := hZs j (hx (.inr (.inr j)))
      obtain ⟨z, hz, hzx⟩ := this
      exact ⟨z, hz, hzx⟩
    choose z hzΛ hzx using hz
    have hb : ∀ i, x (.inr (.inl i)) ≠ 0 := by
      intro i
      obtain ⟨n, -, hn⟩ := mem_image.mp (hx (.inr (.inl i)))
      rw [← hn]; exact_mod_cast Nat.succ_ne_zero n
    let pt : Tan d0 d1 m := (fun i => x (.inl i), fun i => Complex.log (x (.inr (.inl i))), z)
    have hpt := hall pt
    unfold Psi at hpt
    have hσ : ∏ j, sigma (Ls j) (z j) ^ (3 * D) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (sigma_ne_zero (Ls j) (hzΛ j))
    simp_rw [Mono.eval_off Ls _ (hμ _) pt hzΛ] at hpt
    have hpt' : (∏ j, sigma (Ls j) (z j) ^ (3 * D)) * MvPolynomial.eval x Q = 0 := by
      rw [← hpt]
      simp only [Q, map_sum, MvPolynomial.eval_monomial, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [ex, Finsupp.coe_equivFunOnFinite_symm, Mono.rexp, pt,
        Complex.exp_log (hb _), hzx]
      ring_nf
    exact (mul_eq_zero.mp hpt').resolve_left hσ
  -- coefficients
  apply hp
  funext l
  have hc := congrArg (fun q : MvPolynomial (RVar d0 d1 m) ℂ => q.coeff (ex l)) hQ0
  simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at hc
  rw [sum_eq_single l (fun b _ hb => if_neg (fun h => hb (hex h))) (by simp)] at hc
  simp only [↓reduceIte, Int.cast_eq_zero] at hc
  simpa using hc

end LSG.Aux
