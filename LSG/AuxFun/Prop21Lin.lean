/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Prop21

/-!
# W83 Prop. 2.1 for arbitrary `ℂ`-linearly independent periods (Tier 1′)

`LSG.Aux.prop21B` is stated in adapted coordinates (periods `e_1, …, e_κ`). Here the periods are
any `ℂ`-linearly independent `ω_1, …, ω_κ ∈ ℂⁿ`: extend them to a basis, let `A` be the linear
isomorphism with `A e_i = ω_i`, and apply `prop21B` to `ψ_λ ∘ A`. Polydiscs move by `‖A‖` and
`‖A⁻¹‖`, which only changes the constants; the multiplier constant becomes `b ‖A‖²`. As in W83's
statement the hypothesis is `U ≥ r² log(R/r)` (it absorbs the factor `‖A⁻¹‖` in `r`).

* `LSG.Aux.exists_equiv_extend`: the isomorphism `A`.
* `LSG.Aux.prop21Lin`: the theorem.
-/

open Complex Finset Module

namespace LSG.Aux

/-- Extend `ℂ`-independent `ω_1, …, ω_κ` to a linear automorphism `A` of `ℂⁿ` with
`A k = Σ_i k_i ω_i` for every `k` supported in the first `κ` coordinates. -/
theorem exists_equiv_extend {n κ : ℕ} (hκ : κ ≤ n) (ω : Fin κ → (Fin n → ℂ))
    (hω : LinearIndependent ℂ ω) :
    ∃ A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ), ∀ k : Fin n → ℂ, (∀ i : Fin n, κ ≤ i.val → k i = 0) →
      A k = ∑ j : Fin κ, k ⟨j, lt_of_lt_of_le j.isLt hκ⟩ • ω j := by
  classical
  set W := Submodule.span ℂ (Set.range ω)
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  have hfW : finrank ℂ W = κ := by rw [finrank_span_eq_card hω, Fintype.card_fin]
  have hsum := Submodule.finrank_add_eq_of_isCompl hW'
  rw [hfW, finrank_fin_fun] at hsum
  have hfW' : finrank ℂ W' = n - κ := by omega
  let v : Basis (Fin (n - κ)) ℂ W' := Module.finBasisOfFinrankEq ℂ W' hfW'
  let f : Fin κ ⊕ Fin (n - κ) → (Fin n → ℂ) := Sum.elim ω (fun j => (v j : Fin n → ℂ))
  have hv' : LinearIndependent ℂ (fun j => (v j : Fin n → ℂ)) :=
    v.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hspan' : Submodule.span ℂ (Set.range fun j => (v j : Fin n → ℂ)) = W' := by
    have : Set.range (fun j => (v j : Fin n → ℂ)) = W'.subtype '' Set.range v := by
      ext x; simp
    rw [this, Submodule.span_image, v.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hf : LinearIndependent ℂ f := hω.sum_type hv' (by rw [hspan']; exact hW'.disjoint)
  have hcard : Fintype.card (Fin κ ⊕ Fin (n - κ)) = finrank ℂ (Fin n → ℂ) := by
    simp only [Fintype.card_sum, Fintype.card_fin, finrank_fin_fun]; omega
  let b0 := basisOfLinearIndependentOfCardEqFinrank' f hf hcard
  let e : Fin κ ⊕ Fin (n - κ) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  let b := b0.reindex e
  refine ⟨b.equivFun.symm.toContinuousLinearEquiv, fun k hk => ?_⟩
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', Basis.equivFun_symm_apply]
  rw [← e.sum_comp, Fintype.sum_sum_type]
  have h1 : ∀ j : Fin κ, e (Sum.inl j) = ⟨j, lt_of_lt_of_le j.isLt hκ⟩ := fun j => by
    ext; simp [e]
  have h2 : ∀ j : Fin (n - κ), κ ≤ (e (Sum.inr j)).val := fun j => by simp [e]
  have hb : ∀ c, b (e c) = f c := fun c => by simp [b, b0]
  have hz : ∑ j : Fin (n - κ), k (e (Sum.inr j)) • b (e (Sum.inr j)) = 0 :=
    sum_eq_zero fun j _ => by rw [hk _ (h2 j), zero_smul]
  rw [hz, add_zero]
  refine sum_congr rfl fun j _ => ?_
  rw [hb, h1]; rfl

/-- **W83 Prop. 2.1 for `ℂ`-linearly independent periods `ω_1, …, ω_κ`.** -/
theorem prop21Lin (n κ : ℕ) (hκ : κ ≤ n) (a : ℝ) (ha : 0 ≤ a) (ω : Fin κ → (Fin n → ℂ))
    (hω : LinearIndependent ℂ ω) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L : ℕ) (b Δ U R r : ℝ) (ψ : Fin L → (Fin n → ℂ) → ℂ),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → r ^ 2 * Real.log (R / r) ≤ U →
      0 ≤ b → b * r ^ 2 ≤ a * U →
      (∀ l, Differentiable ℂ (ψ l)) → (∀ z, ‖z‖ ≤ R → ∑ l, ‖ψ l z‖ ≤ Real.exp U) →
      (∀ k : Fin κ → ℤ, ∀ z : Fin n → ℂ, ∃ m : ℂ,
        ‖m‖ ≤ Real.exp (b * (‖z‖ + ‖∑ i, (k i : ℂ) • ω i‖) ^ 2) ∧
        ∀ l, ψ l (z + ∑ i, (k i : ℂ) • ω i) = m * ψ l z) →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ Real.exp (-U) := by
  obtain ⟨A, hA⟩ := exists_equiv_extend hκ ω hω
  set α : ℝ := max ‖(A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖ 1 with hα
  set β : ℝ := max ‖(A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖ 1 with hβ
  have hα1 : 1 ≤ α := le_max_right _ _
  have hβ1 : 1 ≤ β := le_max_right _ _
  have hAz : ∀ z, ‖A z‖ ≤ α * ‖z‖ := fun z =>
    ((A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  have hAz' : ∀ z, ‖A.symm z‖ ≤ β * ‖z‖ := fun z =>
    ((A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := prop21B n κ hκ (a * α ^ 2 * β ^ 2) (by positivity)
  set γ : ℝ := α * β with hγ
  have hγ1 : 1 ≤ γ := one_le_mul_of_one_le_of_one_le hα1 hβ1
  refine ⟨max c₁ 1 * γ ^ 2, c₂ * 2 ^ n, by positivity, by positivity, ?_⟩
  intro L b Δ U R r ψ hL hΔ hΔU hRr hr hU hb0 hbU hψd hψR hQP hc
  have hm1 : 1 ≤ max c₁ 1 := le_max_right _ _
  have hγ2 : γ ≤ γ ^ 2 := by nlinarith
  have hr1 : 1 ≤ r := le_trans (one_le_mul_of_one_le_of_one_le hm1 (by nlinarith)) hr
  have hr0 : 0 < r := by linarith
  have hRr0 : 0 < R / r := lt_of_lt_of_le (by positivity) hRr
  have hR0 : 0 < R := (div_pos_iff_of_pos_right hr0).mp hRr0
  have hrβ : β ≤ r := by
    have : β ≤ γ ^ 2 := by nlinarith
    exact this.trans (le_trans (le_mul_of_one_le_left (by positivity) hm1) hr)
  have hγR : γ ^ 2 ≤ R / r := le_trans (le_mul_of_one_le_left (by positivity) hm1) hRr
  -- the new parameters
  set r' : ℝ := β * r
  set R' : ℝ := R / α
  have hratio : R' / r' = (R / r) / γ := by simp only [R', r', hγ]; field_simp
  have hlog : Real.log (R / r) / 2 ≤ Real.log (R' / r') := by
    rw [hratio, Real.log_div hRr0.ne' (by positivity)]
    have h1 : Real.log γ ≤ Real.log (R / r) / 2 := by
      have := Real.log_le_log (by positivity) hγR
      rw [Real.log_pow] at this; push_cast at this; linarith
    linarith
  have hlog' : Real.log (R' / r') ≤ Real.log (R / r) := by
    rw [hratio]
    exact Real.log_le_log (by positivity) (div_le_self hRr0.le hγ1)
  have hlog0 : 0 ≤ Real.log (R / r) := Real.log_nonneg (by nlinarith)
  obtain ⟨p, hp0, hpΔ, hpz⟩ := h L (b * α ^ 2) Δ U R' r' (fun l z => ψ l (A z)) hL hΔ hΔU
    (by rw [hratio, le_div_iff₀ (by positivity)]
        calc c₁ * γ ≤ max c₁ 1 * γ ^ 2 := by
              gcongr; exact le_max_left _ _
          _ ≤ R / r := hRr)
    (by calc c₁ ≤ max c₁ 1 := le_max_left _ _
          _ ≤ max c₁ 1 * γ ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
          _ ≤ r := hr
          _ ≤ r' := le_mul_of_one_le_left hr0.le hβ1)
    (by calc r' * Real.log (R' / r') ≤ r' * Real.log (R / r) := by gcongr
          _ = β * (r * Real.log (R / r)) := by ring
          _ ≤ r * (r * Real.log (R / r)) := by gcongr
          _ = r ^ 2 * Real.log (R / r) := by ring
          _ ≤ U := hU)
    (by positivity)
    (by calc b * α ^ 2 * r' ^ 2 = α ^ 2 * β ^ 2 * (b * r ^ 2) := by ring
          _ ≤ α ^ 2 * β ^ 2 * (a * U) := by gcongr
          _ = a * α ^ 2 * β ^ 2 * U := by ring)
    (fun l => (hψd l).comp A.differentiable)
    (fun z hz => hψR _ (by
      calc ‖A z‖ ≤ α * ‖z‖ := hAz z
        _ ≤ α * R' := by gcongr
        _ = R := by simp only [R']; field_simp))
    (by
      intro k hk z
      set kk : Fin κ → ℤ := fun j => k ⟨j, lt_of_lt_of_le j.isLt hκ⟩
      have hAk : A (fun i => (k i : ℂ)) = ∑ j, (kk j : ℂ) • ω j :=
        hA _ fun i hi => by simp [hk i hi]
      obtain ⟨m, hm, hmψ⟩ := hQP kk (A z)
      refine ⟨m, hm.trans (Real.exp_le_exp.mpr ?_), fun l => ?_⟩
      · rw [← hAk]
        have h1 : ‖A z‖ + ‖A (fun i => (k i : ℂ))‖ ≤ α * (‖z‖ + ‖(fun i => (k i : ℂ))‖) := by
          rw [mul_add]; exact add_le_add (hAz _) (hAz _)
        have h0 : 0 ≤ ‖A z‖ + ‖A (fun i => (k i : ℂ))‖ := by positivity
        calc b * (‖A z‖ + ‖A (fun i => (k i : ℂ))‖) ^ 2
            ≤ b * (α * (‖z‖ + ‖(fun i => (k i : ℂ))‖)) ^ 2 := by gcongr
          _ = b * α ^ 2 * (‖z‖ + ‖(fun i => (k i : ℂ))‖) ^ 2 := by ring
      · simp only [map_add, hAk]
        exact hmψ l)
    (by
      have hrr : r ^ κ ≤ r' ^ κ := pow_le_pow_left₀ hr0.le (le_mul_of_one_le_left hr0.le hβ1) κ
      have hll : (Real.log (R / r) / 2) ^ n ≤ Real.log (R' / r') ^ n :=
        pow_le_pow_left₀ (by positivity) hlog n
      have hΔ0 : (0 : ℝ) ≤ L * Δ := by positivity
      calc c₂ * U ^ (n + 1) = c₂ * 2 ^ n * U ^ (n + 1) / 2 ^ n := by field_simp
        _ ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n / 2 ^ n := by gcongr
        _ = L * Δ * r ^ κ * (Real.log (R / r) / 2) ^ n := by rw [div_pow]; ring
        _ ≤ L * Δ * r' ^ κ * Real.log (R' / r') ^ n := by gcongr)
  refine ⟨p, hp0, hpΔ, fun z hz => ?_⟩
  have := hpz (A.symm z) ((hAz' z).trans (mul_le_mul_of_nonneg_left hz (by positivity)))
  simpa using this

end LSG.Aux
