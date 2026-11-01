/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.SchneiderLang.Deriv
import LSG.SchneiderLang.Params

/-!
# Schneider–Lang: auxiliary objects

* `mon i₁ i₂ a b = X_{i₁}^a X_{i₂}^b` and the house bound `house_entry_le` for the values of
  `Dop^k (mon …)` (the entries of the Siegel system and the terms of `γ`).
* `expo a b`, the exponent of `X₀^a X₁^b` in two variables, and `poly2_ne_zero`: a polynomial
  `∑ c_{ab} X₀^a X₁^b` with some `c_{ab} ≠ 0` is nonzero.
* `norm_G_le`: the growth bound for `G = ∑ c_{ab} (d₀ g₁)^a (d₀ g₂)^b h^{2L-a-b}`.
-/

open MvPolynomial Finset NumberField

namespace LSG.SL

variable {K : Type*} [Field K] [NumberField K] {N : ℕ}

/-- `X_{i₁}^a X_{i₂}^b`. -/
noncomputable def mon (i₁ i₂ : Fin N) (a b : ℕ) : MvPolynomial (Fin N) (𝓞 K) :=
  X i₁ ^ a * X i₂ ^ b

omit [NumberField K] in
theorem totalDegree_mon_le (i₁ i₂ : Fin N) (a b : ℕ) :
    (mon (K := K) i₁ i₂ a b).totalDegree ≤ a + b := by
  unfold mon
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X_pow, totalDegree_X_pow]

theorem hsum_mon_le (i₁ i₂ : Fin N) (a b : ℕ) : hsum (mon (K := K) i₁ i₂ a b) ≤ 1 := by
  unfold mon
  refine (hsum_mul_le _ _).trans ?_
  have h1 := hsum_X_pow_le (K := K) i₁ a
  have h2 := hsum_X_pow_le (K := K) i₂ b
  have h3 := hsum_nonneg (X i₂ ^ b : MvPolynomial (Fin N) (𝓞 K))
  nlinarith

theorem Abd_mono {β Y : ℝ} (hβ : 1 ≤ β) (hY : 1 ≤ Y) (δ L : ℕ) (hL : 1 ≤ L) {k k' : ℕ}
    (hk : k ≤ k') : Abd β Y δ L k ≤ Abd β Y δ L k' := by
  unfold Abd
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hkk : (k : ℝ) ≤ k' := by exact_mod_cast hk
  have hδ : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
  have h1 : 1 ≤ β * (2 * (L : ℝ) + k * δ) := by
    have : (0 : ℝ) ≤ k * δ := by positivity
    nlinarith
  have h2 : β * (2 * (L : ℝ) + k * δ) ≤ β * (2 * L + k' * δ) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  calc (β * (2 * (L : ℝ) + k * δ)) ^ k * Y ^ (2 * L + k * δ)
      ≤ (β * (2 * (L : ℝ) + k' * δ)) ^ k * Y ^ (2 * L + k' * δ) :=
        mul_le_mul (pow_le_pow_left₀ (by linarith) h2 k)
          (pow_le_pow_right₀ hY (by have := Nat.mul_le_mul_right δ hk; omega))
          (by positivity) (pow_nonneg (by linarith [h1.trans h2]) k)
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (h1.trans h2) hk) (by positivity)

/-- House of the values of `Dop^k (X_{i₁}^a X_{i₂}^b)`. -/
theorem house_entry_le (Qh : Fin N → MvPolynomial (Fin N) (𝓞 K)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i, hsum (Qh i) ≤ B) {δ : ℕ} (hδ : ∀ i, (Qh i).totalDegree ≤ δ) (i₁ i₂ : Fin N)
    {L a b : ℕ} (ha : a ≤ L) (hb : b ≤ L) (k : ℕ) (y : Fin N → 𝓞 K) {Y : ℝ} (hY1 : 1 ≤ Y)
    (hY : ∀ i, house ((y i : 𝓞 K) : K) ≤ Y) :
    house ((eval y ((Dop Qh ^ k) (mon i₁ i₂ a b)) : 𝓞 K) : K) ≤ Abd (N * B) Y δ L k := by
  have hD : (mon (K := K) i₁ i₂ a b).totalDegree ≤ 2 * L :=
    (totalDegree_mon_le i₁ i₂ a b).trans (by omega)
  refine (house_eval_Dop_pow_le Qh hB0 hB hδ _ hD k y hY1 hY).trans ?_
  unfold Abd
  have h1 := hsum_mon_le (K := K) i₁ i₂ a b
  have h0 : (0 : ℝ) ≤ (N * B * (((2 * L : ℕ) : ℝ) + k * δ)) ^ k := by positivity
  calc (N * B * (((2 * L : ℕ) : ℝ) + k * δ)) ^ k * hsum (mon (K := K) i₁ i₂ a b) *
        Y ^ (2 * L + k * δ)
      ≤ (N * B * (((2 * L : ℕ) : ℝ) + k * δ)) ^ k * 1 * Y ^ (2 * L + k * δ) := by gcongr
    _ = _ := by push_cast; ring

/-- The exponent of `X₀^a X₁^b`. -/
noncomputable def expo (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

theorem expo_inj {a b a' b' : ℕ} (h : expo a b = expo a' b') : a = a' ∧ b = b' := by
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  simp [expo] at h0 h1
  exact ⟨h0, h1⟩

omit [NumberField K] in
theorem eval₂_monomial_expo (σ : K →+* ℂ) (v : Fin 2 → ℂ) (c : K) (a b : ℕ) :
    eval₂ σ v (monomial (expo a b) c) = σ c * v 0 ^ a * v 1 ^ b := by
  rw [eval₂_monomial, expo, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp [Finsupp.prod_single_index]
  ring

omit [NumberField K] in
theorem poly2_ne_zero {L : ℕ} (coef : Fin L × Fin L → K) (hcoef : coef ≠ 0) :
    (∑ ab : Fin L × Fin L, monomial (expo ab.1 ab.2) (coef ab)) ≠ 0 := by
  classical
  obtain ⟨ab₀, hab₀⟩ := Function.ne_iff.mp hcoef
  intro h
  have h2 := congrArg (fun p : MvPolynomial (Fin 2) K => p.coeff (expo ab₀.1 ab₀.2)) h
  simp only [coeff_sum] at h2
  rw [show (0 : MvPolynomial (Fin 2) K).coeff (expo ab₀.1 ab₀.2) = 0 from by simp] at h2
  simp only [coeff_monomial] at h2
  rw [Finset.sum_eq_single ab₀] at h2
  · simp at h2; exact hab₀ h2
  · intro ab _ hne
    refine ite_eq_right_iff.mpr fun he => ?_
    obtain ⟨h1, h2⟩ := expo_inj he
    exact absurd (Prod.ext (Fin.ext h1) (Fin.ext h2)) hne
  · intro h; exact absurd (mem_univ _) h

/-- Growth of `G`. -/
theorem norm_G_le {L : ℕ} (c : Fin L × Fin L → ℂ) {H : ℝ} (hc : ∀ ab, ‖c ab‖ ≤ H)
    (u v t : ℂ) {E : ℝ} (hE : 1 ≤ E) (d₀ : ℕ) (hd₀ : 1 ≤ d₀) (hu : ‖u‖ ≤ E) (hv : ‖v‖ ≤ E)
    (ht : ‖t‖ ≤ E) :
    ‖∑ ab : Fin L × Fin L, c ab * (((d₀ : ℂ) * u) ^ (ab.1 : ℕ) * ((d₀ : ℂ) * v) ^ (ab.2 : ℕ) *
        t ^ (2 * L - ab.1 - ab.2))‖ ≤ ((L * L : ℕ) : ℝ) * H * (d₀ : ℝ) ^ (2 * L) * E ^ (2 * L) := by
  have hd : (1 : ℝ) ≤ d₀ := by exact_mod_cast hd₀
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  have hH : 0 ≤ H := (norm_nonneg _).trans (hc (⟨0, hL⟩, ⟨0, hL⟩))
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ab : Fin L × Fin L, ‖c ab * (((d₀ : ℂ) * u) ^ (ab.1 : ℕ) *
      ((d₀ : ℂ) * v) ^ (ab.2 : ℕ) * t ^ (2 * L - ab.1 - ab.2))‖ ≤
        H * ((d₀ : ℝ) ^ (2 * L) * E ^ (2 * L)) := by
    intro ab
    have hab : (ab.1 : ℕ) + ab.2 ≤ 2 * L := by have := ab.1.isLt; have := ab.2.isLt; omega
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_mul, norm_mul,
      Complex.norm_natCast]
    refine mul_le_mul (hc ab) ?_ (by positivity) hH
    calc ((d₀ : ℝ) * ‖u‖) ^ (ab.1 : ℕ) * ((d₀ : ℝ) * ‖v‖) ^ (ab.2 : ℕ) *
          ‖t‖ ^ (2 * L - ab.1 - ab.2)
        ≤ ((d₀ : ℝ) * E) ^ (ab.1 : ℕ) * ((d₀ : ℝ) * E) ^ (ab.2 : ℕ) *
          E ^ (2 * L - ab.1 - ab.2) := by gcongr
      _ = (d₀ : ℝ) ^ ((ab.1 : ℕ) + ab.2) * E ^ ((ab.1 : ℕ) + ab.2 + (2 * L - ab.1 - ab.2)) := by
          rw [mul_pow, mul_pow, pow_add, pow_add, pow_add]; ring
      _ ≤ (d₀ : ℝ) ^ (2 * L) * E ^ (2 * L) := by
          rw [show (ab.1 : ℕ) + ab.2 + (2 * L - ab.1 - ab.2) = 2 * L by omega]
          gcongr
  refine (sum_le_sum fun ab _ => hterm ab).trans (le_of_eq ?_)
  rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  ring

end LSG.SL
