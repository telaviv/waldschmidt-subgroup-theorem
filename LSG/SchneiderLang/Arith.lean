/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Arithmetic tools: Siegel's lemma and Liouville's inequality

* `siegel`: Mathlib's Siegel lemma over `𝓞 K` (`house.exists_ne_zero_int_vec_house_le`) in the
  simplified form `house ξ ≤ c (1 + c q A)` when there are at least twice as many unknowns as
  equations.
* `one_le_norm_mul_house_pow`: Liouville's inequality `1 ≤ |σ β| house(β)^{d-1}` for a nonzero
  algebraic integer `β` (copied from `StrongSix/Arith/Liouville.lean`, Apache 2.0).
-/

open NumberField Finset
open private c₁ c₂ c₂_nonneg from Mathlib.NumberTheory.NumberField.House

namespace LSG.SL

variable {K : Type*} [Field K] [NumberField K]

theorem one_le_norm_algebraNorm_of_integral {β : K} (hβ : IsIntegral ℤ β) (hβ0 : β ≠ 0) :
    1 ≤ ‖Algebra.norm ℚ β‖ := by
  let b : 𝓞 K := ⟨β, hβ⟩
  have hb0 : b ≠ 0 := fun h => hβ0 (congrArg Subtype.val h)
  have hn : Algebra.norm ℤ b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb0
  have hcast : ((Algebra.norm ℤ b : ℤ) : ℚ) = Algebra.norm ℚ β := Algebra.coe_norm_int b
  rw [← hcast, Int.norm_cast_rat, Int.norm_eq_abs]
  exact_mod_cast Int.one_le_abs hn

/-- **Liouville's inequality.** -/
theorem one_le_norm_mul_house_pow (β : 𝓞 K) (hβ0 : β ≠ 0) (σ : K →+* ℂ) :
    1 ≤ ‖σ (β : K)‖ * house (β : K) ^ (Module.finrank ℚ K - 1) := by
  have h0 : (β : K) ≠ 0 := fun h => hβ0 (RingOfIntegers.ext (by simpa using h))
  exact (one_le_norm_algebraNorm_of_integral β.2 h0).trans (norm_norm_le_norm_mul_house_pow _ σ)

/-- Real-power bound used to simplify Siegel's estimate. -/
theorem rpow_le_one_add {b t : ℝ} (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : b ^ t ≤ 1 + b := by
  rcases le_total b 1 with h | h
  · exact (Real.rpow_le_one hb h ht0).trans (le_add_of_nonneg_right hb)
  · calc b ^ t ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h ht1
      _ = b := Real.rpow_one b
      _ ≤ 1 + b := le_add_of_nonneg_left zero_le_one

variable (K) in
/-- **Siegel's lemma**, simplified. -/
theorem siegel : ∃ c : ℝ, 0 ≤ c ∧ ∀ {α β : Type} [Fintype α] [Fintype β]
    (a : Matrix α β (𝓞 K)), a ≠ 0 → 0 < Fintype.card α →
      2 * Fintype.card α ≤ Fintype.card β → ∀ A : ℝ, 0 ≤ A →
        (∀ k l, house (a k l : K) ≤ A) →
          ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a.mulVec ξ = 0 ∧
            ∀ l, house (ξ l : K) ≤ c * (1 + c * Fintype.card β * A) := by
  classical
  have hc : 0 ≤ c₁ K := by unfold c₁; exact mul_nonneg (Nat.cast_nonneg _) (c₂_nonneg K)
  refine ⟨c₁ K, hc, ?_⟩
  intro α β _ _ a ha hp hpq A hA habs
  have hlt : Fintype.card α < Fintype.card β := by omega
  obtain ⟨ξ, hξ0, hξ, hb⟩ := house.exists_ne_zero_int_vec_house_le K a ha hp hlt rfl
    habs rfl
  refine ⟨ξ, hξ0, hξ, fun l => (hb l).trans ?_⟩
  have hqp : (0 : ℝ) < (Fintype.card β : ℝ) - Fintype.card α := by
    have : (Fintype.card α : ℝ) < Fintype.card β := by exact_mod_cast hlt
    linarith
  have ht0 : (0 : ℝ) ≤ (Fintype.card α : ℝ) / ((Fintype.card β : ℝ) - Fintype.card α) := by
    positivity
  have ht1 : (Fintype.card α : ℝ) / ((Fintype.card β : ℝ) - Fintype.card α) ≤ 1 := by
    rw [div_le_one hqp]
    have : (2 * Fintype.card α : ℝ) ≤ Fintype.card β := by exact_mod_cast hpq
    linarith
  exact mul_le_mul_of_nonneg_left (rpow_le_one_add (by positivity) ht0 ht1) hc

end LSG.SL
