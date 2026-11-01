/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LawSize

/-!
# Size of an inverse in a number field (Stage 5, phase 2)

If `z = ι x` with `house x ≤ A` and `d x` integral, `x ≠ 0`, then `z⁻¹` has house
`≤ d (dA)^{deg}` and a denominator `d' = |N_{K/ℚ}(d x)| ≤ (dA)^{deg}` (`sz_inv`).

Proof: `β = d x` is a nonzero algebraic integer; `N(β)` lies in the principal ideal `(β)`
(`Ideal.absNorm_mem`), so `N(β)/β` is integral and `N(β) · x⁻¹ = d · N(β)/β`. For the house,
Liouville's `|N(β)| ≤ |σβ| · house(β)^{deg−1}` (`norm_norm_le_norm_mul_house_pow`) gives
`|σ x⁻¹| = d/|σβ| ≤ d · house(β)^{deg−1}`.
-/

open NumberField Finset

noncomputable section

namespace LSG.AuxV

open LSG.Aux

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

/-- **The size of an inverse.** -/
theorem sz_inv {A : ℝ} {d : ℕ} {z : ℂ} (h : Sz ι A d z) (hz : z ≠ 0) (hA : 1 ≤ A)
    (hd : 1 ≤ d) : ∃ d' : ℕ, 1 ≤ d' ∧ (d' : ℝ) ≤ ((d : ℝ) * A) ^ Module.finrank ℚ K ∧
      Sz ι (d * ((d : ℝ) * A) ^ Module.finrank ℚ K) d' z⁻¹ := by
  obtain ⟨x, rfl, hx, hi⟩ := h
  have hx0 : x ≠ 0 := by rintro rfl; simp at hz
  have hd0 : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set n := Module.finrank ℚ K
  have hn : 1 ≤ n := Module.finrank_pos
  set b : 𝓞 K := ⟨(d : K) * x, hi⟩
  have hb0 : b ≠ 0 := fun h0 => mul_ne_zero hd0 hx0 (congrArg Subtype.val h0)
  set N : ℤ := Algebra.norm ℤ b
  have hN0 : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb0
  have hNq : ((N : ℚ)) = Algebra.norm ℚ ((d : K) * x) := Algebra.coe_norm_int b
  -- `N ∈ (b)`
  have hmem : ((N.natAbs : ℕ) : 𝓞 K) ∈ Ideal.span ({b} : Set (𝓞 K)) := by
    have := Ideal.absNorm_mem (Ideal.span ({b} : Set (𝓞 K)))
    rwa [Ideal.absNorm_span_singleton] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  -- sizes
  set H : ℝ := house ((d : K) * x)
  have hH : H ≤ d * A := by
    simp only [H]; rw [house_nat_mul]; exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
  have hdA : 1 ≤ (d : ℝ) * A := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hH0 : 0 ≤ H := house_nonneg _
  have hNabs : ((N.natAbs : ℕ) : ℝ) = ‖Algebra.norm ℚ ((d : K) * x)‖ := by
    rw [← hNq, Int.norm_cast_rat, Int.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]
  have hN1' : 1 ≤ N.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN0)
  refine ⟨N.natAbs, Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN0), ?_, x⁻¹,
    by simp, ?_, ?_⟩
  · -- `|N| ≤ house^n`
    obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h1 := norm_norm_le_norm_mul_house_pow ((d : K) * x) σ
    have h2 : ‖σ ((d : K) * x)‖ ≤ H := norm_embedding_le_house _ σ
    rw [hNabs]
    calc ‖Algebra.norm ℚ ((d : K) * x)‖ ≤ ‖σ ((d : K) * x)‖ * H ^ (n - 1) := h1
      _ ≤ H * H ^ (n - 1) := by gcongr
      _ = H ^ n := by rw [← pow_succ']; congr 1; omega
      _ ≤ ((d : ℝ) * A) ^ n := by gcongr
  · -- house of the inverse
    refine house_le_of (by positivity) fun σ => ?_
    have h1 := norm_norm_le_norm_mul_house_pow ((d : K) * x) σ
    rw [← hNabs] at h1
    have hσ : σ ((d : K) * x) ≠ 0 := by
      rw [map_ne_zero]; exact mul_ne_zero hd0 hx0
    have hσpos : 0 < ‖σ ((d : K) * x)‖ := norm_pos_iff.mpr hσ
    have hσx0 : σ x ≠ 0 := (map_ne_zero σ).mpr hx0
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hσx : σ x⁻¹ = (d : ℂ) / σ ((d : K) * x) := by
      rw [map_inv₀, map_mul, map_natCast]
      field_simp
    rw [hσx, norm_div, Complex.norm_natCast, div_le_iff₀ hσpos]
    have hHn : H ^ (n - 1) ≤ ((d : ℝ) * A) ^ n := by
      calc H ^ (n - 1) ≤ ((d : ℝ) * A) ^ (n - 1) := by gcongr
        _ ≤ ((d : ℝ) * A) ^ n := pow_le_pow_right₀ hdA (Nat.sub_le n 1)
    calc (d : ℝ) = d * 1 := (mul_one _).symm
      _ ≤ d * (‖σ ((d : K) * x)‖ * H ^ (n - 1)) := by
          have h1' : (1 : ℝ) ≤ N.natAbs := by exact_mod_cast hN1'
          gcongr; exact h1'.trans h1
      _ ≤ d * (‖σ ((d : K) * x)‖ * ((d : ℝ) * A) ^ n) := by gcongr
      _ = d * ((d : ℝ) * A) ^ n * ‖σ ((d : K) * x)‖ := by ring
  · -- `|N| x⁻¹ = d c` is integral
    have hc' : (c : K) * ((d : K) * x) = (N.natAbs : K) := by
      have h := congrArg (algebraMap (𝓞 K) K) hc
      rw [map_mul, map_natCast] at h
      exact h
    have : ((N.natAbs : ℕ) : K) * x⁻¹ = (d : K) * (c : K) := by
      rw [← hc']; field_simp
    rw [this]
    have hdI : IsIntegral ℤ (d : K) := by
      simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (d : ℤ))
    exact hdI.mul c.2

end LSG.AuxV
