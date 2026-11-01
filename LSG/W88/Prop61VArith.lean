/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Prop61Arith

/-!
# Parameter bookkeeping for W88 Prop. 6.1 for the class `𝒞` (Stage 5, phase 2)

**`growth61V`**: the growth condition of `prop21_GV_deg`, with the extra terms
`D log(1 + R) + D log K` of the fibre forms, `R = ν³ S`, `U = ν⁶ Δ`.
-/

noncomputable section

namespace LSG.W88

/-- The growth condition of Prop. 2.1 in Prop. 6.1 for the class `𝒞`. -/
lemma growth61V {m : ℕ} {Δ ν S lS cW lL A₀ A₁ D lR lK : ℝ} (hΔ : 0 ≤ Δ) (hν : 3 ≤ ν)
    (hS : 1 ≤ S) (hlS : 1 ≤ lS) (h2lS : 2 * lS ≤ S ^ 2) (hcW : 0 ≤ cW) (hνcW : 16 * m * cW ≤ ν)
    (hlK0 : 0 ≤ lK) (hlK : lK ≤ ν) (hlL : lL ≤ Δ)
    (hA₀ : A₀ ≤ Δ / (ν * lS)) (hA₁ : A₁ ≤ Δ / (ν * S))
    (hD : D ≤ Δ / (ν * S ^ 2)) (hlR : lR ≤ 2 * lS) (hlR0 : 0 ≤ lR) :
    lL + (A₀ + D) * lR + D * lK + A₁ * (ν ^ 3 * S) + m * D * cW * (1 + ν ^ 3 * S) ^ 2 ≤
      ν ^ 6 * Δ := by
  have hν0 : 0 < ν := by linarith
  have hS0 : 0 < S := by linarith
  have hlS0 : 0 < lS := by linarith
  have e1 : A₀ * lR ≤ 2 * Δ / ν := by
    calc A₀ * lR ≤ Δ / (ν * lS) * (2 * lS) := mul_le_mul hA₀ hlR hlR0 (by positivity)
      _ = 2 * Δ / ν := by field_simp
  have e2 : A₁ * (ν ^ 3 * S) ≤ ν ^ 2 * Δ := by
    calc A₁ * (ν ^ 3 * S) ≤ Δ / (ν * S) * (ν ^ 3 * S) :=
          mul_le_mul_of_nonneg_right hA₁ (by positivity)
      _ = ν ^ 2 * Δ := by field_simp
  have hR1 : 1 ≤ ν ^ 3 * S := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hS
  have e3 : (m : ℝ) * D * cW * (1 + ν ^ 3 * S) ^ 2 ≤ 4 * m * cW * ν ^ 5 * Δ := by
    have h1 : (1 + ν ^ 3 * S) ^ 2 ≤ 4 * (ν ^ 3 * S) ^ 2 := by nlinarith
    calc (m : ℝ) * D * cW * (1 + ν ^ 3 * S) ^ 2 ≤
          m * (Δ / (ν * S ^ 2)) * cW * (4 * (ν ^ 3 * S) ^ 2) := by gcongr
      _ = 4 * m * cW * ν ^ 5 * Δ := by field_simp
  have e4 : 4 * m * cW * ν ^ 5 * Δ ≤ ν ^ 6 * Δ / 4 := by
    have : 4 * (m : ℝ) * cW * ν ^ 5 ≤ ν ^ 6 / 4 := by
      have h5 : 0 ≤ ν ^ 5 := by positivity
      calc 4 * (m : ℝ) * cW * ν ^ 5 = (16 * m * cW) * ν ^ 5 / 4 := by ring
        _ ≤ ν * ν ^ 5 / 4 := by gcongr
        _ = ν ^ 6 / 4 := by ring
    calc 4 * m * cW * ν ^ 5 * Δ ≤ ν ^ 6 / 4 * Δ := mul_le_mul_of_nonneg_right this hΔ
      _ = ν ^ 6 * Δ / 4 := by ring
  have e5 : 2 * Δ / ν ≤ Δ := by rw [div_le_iff₀ hν0]; nlinarith
  have hS2 : 0 < S ^ 2 := by positivity
  have e7 : D * lR ≤ Δ := by
    calc D * lR ≤ Δ / (ν * S ^ 2) * (2 * lS) := mul_le_mul hD hlR hlR0 (by positivity)
      _ ≤ Δ / (ν * S ^ 2) * S ^ 2 := by gcongr
      _ = Δ / ν := by field_simp
      _ ≤ Δ := div_le_self hΔ (by linarith)
  have e8 : D * lK ≤ Δ := by
    calc D * lK ≤ Δ / (ν * S ^ 2) * ν := mul_le_mul hD hlK hlK0 (by positivity)
      _ = Δ / S ^ 2 := by field_simp
      _ ≤ Δ := div_le_self hΔ (by nlinarith)
  have e6 : Δ + Δ + ν ^ 2 * Δ + 2 * Δ ≤ 3 * (ν ^ 6 * Δ) / 4 := by
    have h9 : 9 ≤ ν ^ 2 := by nlinarith
    have : 4 + ν ^ 2 ≤ 3 * ν ^ 6 / 4 := by
      have e : ν ^ 6 = (ν ^ 2) ^ 2 * ν ^ 2 := by ring
      have hu2 : 81 ≤ (ν ^ 2) ^ 2 := by nlinarith
      have hu3 : 81 * ν ^ 2 ≤ (ν ^ 2) ^ 2 * ν ^ 2 :=
        mul_le_mul_of_nonneg_right hu2 (by positivity)
      rw [e]; linarith
    nlinarith
  have hsplit : (A₀ + D) * lR = A₀ * lR + D * lR := by ring
  rw [hsplit]
  linarith

end LSG.W88
