/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.MainHyp

/-!
# The sliced coset lower bound from an unsliced lower bound for `H⁰` (α; STAGE_A4 §7.3 (6), step 1)

ME's `hfun_P_coset_ge` for abstract blocks. Assume the unsliced Hilbert lower bound for `I(H⁰)`
(`H0LowerBound O cH`, ME's `hfun_H0_ge''`):
`(tD₀/t₀+1)^{t₀} (tD₁/t₁+1)^{t₁} (tD₂+1)^{t₂+m} ≤ cH · H(I(H⁰); t)`. Translation (`hfun_le_transl`, factor `nLaw B`,
`t ↦ 2t`) and slicing (`hfun_le_of_hom`, factor `(2tD₂+1)^m`) give **`coset_ge_of_lower`**, the field
`SubgroupData.coset_ge` with `cL = cH · nLaw B · 2^m`.

The exponent `t₂ + m` accounts for the cone dimensions: `g_k + 1` for a pivot block, `1` for a non-pivot block.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun)

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-- **The unsliced Hilbert lower bound for `H⁰ = O.grp`** (to be proved in `HilbH0*.lean`). -/
def H0LowerBound (O : ObstrDataB d₀ d₁ B) (cH : ℕ) : Prop :=
  ∀ D₀ D₁ D₂ t : ℕ,
    (t * D₀ / finrank ℂ O.h0 + 1) ^ finrank ℂ O.h0 *
        (t * D₁ / (d₁ - finrank ℚ O.U) + 1) ^ (d₁ - finrank ℚ O.U) *
        (t * D₂ + 1) ^ (finrank ℂ O.t + m) ≤
      cH * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanish O.grp) t

/-- **The sliced coset lower bound** (`SubgroupData.coset_ge`) from `H0LowerBound`. -/
theorem coset_ge_of_lower {O : ObstrDataB d₀ d₁ B} {cH : ℕ} (hlow : H0LowerBound O cH) :
    ∀ (α : Alpha B) (a : GPt d₀ d₁ B), (∀ k, lsl α k ∉ vanish (gtransl a O.grp)) →
    ∀ D₀ D₁ D₂ t : ℕ,
      (t * D₀ / finrank ℂ O.h0 + 1) ^ finrank ℂ O.h0 *
          (t * D₁ / (d₁ - finrank ℚ O.U) + 1) ^ (d₁ - finrank ℚ O.U) *
          (t * D₂ + 1) ^ finrank ℂ O.t ≤
        (cH * nLaw B * 2 ^ m) *
          hfun blk (DfunB D₀ D₁ D₂) ℂ (vanishP Finset.univ α (gtransl a O.grp)) (2 * t) := by
  intro α a hℓ D₀ D₁ D₂ t
  have hpa := vanish_gtransl_isPrime (vanish_grp_isPrime O) a
  have h1 := hlow D₀ D₁ D₂ t
  have h2 := hfun_le_transl (DfunB D₀ D₁ D₂) O.grp a t
  have h3 := hfun_le_of_hom α hpa hℓ _
    (fun _ _ hQ hs => hom_mem_vanish_of_mem_vanishP hpa hℓ hQ hs) (DfunB D₀ D₁ D₂) (2 * t)
  have hprod : ∏ k : Fin m, (2 * t * DfunB (m := m) D₀ D₁ D₂ (.e k) + 1) =
      (2 * t * D₂ + 1) ^ m := by
    simp [DfunB]
  rw [hprod] at h3
  set X := (t * D₀ / finrank ℂ O.h0 + 1) ^ finrank ℂ O.h0 *
    (t * D₁ / (d₁ - finrank ℚ O.U) + 1) ^ (d₁ - finrank ℚ O.U)
  set y := t * D₂ + 1
  set hP := hfun blk (DfunB D₀ D₁ D₂) ℂ (vanishP Finset.univ α (gtransl a O.grp)) (2 * t)
  have hy : 0 < y := Nat.succ_pos _
  have h2y : 2 * t * D₂ + 1 ≤ 2 * y := by simp only [y]; nlinarith
  have hchain : X * y ^ finrank ℂ O.t * y ^ m ≤ (cH * nLaw B * 2 ^ m) * hP * y ^ m := by
    calc X * y ^ finrank ℂ O.t * y ^ m = X * y ^ (finrank ℂ O.t + m) := by rw [pow_add]; ring
      _ ≤ cH * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanish O.grp) t := h1
      _ ≤ cH * (nLaw B * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanish (gtransl a O.grp)) (2 * t)) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ cH * (nLaw B * ((2 * t * D₂ + 1) ^ m * hP)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ cH * (nLaw B * ((2 * y) ^ m * hP)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2y m)))
      _ = (cH * nLaw B * 2 ^ m) * hP * y ^ m := by rw [mul_pow]; ring
  exact Nat.le_of_mul_le_mul_right hchain (pow_pos hy m)

end LSG.MEB
