/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.HilbH0
import LSG.MEBV.MainHyp

/-!
# The sliced coset lower bound (M2.5 β′; template `LSG.MEB.CosetGe`)

From the unsliced lower bound for `H⁰` (`h0LowerBoundV`), **`coset_ge_of_lowerV`** gives the field
`SubgroupDataV.coset_ge` (Hilbert function of the sliced coset at `2t`).

Translation multiplies degrees by `K = 2^{eL B}` (`hfun_le_transl`), not by `2` as in MEB. So the lower bound is
applied at `t′ = 1` with the degrees `D′ᵢ = ⌊2tDᵢ/K⌋` (`K D′ ≤ 2tD`, **`hfun_le_of_le`**: the Hilbert function is
monotone in the degree vector), and each factor loses at most `K` (**`succ_div_le`**). Constant
`cCG B cH = K^{dimG + m} · cH · nLaw B · 2^m`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun)

namespace LSG.MEBV

open LSG.MEB (Blk DfunB)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- **The Hilbert function is monotone in the degree vector.** -/
theorem hfun_le_of_le {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] (β : σ → ι)
    {D D' : ι → ℕ} {t t' : ℕ} (J : Ideal (MvPolynomial σ ℂ)) (h : t • D ≤ t' • D') :
    hfun β D ℂ J t ≤ hfun β D' ℂ J t' := by
  unfold StrongSix.M2.hfun
  set F := FLE ℂ β (t • D)
  set F' := FLE ℂ β (t' • D')
  have hFF : F ≤ F' := StrongSix.M2.FLE_mono ℂ β h
  set I := J.restrictScalars ℂ
  haveI : FiniteDimensional ℂ ↥(I ⊓ F') := Submodule.finiteDimensional_of_le inf_le_right
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq F (I ⊓ F')
  have h2 : F ⊓ (I ⊓ F') = I ⊓ F := by
    rw [inf_comm I F', ← inf_assoc, inf_eq_left.mpr hFF, inf_comm]
  have h3 : finrank ℂ ↥(F ⊔ (I ⊓ F')) ≤ finrank ℂ F' := Submodule.finrank_mono (sup_le hFF inf_le_right)
  have h4 : finrank ℂ ↥(I ⊓ F) ≤ finrank ℂ F := Submodule.finrank_mono inf_le_right
  have h5 : finrank ℂ ↥(I ⊓ F') ≤ finrank ℂ F' := Submodule.finrank_mono inf_le_right
  rw [h2] at h1
  omega

/-- **Each factor loses at most `K`**: `x/e + 1 ≤ K (⌊2x/K⌋/e + 1)`. -/
theorem succ_div_le (x e K : ℕ) (hK : 0 < K) : x / e + 1 ≤ K * (2 * x / K / e + 1) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp; omega
  rw [Nat.div_div_eq_div_mul]
  set q := x / e
  set y := 2 * x / (K * e)
  have h1 : e * q ≤ x := Nat.mul_div_le x e
  have h2 : 2 * x < K * e * (y + 1) := Nat.lt_mul_div_succ _ (Nat.mul_pos hK he)
  by_contra hc
  push Not at hc
  have h3 : K * (y + 1) ≤ q := by omega
  have h4 : K * e * (y + 1) ≤ e * q := by nlinarith
  omega

variable (B) in
/-- The constant of `coset_ge`. -/
def cCG (cH : ℕ) : ℕ := (2 ^ eL B) ^ (dimG d₀ d₁ B + m) * cH * nLaw B * 2 ^ m

theorem cCG_pos {cH : ℕ} (hcH : 0 < cH) : 0 < cCG (d₀ := d₀) (d₁ := d₁) B cH := by
  have := nLaw_pos (B := B)
  unfold cCG; positivity

theorem ex_sum_le (O : ObstrDataGV d₀ d₁ B) :
    ex0 O.tan + (d₁ - finrank ℚ O.U) + ex2 O.tan ≤ dimG d₀ d₁ B := by
  have h := finrank_tanOfV (B := B) O.gam O.U O.t
  have h2 : finrank ℂ O.tan ≤ finrank ℂ (Tan d₀ d₁ B) := Submodule.finrank_le _
  rw [finrank_Tan] at h2
  change ex0 (tanOfV d₀ d₁ B O.gam O.U O.t) + (d₁ - finrank ℚ O.U) + ex2 (tanOfV d₀ d₁ B O.gam O.U O.t) ≤ _
  rw [← h]; exact h2

/-- **The sliced coset lower bound** (`SubgroupDataV.coset_ge`) from `H0LowerBoundV`. -/
theorem coset_ge_of_lowerV {O : ObstrDataGV d₀ d₁ B} {cH : ℕ} (hlow : H0LowerBoundV O cH) :
    ∀ (α : Alpha B) (a : GPt d₀ d₁ B), (∀ k, lsl α k ∉ vanish (gtransl a O.grp)) →
    ∀ D₀ D₁ D₂ t : ℕ,
      (t * D₀ / ex0 O.tan + 1) ^ ex0 O.tan *
          (t * D₁ / (d₁ - finrank ℚ O.U) + 1) ^ (d₁ - finrank ℚ O.U) *
          (t * D₂ + 1) ^ ex2 O.tan ≤
        cCG (d₀ := d₀) (d₁ := d₁) B cH *
          hfun blk (DfunB D₀ D₁ D₂) ℂ (vanishP Finset.univ α (gtransl a O.grp)) (2 * t) := by
  intro α a hℓ D₀ D₁ D₂ t
  set K := 2 ^ eL B with hKdef
  have hK : 0 < K := by positivity
  set e₀ := ex0 O.tan
  set e₁ := d₁ - finrank ℚ O.U
  set e₂ := ex2 O.tan
  set D'₀ := 2 * (t * D₀) / K
  set D'₁ := 2 * (t * D₁) / K
  set D'₂ := 2 * (t * D₂) / K
  have hpa := vanish_gtransl_isPrime (vanish_grp_isPrime O) a
  have h1 := hlow D'₀ D'₁ D'₂ 1
  simp only [one_mul] at h1
  have h2 := hfun_le_transl (DfunB D'₀ D'₁ D'₂) O.grp a 1
  have h3 : hfun blk (DfunB D'₀ D'₁ D'₂) ℂ (vanish (gtransl a O.grp)) (K * 1) ≤
      hfun blk (DfunB D₀ D₁ D₂) ℂ (vanish (gtransl a O.grp)) (2 * t) := by
    refine hfun_le_of_le blk _ fun b => ?_
    cases b with
    | x => simp only [Pi.smul_apply, smul_eq_mul, DfunB, D'₀, mul_one]; nlinarith [Nat.mul_div_le (2 * (t * D₀)) K]
    | yz => simp only [Pi.smul_apply, smul_eq_mul, DfunB, D'₁, mul_one]; nlinarith [Nat.mul_div_le (2 * (t * D₁)) K]
    | e k => simp only [Pi.smul_apply, smul_eq_mul, DfunB, D'₂, mul_one]; nlinarith [Nat.mul_div_le (2 * (t * D₂)) K]
  have h4 := hfun_le_of_hom α hpa hℓ _
    (fun _ _ hQ hs => hom_mem_vanish_of_mem_vanishP hpa hℓ hQ hs) (DfunB D₀ D₁ D₂) (2 * t)
  have hprod : ∏ k : Fin m, (2 * t * DfunB (m := m) D₀ D₁ D₂ (.e k) + 1) = (2 * t * D₂ + 1) ^ m := by
    simp [DfunB]
  rw [hprod] at h4
  set hP := hfun blk (DfunB D₀ D₁ D₂) ℂ (vanishP Finset.univ α (gtransl a O.grp)) (2 * t)
  set y := t * D₂ + 1
  have hy : 0 < y := Nat.succ_pos _
  have h2y : 2 * t * D₂ + 1 ≤ 2 * y := by simp only [y]; nlinarith
  -- the factors
  have f0 : t * D₀ / e₀ + 1 ≤ K * (D'₀ / e₀ + 1) := succ_div_le _ _ _ hK
  have f1 : t * D₁ / e₁ + 1 ≤ K * (D'₁ / e₁ + 1) := succ_div_le _ _ _ hK
  have f2 : y ≤ K * (D'₂ + 1) := by
    have := succ_div_le (t * D₂) 1 K hK
    simpa [y] using this
  have hE := ex_sum_le O
  have hKE : K ^ (e₀ + e₁ + e₂ + m) ≤ K ^ (dimG d₀ d₁ B + m) :=
    Nat.pow_le_pow_right hK (by omega)
  have hchain : (t * D₀ / e₀ + 1) ^ e₀ * (t * D₁ / e₁ + 1) ^ e₁ * y ^ e₂ * y ^ m ≤
      cCG (d₀ := d₀) (d₁ := d₁) B cH * hP * y ^ m := by
    calc (t * D₀ / e₀ + 1) ^ e₀ * (t * D₁ / e₁ + 1) ^ e₁ * y ^ e₂ * y ^ m
        ≤ (K * (D'₀ / e₀ + 1)) ^ e₀ * (K * (D'₁ / e₁ + 1)) ^ e₁ * (K * (D'₂ + 1)) ^ e₂ *
            (K * (D'₂ + 1)) ^ m := by
          gcongr
      _ = K ^ (e₀ + e₁ + e₂ + m) * ((D'₀ / e₀ + 1) ^ e₀ * (D'₁ / e₁ + 1) ^ e₁ * (D'₂ + 1) ^ (e₂ + m)) := by
          simp only [mul_pow, pow_add]; ring
      _ ≤ K ^ (dimG d₀ d₁ B + m) * (cH * hfun blk (DfunB D'₀ D'₁ D'₂) ℂ (vanish O.grp) 1) :=
          Nat.mul_le_mul hKE h1
      _ ≤ K ^ (dimG d₀ d₁ B + m) * (cH * (nLaw B * hfun blk (DfunB D'₀ D'₁ D'₂) ℂ
            (vanish (gtransl a O.grp)) (K * 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ ≤ K ^ (dimG d₀ d₁ B + m) * (cH * (nLaw B * ((2 * t * D₂ + 1) ^ m * hP))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (h3.trans h4)))
      _ ≤ K ^ (dimG d₀ d₁ B + m) * (cH * (nLaw B * ((2 * y) ^ m * hP))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2y m))))
      _ = cCG (d₀ := d₀) (d₁ := d₁) B cH * hP * y ^ m := by
          rw [cCG, mul_pow]; ring
  exact Nat.le_of_mul_le_mul_right hchain (pow_pos hy m)

end LSG.MEBV
