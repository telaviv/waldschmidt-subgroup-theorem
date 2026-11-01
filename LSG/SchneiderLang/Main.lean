/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.Interface
import LSG.SchneiderLang.Core

/-!
# The Schneider–Lang criterion

`LSG.schneiderLang : LSG.SchneiderLang`. Reduction to `LSG.SL.core`: make the order `ρ` a positive
integer and the growth constant common and nonnegative; if the set of `K`-points were infinite,
pick `4 [K:ℚ] ρ + 1` of them.
-/

open MvPolynomial

namespace LSG

theorem SL.exp_growth_le {C C' ρ : ℝ} {ρ' : ℕ} (hCC : C ≤ C') (hC' : 0 ≤ C') (hρ : ρ ≤ ρ')
    (t : ℝ) (ht : 0 ≤ t) : Real.exp (C * (1 + t) ^ ρ) ≤ Real.exp (C' * (1 + t) ^ ρ') := by
  refine Real.exp_le_exp.mpr ?_
  have h1 : (1 : ℝ) ≤ 1 + t := by linarith
  have h2 : (1 + t) ^ ρ ≤ (1 + t) ^ ρ' := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 hρ
  have h3 : 0 ≤ (1 + t) ^ ρ := Real.rpow_nonneg (by linarith) _
  calc C * (1 + t) ^ ρ ≤ C' * (1 + t) ^ ρ := mul_le_mul_of_nonneg_right hCC h3
    _ ≤ C' * (1 + t) ^ ρ' := mul_le_mul_of_nonneg_left h2 hC'

/-- **The Schneider–Lang criterion** (Lang, *Introduction to transcendental numbers*, Ch. III,
Thm 1). -/
theorem schneiderLang : SchneiderLang := by
  intro K _ N g h ρ hg hh hgG hhG hQ hind
  classical
  have : NumberField K := ⟨⟩
  set σ : K →+* ℂ := algebraMap K ℂ with hσ
  by_contra hfin
  have hinf : Set.Infinite {w : ℂ | h w ≠ 0 ∧ ∀ i, ∃ k : K, g i w / h w = (k : ℂ)} := hfin
  -- order and growth constant
  set ρ' : ℕ := max 1 ⌈ρ⌉₊ with hρ'
  have hρ'1 : 1 ≤ ρ' := le_max_left _ _
  have hρρ' : ρ ≤ (ρ' : ℝ) :=
    (Nat.le_ceil ρ).trans (by exact_mod_cast le_max_right 1 ⌈ρ⌉₊)
  choose Cg hCg using hgG
  obtain ⟨Ch, hCh⟩ := hhG
  set C : ℝ := |Ch| + ∑ i, |Cg i| with hC
  have hC0 : 0 ≤ C := by positivity
  have hCgC : ∀ i, Cg i ≤ C := fun i => by
    have := Finset.single_le_sum (f := fun i => |Cg i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith [le_abs_self (Cg i), abs_nonneg Ch]
  have hChC : Ch ≤ C := by
    have : 0 ≤ ∑ i, |Cg i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self Ch]
  have hgC : ∀ i z, ‖g i z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ') := fun i z =>
    (hCg i z).trans (SL.exp_growth_le (hCgC i) hC0 hρρ' _ (norm_nonneg _))
  have hhC : ∀ z, ‖h z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ') := fun z =>
    (hCh z).trans (SL.exp_growth_le hChC hC0 hρρ' _ (norm_nonneg _))
  -- derivatives and independence in `eval₂` form
  choose Q hQ' using hQ
  have hQ'' : ∀ i z, h z ≠ 0 →
      HasDerivAt (fun x => g i x / h x) (eval₂ σ (fun j => g j z / h z) (Q i)) z := by
    intro i z hz
    simpa [aeval_def] using hQ' i z hz
  obtain ⟨i₁, i₂, hind'⟩ := hind
  have hind'' : ∀ P : MvPolynomial (Fin 2) K,
      (∀ z, h z ≠ 0 → eval₂ σ ![g i₁ z / h z, g i₂ z / h z] P = 0) → P = 0 := by
    intro P hP
    exact hind' P fun z hz => by rw [aeval_def]; exact hP z hz
  -- many points
  set m : ℕ := 4 * Module.finrank ℚ K * ρ' + 1 with hm
  obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq m
  let e : Fin m ≃ t := (t.equivFin.trans (finCongr htc)).symm
  let w : Fin m → ℂ := fun j => (e j : ℂ)
  have hw : Function.Injective w := Subtype.val_injective.comp e.injective
  have hwS : ∀ j, w j ∈ {w : ℂ | h w ≠ 0 ∧ ∀ i, ∃ k : K, g i w / h w = (k : ℂ)} :=
    fun j => hts (e j).2
  have hwh : ∀ j, h (w j) ≠ 0 := fun j => (hwS j).1
  choose x hx using fun j => (hwS j).2
  exact SL.core σ g h ρ' hρ'1 C hC0 hg hh hgC hhC Q hQ'' i₁ i₂ hind'' m (by omega) w hw hwh x
    (fun j i => hx j i)

end LSG
