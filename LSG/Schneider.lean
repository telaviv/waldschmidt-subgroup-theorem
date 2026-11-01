/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.Interface
import LSG.Weierstrass.Basic

/-!
# Schneider's theorems on elliptic periods

For a period pair `L` with `g₂, g₃` algebraic and a nonzero period `ω`:
* `LSG.Schneider.period_transcendental_of` : `ω` is transcendental;
* `LSG.Schneider.period_div_pi_transcendental_of` : `ω / π` is transcendental;

both conditional on the Schneider–Lang criterion `LSG.SchneiderLang` and on
`LSG.WeierstrassOrderTwo L` (`℘`, `℘'` are quotients of entire functions of order `≤ 2`).

Proof (Lang, *Introduction to transcendental numbers*, Ch. III): reduce to `ω` primitive, so
that `ω/2 ∉ Λ`; the points `w_k = ω/2 + kω` (`k ∈ ℤ`) are pairwise distinct and off the lattice.
* If `ω ∈ Q̄`: the functions `(z, ℘, ℘')` over `K = ℚ(g₂, g₃, e, ω)`, `e = ℘(ω/2)`, take the
  values `(w_k, e, 0) ∈ K³` at every `w_k`.
* If `ω/π ∈ Q̄`: `λ = 2πi/ω ∈ Q̄`, and `(℘, ℘', exp (λz))` over `K = ℚ(g₂, g₃, e, λ)` take the
  values `(e, 0, -1)`.
In both cases Schneider–Lang allows only finitely many such points.
-/

open Complex Filter Topology PeriodPair Real

namespace LSG.Schneider

open LSG.Weierstrass

variable (L : PeriodPair)

/-! ### Growth helpers -/

lemma growthLE_two_mul {f h : ℂ → ℂ} (hf : ∃ a : ℝ, ∀ z, ‖f z‖ ≤ Real.exp (a * (1 + ‖z‖) ^ (2 : ℝ)))
    (hh : GrowthLE 2 h) : GrowthLE 2 (fun z => f z * h z) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨C, hC⟩ := hh
  refine ⟨a + C, fun z => ?_⟩
  rw [norm_mul, add_mul, Real.exp_add]
  exact mul_le_mul (ha z) (hC z) (norm_nonneg _) (Real.exp_pos _).le

lemma norm_le_exp_sq (z : ℂ) : ‖z‖ ≤ Real.exp (1 * (1 + ‖z‖) ^ (2 : ℝ)) := by
  rw [Real.rpow_two, one_mul]
  have h0 := norm_nonneg z
  have h1 : ‖z‖ ≤ (1 + ‖z‖) ^ 2 := by nlinarith
  have h2 := Real.add_one_le_exp ((1 + ‖z‖) ^ 2)
  linarith

lemma norm_cexp_le_exp_sq (c z : ℂ) : ‖cexp (c * z)‖ ≤ Real.exp (‖c‖ * (1 + ‖z‖) ^ (2 : ℝ)) := by
  rw [Complex.norm_exp, Real.rpow_two]
  apply Real.exp_le_exp.mpr
  have h0 := norm_nonneg z
  have hc := norm_nonneg c
  have h1 : ‖z‖ ≤ (1 + ‖z‖) ^ 2 := by nlinarith
  calc (c * z).re ≤ ‖c * z‖ := Complex.re_le_norm _
    _ = ‖c‖ * ‖z‖ := norm_mul _ _
    _ ≤ ‖c‖ * (1 + ‖z‖) ^ 2 := mul_le_mul_of_nonneg_left h1 hc

/-! ### Small algebraic facts -/

lemma isAlgebraic_I : IsAlgebraic ℚ I := by
  refine ⟨Polynomial.X ^ 2 + 1, ?_, by simp⟩
  intro hp
  have := congrArg (Polynomial.coeff · 0) hp
  simp at this

/-- The points `ω/2 + kω` are pairwise distinct. -/
lemma injective_half_add_mul {ω : ℂ} (h0 : ω ≠ 0) :
    Function.Injective (fun k : ℤ => ω / 2 + k * ω) := by
  intro k l hkl
  simp only [add_right_inj] at hkl
  exact_mod_cast mul_right_cancel₀ h0 hkl

/-! ### The primitive cases -/

section Primitive

variable {L}
variable (hSL : SchneiderLang) (hW : WeierstrassOrderTwo L)
  (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
  {ω : ℂ} (hω : ω ∈ L.lattice) (h0 : ω ≠ 0) (h2 : ω / 2 ∉ L.lattice)
include hSL hW hg₂ hg₃ hω h0 h2

/-- Schneider's theorem, primitive case: `ω` is not algebraic. -/
theorem not_isAlgebraic_primitive (halg : IsAlgebraic ℚ ω) : False := by
  obtain ⟨h, gP, gP', hh, hgP, hgP', Gh, GgP, GgP', hzero, hval⟩ := hW
  have hne : ∀ z, h z ≠ 0 → z ∉ L.lattice := fun z hz hm => hz ((hzero z).mpr hm)
  have hne' : ∀ z, z ∉ L.lattice → h z ≠ 0 := fun z hz h0 => hz ((hzero z).mp h0)
  set e := ℘[L] (ω / 2) with he_def
  have he : IsAlgebraic ℚ e := isAlgebraic_weierstrassP_half L hg₂ hg₃ hω h2
  set K := IntermediateField.adjoin ℚ ({L.g₂, L.g₃, e, ω} : Set ℂ)
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl | rfl | rfl)
    · exact hg₂.isIntegral
    · exact hg₃.isIntegral
    · exact he.isIntegral
    · exact halg.isIntegral)
  have m₂ : L.g₂ ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have me : e ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have mω : ω ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have hfin := hSL K 3 ![fun z => z * h z, gP, gP'] h 2
    (by
      intro i
      fin_cases i
      · exact differentiable_id.mul hh
      · exact hgP
      · exact hgP')
    hh
    (by
      intro i
      fin_cases i
      · exact growthLE_two_mul ⟨1, norm_le_exp_sq⟩ Gh
      · exact GgP
      · exact GgP')
    Gh
    (by
      intro i
      fin_cases i
      · refine ⟨1, fun z hz => ?_⟩
        rw [map_one]
        refine (hasDerivAt_id' z).congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_compl_lattice L).mem_nhds (hne z hz)] with x hx
        simp [mul_div_cancel_right₀ _ (hne' x hx)]
      · refine ⟨MvPolynomial.X 2, fun z hz => ?_⟩
        simp only [MvPolynomial.aeval_X, Fin.isValue, Matrix.cons_val]
        rw [← (hval z (hne z hz)).2]
        refine (hasDerivAt_weierstrassP L (hne z hz)).congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_compl_lattice L).mem_nhds (hne z hz)] with x hx
        simp [← (hval x hx).1]
      · refine ⟨6 * MvPolynomial.X 1 ^ 2 - MvPolynomial.C (⟨L.g₂, m₂⟩ / 2), fun z hz => ?_⟩
        simp only [map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
          Fin.isValue, Matrix.cons_val, map_ofNat, map_div₀]
        rw [← (hval z (hne z hz)).1]
        convert (hasDerivAt_derivWeierstrassP L (hne z hz)).congr_of_eventuallyEq ?_ using 1
        · simp
        · filter_upwards [(isOpen_compl_lattice L).mem_nhds (hne z hz)] with x hx
          simp [← (hval x hx).2])
    ⟨0, 1, fun P hP => algIndep_id_weierstrassP L P fun z hz => by
      have := hP z (hne' z hz)
      simpa [mul_div_cancel_right₀ _ (hne' z hz), ← (hval z hz).1] using this⟩
  refine (Set.infinite_of_injective_forall_mem (injective_half_add_mul h0) ?_) hfin
  intro k
  have hw := half_add_mul_notMem L hω h2 k
  refine ⟨hne' _ hw, fun i => ?_⟩
  fin_cases i
  · refine ⟨⟨ω / 2 + k * ω, K.add_mem (K.div_mem mω (by simp))
      (K.mul_mem (K.intCast_mem k) mω)⟩, ?_⟩
    simp [mul_div_cancel_right₀ _ (hne' _ hw)]
  · refine ⟨⟨e, me⟩, ?_⟩
    simp [← (hval _ hw).1, weierstrassP_half_add_mul L hω k, he_def]
  · refine ⟨0, ?_⟩
    simp [← (hval _ hw).2, derivWeierstrassP_half_add_mul L hω k]

/-- Schneider's theorem, primitive case: `ω / π` is not algebraic. -/
theorem not_isAlgebraic_div_pi_primitive (halg : IsAlgebraic ℚ (ω / π)) : False := by
  obtain ⟨h, gP, gP', hh, hgP, hgP', Gh, GgP, GgP', hzero, hval⟩ := hW
  have hne : ∀ z, h z ≠ 0 → z ∉ L.lattice := fun z hz hm => hz ((hzero z).mpr hm)
  have hne' : ∀ z, z ∉ L.lattice → h z ≠ 0 := fun z hz h0 => hz ((hzero z).mp h0)
  set e := ℘[L] (ω / 2) with he_def
  have he : IsAlgebraic ℚ e := isAlgebraic_weierstrassP_half L hg₂ hg₃ hω h2
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hlam_eq : 2 * (π : ℂ) * I / ω = 2 * I * (ω / π)⁻¹ := by field_simp
  have hlam : IsAlgebraic ℚ (2 * (π : ℂ) * I / ω) := by
    rw [hlam_eq]
    have h2' : IsAlgebraic ℚ (2 : ℂ) := by simpa using isAlgebraic_natCast (R := ℚ) (A := ℂ) 2
    exact (h2'.mul isAlgebraic_I).mul (IsAlgebraic.inv_iff.mpr halg)
  set K := IntermediateField.adjoin ℚ ({L.g₂, L.g₃, e, 2 * (π : ℂ) * I / ω} : Set ℂ)
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl | rfl | rfl)
    · exact hg₂.isIntegral
    · exact hg₃.isIntegral
    · exact he.isIntegral
    · exact hlam.isIntegral)
  have m₂ : L.g₂ ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have me : e ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have mlam : 2 * (π : ℂ) * I / ω ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have hfin := hSL K 3 ![gP, gP', fun z => cexp (2 * π * I / ω * z) * h z] h 2
    (by
      intro i
      fin_cases i
      · exact hgP
      · exact hgP'
      · exact (differentiable_id.const_mul _).cexp.mul hh)
    hh
    (by
      intro i
      fin_cases i
      · exact GgP
      · exact GgP'
      · exact growthLE_two_mul ⟨_, norm_cexp_le_exp_sq _⟩ Gh)
    Gh
    (by
      intro i
      fin_cases i
      · refine ⟨MvPolynomial.X 1, fun z hz => ?_⟩
        simp only [MvPolynomial.aeval_X, Fin.isValue, Matrix.cons_val]
        rw [← (hval z (hne z hz)).2]
        refine (hasDerivAt_weierstrassP L (hne z hz)).congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_compl_lattice L).mem_nhds (hne z hz)] with x hx
        simp [← (hval x hx).1]
      · refine ⟨6 * MvPolynomial.X 0 ^ 2 - MvPolynomial.C (⟨L.g₂, m₂⟩ / 2), fun z hz => ?_⟩
        simp only [map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
          Fin.isValue, Matrix.cons_val, map_ofNat, map_div₀]
        rw [← (hval z (hne z hz)).1]
        convert (hasDerivAt_derivWeierstrassP L (hne z hz)).congr_of_eventuallyEq ?_ using 1
        · simp
        · filter_upwards [(isOpen_compl_lattice L).mem_nhds (hne z hz)] with x hx
          simp [← (hval x hx).2]
      · refine ⟨MvPolynomial.C ⟨2 * π * I / ω, mlam⟩ * MvPolynomial.X 2, fun z hz => ?_⟩
        simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Fin.isValue,
          Matrix.cons_val]
        have hd := ((hasDerivAt_id' z).const_mul (2 * π * I / ω)).cexp
        convert hd.congr_of_eventuallyEq ?_ using 1
        · simp [mul_div_cancel_right₀ _ hz]; ring
        · filter_upwards [hh.continuous.continuousAt.eventually_ne hz] with x hx
          simp [mul_div_cancel_right₀ _ hx])
    ⟨0, 2, fun P hP => algIndep_weierstrassP_exp L h0 P fun z hz => by
      have := hP z (hne' z hz)
      simpa [mul_div_cancel_right₀ _ (hne' z hz), ← (hval z hz).1] using this⟩
  refine (Set.infinite_of_injective_forall_mem (injective_half_add_mul h0) ?_) hfin
  intro k
  have hw := half_add_mul_notMem L hω h2 k
  refine ⟨hne' _ hw, fun i => ?_⟩
  fin_cases i
  · refine ⟨⟨e, me⟩, ?_⟩
    simp [← (hval _ hw).1, weierstrassP_half_add_mul L hω k, he_def]
  · refine ⟨0, ?_⟩
    simp [← (hval _ hw).2, derivWeierstrassP_half_add_mul L hω k]
  · refine ⟨-1, ?_⟩
    have hexp : 2 * (π : ℂ) * I / ω * (ω / 2 + k * ω) = π * I + k * (2 * π * I) := by
      field_simp
    change cexp (2 * (π : ℂ) * I / ω * (ω / 2 + k * ω)) * h (ω / 2 + k * ω) /
      h (ω / 2 + k * ω) = _
    rw [mul_div_cancel_right₀ _ (hne' _ hw), hexp, Complex.exp_add, Complex.exp_pi_mul_I,
      Complex.exp_int_mul_two_pi_mul_I]
    simp

end Primitive

/-! ### Schneider's theorems (conditional) -/

section Conditional

variable {L}

/-- **Schneider (1937), conditional form.** If `g₂, g₃` are algebraic, every nonzero period is
transcendental (assuming the Schneider–Lang criterion and the order-two representation of
`℘, ℘'`). -/
theorem period_transcendental_of (hSL : SchneiderLang) (hW : WeierstrassOrderTwo L)
    (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) {ω : ℂ} (hω : ω ∈ L.lattice)
    (h0 : ω ≠ 0) : Transcendental ℚ ω := by
  obtain ⟨m, ω₀, hm, hω₀, rfl, h2⟩ := exists_primitive L hω h0
  intro halg
  have h00 : ω₀ ≠ 0 := by rintro rfl; simp at h0
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have : IsAlgebraic ℚ ω₀ := by
    have := (IsAlgebraic.inv_iff.mpr (isAlgebraic_natCast (R := ℚ) (A := ℂ) m)).mul halg
    rwa [inv_mul_cancel_left₀ hm'] at this
  exact not_isAlgebraic_primitive hSL hW hg₂ hg₃ hω₀ h00 h2 this

/-- **Schneider (1937), conditional form.** If `g₂, g₃` are algebraic, `ω / π` is transcendental
for every nonzero period `ω`. -/
theorem period_div_pi_transcendental_of (hSL : SchneiderLang) (hW : WeierstrassOrderTwo L)
    (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) {ω : ℂ} (hω : ω ∈ L.lattice)
    (h0 : ω ≠ 0) : Transcendental ℚ (ω / (π : ℂ)) := by
  obtain ⟨m, ω₀, hm, hω₀, rfl, h2⟩ := exists_primitive L hω h0
  intro halg
  have h00 : ω₀ ≠ 0 := by rintro rfl; simp at h0
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have : IsAlgebraic ℚ (ω₀ / π) := by
    have := (IsAlgebraic.inv_iff.mpr (isAlgebraic_natCast (R := ℚ) (A := ℂ) m)).mul halg
    rwa [mul_div_assoc, inv_mul_cancel_left₀ hm'] at this
  exact not_isAlgebraic_div_pi_primitive hSL hW hg₂ hg₃ hω₀ h00 h2 this

end Conditional

end LSG.Schneider
