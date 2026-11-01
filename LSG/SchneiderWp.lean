/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Schneider
import LSG.Weierstrass.Dictionary

/-!
# Schneider's theorem on values of `℘` at algebraic points (conditional)

`LSG.Schneider.wp_transcendental_of`: if `g₂, g₃` are algebraic and `α ∉ Λ` is algebraic, then
`℘(α)` is transcendental — assuming the Schneider–Lang criterion `LSG.SchneiderLang` and the
order-two representation `LSG.WeierstrassOrderTwo L`.

Proof. Suppose `℘(α)` is algebraic; then so is `℘'(α)` (`℘'² = 4℘³ - g₂℘ - g₃`).
* If `kα ∈ Λ` for some `k ≥ 1`, then `kα` is a nonzero algebraic period, contradicting
  `period_transcendental_of`.
* Otherwise, over `K = ℚ(g₂, g₃, α, ℘(α), ℘'(α))` the functions `(z, ℘, ℘')` take values in `K` at
  all the points `kα`, `k ≥ 1` (`mem_of_intCast_mul`: the group law), which are pairwise distinct;
  Schneider–Lang (`finite_of_schneiderLang`) allows only finitely many such points.
-/

open Complex Filter Topology PeriodPair

namespace LSG.Schneider

open LSG.Weierstrass

variable {L : PeriodPair}

/-- Schneider–Lang applied to `(z, ℘, ℘')`: over a number field `K ∋ g₂`, only finitely many
`w ∉ Λ` have `w, ℘(w), ℘'(w) ∈ K`. -/
theorem finite_of_schneiderLang (hSL : SchneiderLang) (hW : WeierstrassOrderTwo L)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (m₂ : L.g₂ ∈ K) :
    Set.Finite {w : ℂ | w ∉ L.lattice ∧ w ∈ K ∧ ℘[L] w ∈ K ∧ ℘'[L] w ∈ K} := by
  obtain ⟨h, gP, gP', hh, hgP, hgP', Gh, GgP, GgP', hzero, hval⟩ := hW
  have hne : ∀ z, h z ≠ 0 → z ∉ L.lattice := fun z hz hm => hz ((hzero z).mpr hm)
  have hne' : ∀ z, z ∉ L.lattice → h z ≠ 0 := fun z hz h0 => hz ((hzero z).mp h0)
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
  refine hfin.subset ?_
  rintro w ⟨hw, hwK, hPK, hP'K⟩
  refine ⟨hne' w hw, fun i => ?_⟩
  fin_cases i
  · exact ⟨⟨w, hwK⟩, by simp [mul_div_cancel_right₀ _ (hne' w hw)]⟩
  · exact ⟨⟨℘[L] w, hPK⟩, by simp [← (hval w hw).1]⟩
  · exact ⟨⟨℘'[L] w, hP'K⟩, by simp [← (hval w hw).2]⟩

/-- If `℘(α)` and `g₂, g₃` are algebraic, so is `℘'(α)`. -/
lemma isAlgebraic_derivWeierstrassP (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
    {α : ℂ} (hαΛ : α ∉ L.lattice) (hP : IsAlgebraic ℚ (℘[L] α)) :
    IsAlgebraic ℚ (℘'[L] α) := by
  set A := (algebraicClosure ℚ ℂ).toSubfield
  have hA : ∀ x : ℂ, x ∈ A ↔ IsAlgebraic ℚ x := fun x => mem_algebraicClosure_iff
  refine IsAlgebraic.of_pow two_pos ?_
  rw [← hA, L.derivWeierstrassP_sq α hαΛ]
  have h1 := (hA _).mpr hP
  have h2 := (hA _).mpr hg₂
  have h3 := (hA _).mpr hg₃
  exact A.sub_mem (A.sub_mem (A.mul_mem (show (4 : ℂ) ∈ A by simp) (A.pow_mem h1 3))
    (A.mul_mem h2 h1)) h3

/-- **Schneider (1937), `℘` at algebraic points (conditional form).** If `g₂, g₃` are algebraic
and `α ∉ Λ` is algebraic, then `℘(α)` is transcendental (assuming the Schneider–Lang criterion
and the order-two representation of `℘, ℘'`). -/
theorem wp_transcendental_of (hSL : SchneiderLang) (hW : WeierstrassOrderTwo L)
    (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) {α : ℂ} (hα : IsAlgebraic ℚ α)
    (hαΛ : α ∉ L.lattice) : Transcendental ℚ (℘[L] α) := by
  intro hP
  have hα0 : α ≠ 0 := by rintro rfl; exact hαΛ L.lattice.zero_mem
  by_cases htor : ∃ k : ℕ, 0 < k ∧ (k : ℂ) * α ∈ L.lattice
  · -- torsion: `kα` is a nonzero algebraic period
    obtain ⟨k, hk, hkα⟩ := htor
    have hk0 : (k : ℂ) * α ≠ 0 := mul_ne_zero (by exact_mod_cast hk.ne') hα0
    exact period_transcendental_of hSL hW hg₂ hg₃ hkα hk0
      ((isAlgebraic_natCast (R := ℚ) (A := ℂ) k).mul hα)
  push_neg at htor
  have hP' := isAlgebraic_derivWeierstrassP hg₂ hg₃ hαΛ hP
  set K := IntermediateField.adjoin ℚ ({L.g₂, L.g₃, α, ℘[L] α, ℘'[L] α} : Set ℂ)
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · exact hg₂.isIntegral
    · exact hg₃.isIntegral
    · exact hα.isIntegral
    · exact hP.isIntegral
    · exact hP'.isIntegral)
  have m₂ : L.g₂ ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have mα : α ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have mP : ℘[L] α ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have mP' : ℘'[L] α ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have hfin := finite_of_schneiderLang hSL hW K m₂
  have hinj : Function.Injective (fun k : ℕ => ((k + 1 : ℕ) : ℂ) * α) := by
    intro k l hkl
    have := mul_right_cancel₀ hα0 hkl
    exact_mod_cast Nat.succ_injective (by exact_mod_cast this)
  refine (Set.infinite_of_injective_forall_mem hinj ?_) hfin
  intro k
  have hk : ((k + 1 : ℕ) : ℂ) * α ∉ L.lattice := htor (k + 1) (Nat.succ_pos k)
  have hk' : (((k + 1 : ℕ) : ℤ) : ℂ) * α ∉ L.lattice := by exact_mod_cast hk
  obtain ⟨h1, h2⟩ := mem_of_intCast_mul L K.toSubfield m₂ hαΛ mP mP' ((k + 1 : ℕ) : ℤ) hk'
  simp only [Int.cast_natCast] at h1 h2
  exact ⟨hk, K.mul_mem (K.natCast_mem _) mα, h1, h2⟩

end LSG.Schneider
