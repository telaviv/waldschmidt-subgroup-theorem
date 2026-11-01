/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7Bridge
import LSG.W88.Sec7Rat
import LSG.W88.Sec7Arith

/-!
# Auxiliary lemmas for the assembly of W88 §7

* `exists_gens`: a finitely generated subgroup is `closure (range y)`, `y : Fin μ → E`;
* `exists_periods`: `rk Z` `ℤ`-independent elements of `Z` (for `Z = Y ∩ Ω`);
* `obstr_delta_pos`: a proper obstruction has codimension `≥ 1`;
* **`log_count`**: the logarithm of the multiplicity estimate's conclusion, i.e. W88 (7.2) in the
  form needed by `core_ineq`.
-/

open MvPolynomial LSG.ME Module

noncomputable section

namespace LSG.W88

theorem exists_gens {E : Type*} [AddCommGroup E] (Y : AddSubgroup E) (hY : Y.FG) :
    ∃ (μ : ℕ) (y : Fin μ → E), AddSubgroup.closure (Set.range y) = Y := by
  obtain ⟨S, hS, hfin⟩ := (AddSubgroup.fg_iff Y).mp hY
  set s := hfin.toFinset
  refine ⟨s.card, fun i => (s.equivFin.symm i : E), ?_⟩
  have : Set.range (fun i => (s.equivFin.symm i : E)) = S := by
    rw [show (fun i => (s.equivFin.symm i : E)) = Subtype.val ∘ s.equivFin.symm from rfl,
      s.equivFin.symm.surjective.range_comp]
    ext x; simp [s]
  rw [this, hS]

theorem exists_periods {E : Type*} [AddCommGroup E] [Module ℚ E] (Z : AddSubgroup E)
    [FiniteDimensional ℚ (Submodule.span ℚ (Z : Set E))] :
    ∃ ω : Fin (rk Z) → E, (∀ i, ω i ∈ Z) ∧ LinearIndependent ℤ ω := by
  classical
  obtain ⟨b, hbZ, hbspan, hli⟩ := exists_linearIndependent ℚ (Z : Set E)
  have hli' : LinearIndependent ℚ (fun x : b => (⟨x.1, hbspan ▸ Submodule.subset_span x.2⟩ :
      Submodule.span ℚ (Z : Set E))) :=
    LinearIndependent.of_comp (Submodule.span ℚ (Z : Set E)).subtype hli
  have : Finite b := hli'.finite
  let _ : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = rk Z := by
    rw [rk, ← hbspan, ← finrank_span_eq_card hli, Subtype.range_coe]
  let eqv : Fin (rk Z) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (eqv i : E), fun i => hbZ (eqv i).2, ?_⟩
  exact ((hli.comp eqv eqv.injective).restrict_scalars' ℤ)

variable {d0 d1 m : ℕ} {Ls : Fin m → PeriodPair}

theorem finrank_h0_le (O : ObstrData d0 d1 Ls) : finrank ℂ O.h0 ≤ d0 := by
  simpa using Submodule.finrank_le O.h0

theorem finrank_U_le (O : ObstrData d0 d1 Ls) : finrank ℚ O.U ≤ d1 := by
  simpa using Submodule.finrank_le O.U

theorem finrank_t_le (O : ObstrData d0 d1 Ls) : finrank ℂ O.t ≤ m := by
  simpa using Submodule.finrank_le O.t

/-- **A proper obstruction has codimension `≥ 1`.** -/
theorem obstr_delta_pos (O : ObstrData d0 d1 Ls) (hO : O.Proper) :
    1 ≤ d0 - finrank ℂ O.h0 + finrank ℚ O.U + (m - finrank ℂ O.t) := by
  by_contra hcon
  apply hO
  have h1 : finrank ℂ O.h0 = d0 := by have := finrank_h0_le O; omega
  have h2 : finrank ℚ O.U = 0 := by omega
  have h3 : finrank ℂ O.t = m := by have := finrank_t_le O; omega
  have e1 : O.h0 = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using h1)
  have e2 : O.U = ⊥ := Submodule.finrank_eq_zero.mp h2
  have e3 : O.t = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using h3)
  have e4 : torusLie O.U = ⊤ := by
    rw [e2]
    refine eq_top_iff.mpr fun v _ φ hφ => ?_
    rw [Submodule.mem_bot] at hφ
    simp [hφ]
  rw [ObstrData.tan, e1, e4, e3, Submodule.prod_top, Submodule.prod_top]

/-- **The logarithm of W88 (7.2).** -/
theorem log_count {T M1 D0 D1 D2 C τ lam t0 u t2 d0 d1 m : ℕ}
    (ht0 : t0 ≤ d0) (hu : u ≤ d1) (ht2 : t2 ≤ m) (hT : 1 ≤ T) (hM : 1 ≤ M1) (h0 : 1 ≤ D0)
    (h1 : 1 ≤ D1) (h2 : 1 ≤ D2)
    (hcnt : T ^ τ * M1 ^ lam * D0 ^ t0 * D1 ^ (d1 - u) * D2 ^ t2 ≤ C * D0 ^ d0 * D1 ^ d1 * D2 ^ m)
    {LS ℓℓ LΔ cT c4 lnn : ℝ}
    (bT : LΔ - cT - ℓℓ ≤ Real.log T) (bM : LS - lnn ≤ Real.log M1)
    (b0 : Real.log D0 ≤ LΔ - 2 * ℓℓ + c4) (b1 : Real.log D1 ≤ LΔ - LS + c4)
    (b2 : Real.log D2 ≤ LΔ - 2 * LS + c4) :
    ((lam + u + 2 * (m - t2) : ℕ) : ℝ) * LS ≤
      (Real.log C + τ * cT + lam * lnn + ((d0 - t0 + u + (m - t2) : ℕ) : ℝ) * c4) +
        (((d0 - t0 + u + (m - t2) : ℕ) : ℝ) - τ) * LΔ + ((τ : ℝ) - 2 * (d0 - t0 : ℕ)) * ℓℓ := by
  -- cancel the common factor
  have hX : 0 < D0 ^ t0 * D1 ^ (d1 - u) * D2 ^ t2 := by positivity
  have hnat : T ^ τ * M1 ^ lam ≤ C * (D0 ^ (d0 - t0) * D1 ^ u * D2 ^ (m - t2)) := by
    refine Nat.le_of_mul_le_mul_right ?_ hX
    calc T ^ τ * M1 ^ lam * (D0 ^ t0 * D1 ^ (d1 - u) * D2 ^ t2)
        = T ^ τ * M1 ^ lam * D0 ^ t0 * D1 ^ (d1 - u) * D2 ^ t2 := by ring
      _ ≤ C * D0 ^ d0 * D1 ^ d1 * D2 ^ m := hcnt
      _ = C * (D0 ^ (d0 - t0) * D1 ^ u * D2 ^ (m - t2)) * (D0 ^ t0 * D1 ^ (d1 - u) * D2 ^ t2) := by
        have e0 : D0 ^ d0 = D0 ^ t0 * D0 ^ (d0 - t0) := by rw [← pow_add, Nat.add_sub_cancel' ht0]
        have e1 : D1 ^ d1 = D1 ^ (d1 - u) * D1 ^ u := by rw [← pow_add, Nat.sub_add_cancel hu]
        have e2 : D2 ^ m = D2 ^ t2 * D2 ^ (m - t2) := by rw [← pow_add, Nat.add_sub_cancel' ht2]
        rw [e0, e1, e2]; ring
  have hL1 : 1 ≤ T ^ τ * M1 ^ lam := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hC : 1 ≤ C := by
    rcases Nat.eq_zero_or_pos C with h | h
    · rw [h, zero_mul] at hnat; omega
    · exact h
  -- logarithms
  have hR : ((T : ℝ) ^ τ * (M1 : ℝ) ^ lam) ≤
      (C : ℝ) * ((D0 : ℝ) ^ (d0 - t0) * (D1 : ℝ) ^ u * (D2 : ℝ) ^ (m - t2)) := by
    exact_mod_cast hnat
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hM0 : (0 : ℝ) < M1 := by exact_mod_cast hM
  have hD0 : (0 : ℝ) < D0 := by exact_mod_cast h0
  have hD1 : (0 : ℝ) < D1 := by exact_mod_cast h1
  have hD2 : (0 : ℝ) < D2 := by exact_mod_cast h2
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  -- the bounds, multiplied by the exponents
  have m1 := mul_le_mul_of_nonneg_left bT (Nat.cast_nonneg τ)
  have m2 := mul_le_mul_of_nonneg_left bM (Nat.cast_nonneg lam)
  have m3 := mul_le_mul_of_nonneg_left b0 (Nat.cast_nonneg (d0 - t0))
  have m4 := mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg u)
  have m5 := mul_le_mul_of_nonneg_left b2 (Nat.cast_nonneg (m - t2))
  push_cast
  nlinarith [m1, m2, m3, m4, m5, hlog]

end LSG.W88
