/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.ExpCoordsN

/-!
# Charts for `exp_{E^♮}` with lower bounds (analogue of `LSG/AuxFun/Chart.lean`)

For every `u ∈ ℂ` there is a **base** coordinate `X_i ∈ {U, V, W}` of `ellN` (the entire
coordinates of `exp_{E^♮}`) with
* `|X_i(u + z, w)| ≥ e^{−c(1+|u|)²}` for `|z| ≤ ρ₀` and **all** `w` (the base coordinates do not
  depend on `w`; this is `LSG.Aux.exists_chart`), and
* every coordinate is dominated in that chart:
  `|ellN(u + z, w)_k| ≤ (1 + |w|) e^{c(1+|u|)²} |X_i(u + z, w)|` (the affine chart coordinates
  `ellN_k / X_i`, including the two fibre coordinates `T₁/X_i`, `T₃/X_i`, are bounded by
  `(1 + |w|) e^{c(1+|u|)²}`).

This is the input of W83's Step 2 / Lemma U for `E^♮` blocks: the fibre forms of `G₂`
(`fibF`) divided by `Π_j X_{j,i_j}` are polynomials in these affine coordinates and in `s`.

* **`exists_chartN`**.
-/

open Complex Finset LSG.Weierstrass PeriodPair

noncomputable section

namespace LSG.AuxV

variable (L : PeriodPair)

/-- The base coordinate `i : Fin 3` of `ellN` is the coordinate `i` of `ellV`. -/
lemma ellN_castSucc (z w : ℂ) (i : Fin 3) :
    ellN L z w (Fin.castSucc (Fin.castSucc i)) = LSG.Aux.ellV L z i := by
  fin_cases i <;> rfl

/-- **Chart lower bound for `exp_{E^♮}`** with domination of all five coordinates. -/
theorem exists_chartN : ∃ ρ₀ c : ℝ, 0 < ρ₀ ∧ 0 ≤ c ∧ ∀ u : ℂ, ∃ i : Fin 3, ∀ z w : ℂ,
    ‖z‖ ≤ ρ₀ →
      Real.exp (-(c * (1 + ‖u‖) ^ 2)) ≤ ‖ellN L (u + z) w (Fin.castSucc (Fin.castSucc i))‖ ∧
      ∀ k, ‖ellN L (u + z) w k‖ ≤
        (1 + ‖w‖) * Real.exp (c * (1 + ‖u‖) ^ 2) *
          ‖ellN L (u + z) w (Fin.castSucc (Fin.castSucc i))‖ := by
  obtain ⟨ρ₀, c₀, hρ₀, hc₀, hch⟩ := LSG.Aux.exists_chart L
  obtain ⟨cg, hcg0, hcg⟩ := exists_ellN_growth L
  set A : ℝ := cg * (1 + ρ₀) ^ 2
  have hA0 : 0 ≤ A := by positivity
  refine ⟨ρ₀, A + c₀, hρ₀, by positivity, fun u => ?_⟩
  obtain ⟨i, hi⟩ := hch u
  refine ⟨i, fun z w hz => ?_⟩
  have hlow := hi z hz
  rw [← ellN_castSucc L (u + z) w i] at hlow
  set X := ‖ellN L (u + z) w (Fin.castSucc (Fin.castSucc i))‖
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hsq : 0 ≤ (1 + ‖u‖) ^ 2 := by positivity
  constructor
  · refine le_trans (Real.exp_le_exp.mpr ?_) hlow
    have : c₀ * (1 + ‖u‖) ^ 2 ≤ (A + c₀) * (1 + ‖u‖) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hsq
    linarith
  · intro k
    have hg := hcg k (u + z) w
    have h1 : (1 + ‖u + z‖) ^ 2 ≤ (1 + ρ₀) ^ 2 * (1 + ‖u‖) ^ 2 := by
      have : 1 + ‖u + z‖ ≤ (1 + ρ₀) * (1 + ‖u‖) := by
        have := norm_add_le u z
        nlinarith [norm_nonneg z]
      calc (1 + ‖u + z‖) ^ 2 ≤ ((1 + ρ₀) * (1 + ‖u‖)) ^ 2 := by gcongr
        _ = _ := by ring
    have h2 : Real.exp (cg * (1 + ‖u + z‖) ^ 2) ≤ Real.exp (A * (1 + ‖u‖) ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      calc cg * (1 + ‖u + z‖) ^ 2 ≤ cg * ((1 + ρ₀) ^ 2 * (1 + ‖u‖) ^ 2) := by gcongr
        _ = A * (1 + ‖u‖) ^ 2 := by ring
    have h3 : 1 ≤ Real.exp (c₀ * (1 + ‖u‖) ^ 2) * X := by
      have := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (c₀ * (1 + ‖u‖) ^ 2)).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
    have hw : 0 ≤ 1 + ‖w‖ := by positivity
    calc ‖ellN L (u + z) w k‖ ≤ (1 + ‖w‖) * Real.exp (A * (1 + ‖u‖) ^ 2) :=
          hg.trans (mul_le_mul_of_nonneg_left h2 hw)
      _ ≤ (1 + ‖w‖) * Real.exp (A * (1 + ‖u‖) ^ 2) * (Real.exp (c₀ * (1 + ‖u‖) ^ 2) * X) :=
          le_mul_of_one_le_right (by positivity) h3
      _ = (1 + ‖w‖) * Real.exp ((A + c₀) * (1 + ‖u‖) ^ 2) * X := by
          rw [show (A + c₀) * (1 + ‖u‖) ^ 2 = A * (1 + ‖u‖) ^ 2 + c₀ * (1 + ‖u‖) ^ 2 by ring,
            Real.exp_add]; ring

end LSG.AuxV
