/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.TaylorCharts

/-!
# The Taylor bounds in charts 4 and 8 from the `A1Facts` tables (STAGE_A3 §8)

* `sz_ratTable`: an entry `num / den` with `|num| ≤ H` has size `(H / den, den)`;
* **`ThetaData.ks_chart4F`**, **`ThetaData.ks_chart8`**: the `KS` bounds in the charts `X₄ = 1` and `X₈ = 1`
  (hypotheses of `ks_chart4` / `ks_chart_rel` discharged by `W4_table`, `W8_table`, `W8rel`, `W8_eight`);
* **`ThetaData.theta_chart_cover`**: every `θ z` has `X₀ ≠ 0`, `X₄ ≠ 0` or `X₈ ≠ 0` (`onQ_quad`, `quadA_cover`).
-/

open Finset

noncomputable section

namespace LSG.JacAn

open LSG.Aux

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

lemma sz_ratTable {num : ℤ} {den H : ℕ} (hden : 0 < den) (hb : |num| ≤ H) :
    Sz ι ((H : ℝ) / den) den ((num : ℂ) / den) := by
  have h := (Sz.intCast (ι := ι) num).div_nat (n := den) hden.ne'
  rw [one_mul] at h
  refine h.mono_le ?_
  have hb' : |(num : ℝ)| ≤ (H : ℝ) := by
    rw [← Int.cast_abs]; exact_mod_cast hb
  exact div_le_div_of_nonneg_right hb' (by positivity)

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

lemma A1Facts.W8_smul (A : A1Facts) (j : Fin 2) (a : ℂ) (X : P9) : A.W8 j (a • X) = a ^ 2 • A.W8 j X := by
  funext l
  simp only [A.W8_table, Pi.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun b _ => sum_congr rfl fun c _ => by ring

/-- **Chart `X₄ = 1`** from the `W4` table. -/
theorem ThetaData.ks_chart4F {z₀ c : Fin 2 → ℂ} (hz : D.theta z₀ 4 ≠ 0) {Hc : ℝ} {dc : ℕ}
    (hc : ∀ j, Sz ι Hc dc (c j)) {A' B : ℝ} {E : ℕ} (h0 : ∀ l, Sz ι A' E (normalize 4 (D.theta z₀) l))
    (hA : 1 ≤ A') (hB1 : 1 ≤ B) (hB : 81 * (2 * Hc * ((A.W4H : ℝ) / A.W4den)) * A' ≤ B) :
    ∀ l, KS ι A' B E (dc * A.W4den * E) (fun s => normalize 4 (D.theta (z₀ + s • c)) l) :=
  D.ks_chart4 (fun j l a b => (A.W4num j l a b : ℂ) / A.W4den) A.W4_table
    (fun j l a b => sz_ratTable A.W4den_pos (A.W4num_bound j l a b)) hz hc h0 hA hB1 (by linarith)

/-- **Chart `X₈ = 1`** from the `W8` data. -/
theorem ThetaData.ks_chart8 {z₀ c : Fin 2 → ℂ} (hz : D.theta z₀ 8 ≠ 0) {Hc : ℝ} {dc : ℕ}
    (hc : ∀ j, Sz ι Hc dc (c j)) {A' B : ℝ} {E : ℕ} (h0 : ∀ l, Sz ι A' E (normalize 8 (D.theta z₀) l))
    (hA : 1 ≤ A') (hB1 : 1 ≤ B) (hB : 81 * (2 * Hc * ((A.W8H : ℝ) / A.W8den)) * A' ≤ B) :
    ∀ l, KS ι A' B E (dc * A.W8den * E) (fun s => normalize 8 (D.theta (z₀ + s • c)) l) :=
  D.ks_chart_rel A.W8 A.W8_smul 8 (fun j l a b => (A.W8num j l a b : ℂ) / A.W8den) A.W8_table A.W8rel
    A.W8_eight (fun j l a b => sz_ratTable A.W8den_pos (A.W8num_bound j l a b)) hz hc h0 hA hB1
    (by linarith)

/-- **The charts `X₀`, `X₄`, `X₈` cover `E(ℂ²)`.** -/
theorem ThetaData.theta_chart_cover (z : Fin 2 → ℂ) :
    D.theta z 0 ≠ 0 ∨ D.theta z 4 ≠ 0 ∨ D.theta z 8 ≠ 0 :=
  quadA_cover (A.onQ_quad _ (D.theta_onQ z)) (D.theta_ne_zero z)

end LSG.JacAn
