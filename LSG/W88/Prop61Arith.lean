/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Parameter estimates for W88 Prop. 6.1 (Stage 3, D3c)

`Δ = (C S^e (log S)^{d₀})^{1/q}` with `e ≥ 2q` (this is (NR)). For `S ≥ 3`:
* `delta_pow`: `Δ^q = C S^e (log S)^{d₀}`;
* `sq_le_delta`: `S² ≤ Δ` (`C ≥ 1`);
* `log_delta_le`: `log Δ ≤ ((e + d₀ + 1)/q) log S` (`C ≤ S`);
* `log_le_sq`, `log_succ_le_two_log`.
-/

open Real

noncomputable section

namespace LSG.W88

/-- The parameter `Δ` of W88 Prop. 6.1: `Δ^q = C S^e (log S)^{d₀}`. -/
def delta61 (C : ℝ) (e d0 q S : ℕ) : ℝ := (C * (S : ℝ) ^ e * Real.log S ^ d0) ^ (1 / (q : ℝ))

variable {C : ℝ} {e d0 q S : ℕ}

lemma log_ge_one (hS : 3 ≤ S) : 1 ≤ Real.log S := by
  have h3 : (3 : ℝ) ≤ S := by exact_mod_cast hS
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans h3

lemma delta_nonneg (hC : 0 ≤ C) : 0 ≤ delta61 C e d0 q S := by
  unfold delta61
  apply Real.rpow_nonneg
  have : 0 ≤ Real.log S := Real.log_natCast_nonneg S
  positivity

lemma delta_pow (hC : 0 ≤ C) (hq : 1 ≤ q) :
    delta61 C e d0 q S ^ q = C * (S : ℝ) ^ e * Real.log S ^ d0 := by
  unfold delta61
  have : 0 ≤ Real.log S := Real.log_natCast_nonneg S
  rw [one_div, Real.rpow_inv_natCast_pow (by positivity) (by omega)]

lemma sq_le_delta (hC : 1 ≤ C) (hq : 1 ≤ q) (he : 2 * q ≤ e) (hS : 3 ≤ S) :
    (S : ℝ) ^ 2 ≤ delta61 C e d0 q S := by
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast (by omega : 1 ≤ S)
  have hl := log_ge_one hS
  have hX : ((S : ℝ) ^ 2) ^ q ≤ delta61 C e d0 q S ^ q := by
    rw [delta_pow (by linarith) hq, ← pow_mul]
    calc (S : ℝ) ^ (2 * q) ≤ (S : ℝ) ^ e := pow_le_pow_right₀ hS1 he
      _ = 1 * (S : ℝ) ^ e * 1 := by ring
      _ ≤ C * (S : ℝ) ^ e * Real.log S ^ d0 := by
          gcongr
          exact one_le_pow₀ hl
  exact le_of_pow_le_pow_left₀ (by omega) (delta_nonneg (by linarith)) hX

lemma log_le_self' {x : ℝ} (hx : 0 < x) : Real.log x ≤ x :=
  (Real.log_le_sub_one_of_pos hx).trans (by linarith)

lemma log_delta_le (hC : 1 ≤ C) (hCS : C ≤ S) (hq : 1 ≤ q) (he : 2 * q ≤ e) (hS : 3 ≤ S) :
    Real.log (delta61 C e d0 q S) ≤ ((e + d0 + 1 : ℕ) / (q : ℝ)) * Real.log S := by
  have hS0 : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast (by omega : 1 ≤ S)
  have hD0 : 0 < delta61 C e d0 q S :=
    lt_of_lt_of_le (by positivity) (sq_le_delta hC hq he hS)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hX : delta61 C e d0 q S ^ q ≤ (S : ℝ) ^ (e + d0 + 1) := by
    rw [delta_pow (by linarith) hq, pow_add, pow_add, pow_one]
    have hl : Real.log S ^ d0 ≤ (S : ℝ) ^ d0 :=
      pow_le_pow_left₀ (Real.log_natCast_nonneg S) (log_le_self' hS0) d0
    calc C * (S : ℝ) ^ e * Real.log S ^ d0 ≤ S * (S : ℝ) ^ e * (S : ℝ) ^ d0 := by gcongr
      _ = _ := by ring
  have h1 := Real.log_le_log (by positivity) hX
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hqR]
  push_cast at h1 ⊢
  linarith

lemma log_succ_le_two_log (hS : 3 ≤ S) : Real.log ((S : ℝ) + 1) ≤ 2 * Real.log S := by
  have hS0 : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
  have h3 : (3 : ℝ) ≤ S := by exact_mod_cast hS
  rw [← Real.log_rpow hS0, Real.log_le_log_iff (by positivity) (by positivity)]
  rw [show ((S : ℝ) ^ (2 : ℝ)) = S ^ 2 by norm_cast]
  nlinarith

lemma log_le_sq (hS : 3 ≤ S) : Real.log S ≤ (S : ℝ) ^ 2 := by
  have hS0 : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
  have h3 : (3 : ℝ) ≤ S := by exact_mod_cast hS
  exact (log_le_self' hS0).trans (by nlinarith)

/-- The Siegel inequality of Prop. 6.1 (`c₂ U^{n+1} ≤ L Δ' r^κ log(R/r)^n`). -/
lemma siegel61 {n q e d0 d1 m κ : ℕ} {Δ ν S lS C c₂ x₀ x₁ x₂ : ℝ} (hΔ : 0 < Δ) (hν : 1 ≤ ν)
    (hS : 1 ≤ S) (hlS : 1 ≤ lS) (hlogν : 0 < Real.log ν) (hc₂ : 0 ≤ c₂)
    (hdq : d0 + d1 + m = n + q) (heκ : e + κ = d1 + 2 * m)
    (hΔq : Δ ^ q = C * S ^ e * lS ^ d0)
    (hx₀ : Δ / ((d0 + 1) * ν * lS) ≤ x₀) (hx₁ : Δ / ((d1 + 1) * ν * S) ≤ x₁)
    (hx₂ : Δ / (ν * S ^ 2) ≤ x₂)
    (hCK : c₂ * ν ^ (6 * (n + 1)) ≤ C * (ν ^ (2 * κ) * Real.log ν ^ n /
      (((d0 : ℝ) + 1) ^ d0 * ((d1 : ℝ) + 1) ^ d1 * ν ^ (d0 + d1 + m + 1)))) :
    c₂ * (ν ^ 6 * Δ) ^ (n + 1) ≤
      x₀ ^ d0 * x₁ ^ d1 * x₂ ^ m * (Δ / ν) * (ν ^ 2 * S) ^ κ * Real.log ν ^ n := by
  have hν0 : 0 < ν := by linarith
  have hS0 : 0 < S := by linarith
  have hlS0 : 0 < lS := by linarith
  set Kν : ℝ := ν ^ (2 * κ) * Real.log ν ^ n /
    (((d0 : ℝ) + 1) ^ d0 * ((d1 : ℝ) + 1) ^ d1 * ν ^ (d0 + d1 + m + 1)) with hKν
  have h0 : 0 ≤ Δ / ((d0 + 1) * ν * lS) := by positivity
  have h1 : 0 ≤ Δ / ((d1 + 1) * ν * S) := by positivity
  have h2 : 0 ≤ Δ / (ν * S ^ 2) := by positivity
  have hkey : Δ ^ d0 * Δ ^ d1 * Δ ^ m * Δ = Δ ^ (n + 1) * (C * S ^ e * lS ^ d0) := by
    rw [← hΔq, ← pow_add, ← pow_add, ← pow_succ, ← pow_add, hdq]; ring
  have hSpow : S ^ e * S ^ κ = S ^ d1 * (S ^ 2) ^ m := by
    rw [← pow_add, heκ, ← pow_mul, ← pow_add]
  have heq : (Δ / ((d0 + 1) * ν * lS)) ^ d0 * (Δ / ((d1 + 1) * ν * S)) ^ d1 *
      (Δ / (ν * S ^ 2)) ^ m * (Δ / ν) * (ν ^ 2 * S) ^ κ * Real.log ν ^ n =
      Δ ^ (n + 1) * (C * Kν) := by
    calc (Δ / ((d0 + 1) * ν * lS)) ^ d0 * (Δ / ((d1 + 1) * ν * S)) ^ d1 *
          (Δ / (ν * S ^ 2)) ^ m * (Δ / ν) * (ν ^ 2 * S) ^ κ * Real.log ν ^ n
        = (Δ ^ d0 * Δ ^ d1 * Δ ^ m * Δ) * (ν ^ (2 * κ) * Real.log ν ^ n) * S ^ κ /
            ((((d0 : ℝ) + 1) ^ d0 * ((d1 : ℝ) + 1) ^ d1 * ν ^ (d0 + d1 + m + 1)) * lS ^ d0 *
              S ^ d1 * (S ^ 2) ^ m) := by
          rw [div_pow, div_pow, div_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul]
          field_simp
          ring
      _ = Δ ^ (n + 1) * (C * S ^ e * lS ^ d0) * (ν ^ (2 * κ) * Real.log ν ^ n) * S ^ κ /
            ((((d0 : ℝ) + 1) ^ d0 * ((d1 : ℝ) + 1) ^ d1 * ν ^ (d0 + d1 + m + 1)) * lS ^ d0 *
              S ^ d1 * (S ^ 2) ^ m) := by rw [hkey]
      _ = Δ ^ (n + 1) * (C * Kν) * ((S ^ e * S ^ κ) / (S ^ d1 * (S ^ 2) ^ m)) := by
          rw [hKν]; field_simp
      _ = Δ ^ (n + 1) * (C * Kν) := by
          rw [hSpow, div_self (by positivity), mul_one]
  have hfin : c₂ * (ν ^ 6 * Δ) ^ (n + 1) ≤ Δ ^ (n + 1) * (C * Kν) := by
    rw [mul_pow, ← pow_mul]
    calc c₂ * (ν ^ (6 * (n + 1)) * Δ ^ (n + 1)) = (c₂ * ν ^ (6 * (n + 1))) * Δ ^ (n + 1) := by
          ring
      _ ≤ (C * Kν) * Δ ^ (n + 1) := mul_le_mul_of_nonneg_right hCK (by positivity)
      _ = Δ ^ (n + 1) * (C * Kν) := by ring
  have hx₀0 : 0 ≤ x₀ := h0.trans hx₀
  have hx₁0 : 0 ≤ x₁ := h1.trans hx₁
  have hx₂0 : 0 ≤ x₂ := h2.trans hx₂
  calc c₂ * (ν ^ 6 * Δ) ^ (n + 1) ≤ Δ ^ (n + 1) * (C * Kν) := hfin
    _ = (Δ / ((d0 + 1) * ν * lS)) ^ d0 * (Δ / ((d1 + 1) * ν * S)) ^ d1 *
          (Δ / (ν * S ^ 2)) ^ m * (Δ / ν) * (ν ^ 2 * S) ^ κ * Real.log ν ^ n := heq.symm
    _ ≤ x₀ ^ d0 * x₁ ^ d1 * x₂ ^ m * (Δ / ν) * (ν ^ 2 * S) ^ κ * Real.log ν ^ n := by
        gcongr

/-- The growth condition of Prop. 2.1 in Prop. 6.1. -/
lemma growth61 {m : ℕ} {Δ ν S lS cW lL A₀ A₁ D lR : ℝ} (hΔ : 0 ≤ Δ) (hν : 3 ≤ ν) (hS : 1 ≤ S)
    (hlS : 1 ≤ lS) (hcW : 0 ≤ cW) (hνcW : 16 * m * cW ≤ ν) (hlL : lL ≤ Δ)
    (hA₀ : A₀ ≤ Δ / (ν * lS)) (hA₀0 : 0 ≤ A₀) (hA₁ : A₁ ≤ Δ / (ν * S)) (hA₁0 : 0 ≤ A₁)
    (hD : D ≤ Δ / (ν * S ^ 2)) (hD0 : 0 ≤ D) (hlR : lR ≤ 2 * lS) (hlR0 : 0 ≤ lR) :
    lL + A₀ * lR + A₁ * (ν ^ 3 * S) + m * D * cW * (1 + ν ^ 3 * S) ^ 2 ≤ ν ^ 6 * Δ := by
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
  have e6 : Δ + Δ + ν ^ 2 * Δ ≤ 3 * (ν ^ 6 * Δ) / 4 := by
    have h9 : 9 ≤ ν ^ 2 := by nlinarith
    have : 2 + ν ^ 2 ≤ 3 * ν ^ 6 / 4 := by
      have e : ν ^ 6 = (ν ^ 2) ^ 2 * ν ^ 2 := by ring
      have hu2 : 81 ≤ (ν ^ 2) ^ 2 := by nlinarith
      have hu3 : 81 * ν ^ 2 ≤ (ν ^ 2) ^ 2 * ν ^ 2 :=
        mul_le_mul_of_nonneg_right hu2 (by positivity)
      rw [e]; linarith
    nlinarith
  linarith

/-- The budget of Lemma U in Prop. 6.1. -/
lemma budget61 {Δ ν S lS c₀ Kt lL1 lS1 A₀ A₁ D T lT : ℝ} (hΔ : 1 ≤ Δ) (hν : 1 ≤ ν)
    (hS : 3 ≤ S) (hlS : 1 ≤ lS) (hlSS : 2 * lS ≤ S ^ 2) (hSΔ : S ^ 2 ≤ Δ) (hc₀ : 0 ≤ c₀)
    (hKt : 0 ≤ Kt) (hνbud : c₀ * (9 + 3 * Kt) ≤ ν) (hlL1 : lL1 ≤ Δ)
    (hA₀ : A₀ ≤ Δ / (ν * lS)) (hlS1 : lS1 ≤ 2 * lS) (hlS10 : 0 ≤ lS1) (hA₀0 : 0 ≤ A₀)
    (hA₁ : A₁ ≤ Δ / (ν * S)) (hD : D ≤ Δ / (ν * S ^ 2)) (hT : T ≤ Δ / lS + 1) (hT0 : 0 ≤ T)
    (hlT : lT ≤ Kt * lS) (hlT0 : 0 ≤ lT) :
    c₀ * (Δ / ν + lL1 + (A₀ + 1) * lS1 + (A₁ + 1) * S + (D + 1) * S ^ 2 + (T + 1) * lT) ≤
      ν ^ 6 * Δ := by
  have hν0 : 0 < ν := by linarith
  have hS0 : 0 < S := by linarith
  have hlS0 : 0 < lS := by linarith
  have hΔ0 : 0 ≤ Δ := by linarith
  have b1 : Δ / ν ≤ Δ := div_le_self hΔ0 hν
  have b2 : (A₀ + 1) * lS1 ≤ 3 * Δ := by
    calc (A₀ + 1) * lS1 ≤ (Δ / (ν * lS) + 1) * (2 * lS) :=
          mul_le_mul (by linarith) hlS1 hlS10 (by positivity)
      _ = 2 * (Δ / ν) + 2 * lS := by field_simp
      _ ≤ 3 * Δ := by linarith
  have b3 : (A₁ + 1) * S ≤ 2 * Δ := by
    calc (A₁ + 1) * S ≤ (Δ / (ν * S) + 1) * S := mul_le_mul_of_nonneg_right (by linarith) hS0.le
      _ = Δ / ν + S := by field_simp
      _ ≤ 2 * Δ := by nlinarith
  have b4 : (D + 1) * S ^ 2 ≤ 2 * Δ := by
    calc (D + 1) * S ^ 2 ≤ (Δ / (ν * S ^ 2) + 1) * S ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = Δ / ν + S ^ 2 := by field_simp
      _ ≤ 2 * Δ := by linarith
  have b5 : (T + 1) * lT ≤ 2 * Kt * Δ := by
    calc (T + 1) * lT ≤ (Δ / lS + 2) * (Kt * lS) := mul_le_mul (by linarith) hlT hlT0 (by positivity)
      _ = Kt * Δ + Kt * (2 * lS) := by field_simp
      _ ≤ Kt * Δ + Kt * Δ := by gcongr; linarith
      _ = 2 * Kt * Δ := by ring
  have hsum : Δ / ν + lL1 + (A₀ + 1) * lS1 + (A₁ + 1) * S + (D + 1) * S ^ 2 + (T + 1) * lT ≤
      (9 + 3 * Kt) * Δ := by nlinarith
  calc c₀ * (Δ / ν + lL1 + (A₀ + 1) * lS1 + (A₁ + 1) * S + (D + 1) * S ^ 2 + (T + 1) * lT)
      ≤ c₀ * ((9 + 3 * Kt) * Δ) := mul_le_mul_of_nonneg_left hsum hc₀
    _ = (c₀ * (9 + 3 * Kt)) * Δ := by ring
    _ ≤ ν * Δ := mul_le_mul_of_nonneg_right hνbud hΔ0
    _ ≤ ν ^ 6 * Δ := by
        refine mul_le_mul_of_nonneg_right ?_ hΔ0
        calc ν = ν ^ 1 := (pow_one ν).symm
          _ ≤ ν ^ 6 := pow_le_pow_right₀ hν (by norm_num)

end LSG.W88
