/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LemmaUBounds
import LSG.AuxFun.LemmaU

/-!
# Lemma U: the parameter bookkeeping (Stage 3, D3b)

**`lemmaU_arith`**: from the budget inequality
`c₀ (B + log(L+1) + (A₀+1) log(S+1) + (A₁+1) S + (D+1) S² + (T+1) log(T+2)) ≤ U`
(with the explicit `c₀ = 2 + Y + κ₁ + κ₂ + κ₃ + κ₄ + 2 deg`) follows the Liouville inequality `hQ` of
`lemmaU_dir`. Every factor is bounded by `exp` of a multiple of one budget term.
-/

open Finset

noncomputable section

namespace LSG.Aux

variable {d0 d1 m : ℕ}

lemma le_exp_sq {x c S : ℝ} (hx : 0 < x) (hc : Real.log x ≤ c) (hc0 : 0 ≤ c) (hS : 1 ≤ S) :
    x ≤ Real.exp (c * S ^ 2) :=
  (le_exp_of_log_le hx hc).trans (Real.exp_le_exp.mpr (le_mul_of_one_le_right hc0 (by nlinarith)))

lemma mul_le_exp {x y a b : ℝ} (hy0 : 0 ≤ y) (hx : x ≤ Real.exp a) (hy : y ≤ Real.exp b) :
    x * y ≤ Real.exp (a + b) := by
  rw [Real.exp_add]; exact mul_le_mul hx hy hy0 (Real.exp_pos a).le

lemma exp_le_of_le {a b : ℝ} {x : ℝ} (hx : x ≤ Real.exp a) (h : a ≤ b) : x ≤ Real.exp b :=
  hx.trans (Real.exp_le_exp.mpr h)

lemma natCast_pow_eq_exp {x : ℝ} (hx : 0 < x) (n : ℕ) : x ^ n = Real.exp (n * Real.log x) := by
  rw [← Real.exp_log hx, ← Real.exp_nat_mul, Real.exp_log hx]

set_option maxHeartbeats 1000000 in
/-- **The bookkeeping of Lemma U.** -/
theorem lemmaU_arith {deg μ τ D A₀ A₁ L S T k d l dX : ℕ}
    {H Cl C'l Mξ Aa cc Y Wn ρ₁ B U nv : ℝ} (hS : 1 ≤ S) (hk : k < T) (hH : 1 ≤ H) (hd : 1 ≤ d)
    (hCl : 1 ≤ Cl) (hC'l : 1 ≤ C'l) (hMξ : 1 ≤ Mξ) (hAa : 0 ≤ Aa) (hcc : 0 ≤ cc) (hY : 0 ≤ Y)
    (hWn : 0 ≤ Wn) (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ ≤ 1) (hl : 1 ≤ l) (hB : 0 ≤ B) (hdX1 : 1 ≤ dX)
    (hdX : (dX : ℝ) ≤ Real.exp (Aa * S ^ 2)) (hnv0 : 0 ≤ nv) (hnv : nv ≤ T * Wn)
    (hbud : (2 + Y +
        (m * (Real.log C'l + 2 * (Real.log Cl + 2 * Aa + 2 * Real.log H) + 2 * Real.log Mξ +
            cc * (1 + Y) ^ 2) +
          deg * (3 * m * (36 * Real.log l + 4 * Aa + 6 * Real.log d) +
            3 * m * (1 + (Real.log 144 + Real.log Cl +
              2 * (Real.log Cl + 2 * Aa + 2 * Real.log H) + 2 * Real.log H)))) +
        deg * (d0 * Real.log d / Real.log 2 + d0 +
          d0 * (1 + Real.log ((μ + 1) * H) / Real.log 2)) +
        deg * (d1 * μ * Real.log d + d1 + d1 * μ * Real.log H) +
        ((1 + Real.log ((1 + Wn) / ρ₁) / Real.log 2) +
          deg * (2 * Real.log d / Real.log 2 + 1 +
            (1 + Real.log (4 * (1 + 7 * τ * H ^ 2)) / Real.log 2))) + 2 * deg) *
      (B + Real.log (L + 1) + (A₀ + 1) * Real.log (S + 1) + (A₁ + 1) * S + (D + 1) * S ^ 2 +
        (T + 1) * Real.log (T + 2)) ≤ U) :
    (C'l * (Cl * Real.exp (Aa * S ^ 2) ^ 2 * H ^ 2) ^ 2 * Mξ ^ 2 *
        Real.exp (cc * (1 + S * Y) ^ 2)) ^ (m * D) * Real.exp (-U) / (ρ₁ / (1 + nv)) ^ k *
      ((((∏ f, efac (d0 := d0) (d1 := d1) (m := m) d (d ^ (μ * S)) l (l ^ 12 * dX ^ 2 * d ^ 2) f ^
        Nfac A₀ A₁ D f) * (d ^ 2) ^ k * k.factorial : ℕ) : ℝ) *
        (((L : ℝ) + 1) * Real.exp B * (2 ^ (∑ f : Fct d0 d1 m, Nfac A₀ A₁ D f) *
          ∏ f, Afac (d0 := d0) (d1 := d1) (m := m) (S * (μ + 1) * H) (H ^ (μ * S)) Cl
            (Cl * Real.exp (Aa * S ^ 2) ^ 2 * H ^ 2) H f ^ Nfac A₀ A₁ D f) *
          (2 * (2 * (1 + 7 * (T * τ * H) * H))) ^ k)) ^ deg < 1 := by
  -- basic facts
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hS2 : (1 : ℝ) ≤ (S : ℝ) ^ 2 := one_le_pow₀ hSR
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith only [this]
  have hlS : Real.log 2 ≤ Real.log (S + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hlT : Real.log 2 ≤ Real.log (T + 2) :=
    Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  have hlogH := Real.log_nonneg hH
  have hlogd := Real.log_nonneg hdR
  have hlogl := Real.log_nonneg hlR
  have hlogCl := Real.log_nonneg hCl
  have hlogC'l := Real.log_nonneg hC'l
  have hlogMξ := Real.log_nonneg hMξ
  have hkT : (k : ℝ) ≤ T := by exact_mod_cast hk.le
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  set P1 : ℝ := (D + 1) * S ^ 2 with hP1
  set P2 : ℝ := (A₀ + 1) * Real.log (S + 1) with hP2
  set P3 : ℝ := (A₁ + 1) * S with hP3
  set P4 : ℝ := (T + 1) * Real.log (T + 2) with hP4
  have hA₀0 : (0 : ℝ) ≤ A₀ := Nat.cast_nonneg A₀
  have hA₁0 : (0 : ℝ) ≤ A₁ := Nat.cast_nonneg A₁
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hA₀ : (A₀ : ℝ) * Real.log 2 ≤ P2 :=
    mul_le_mul (by linarith only) hlS hlog2.le (by linarith only [hA₀0])
  have hA₁S : (A₁ : ℝ) * S ≤ P3 :=
    mul_le_mul_of_nonneg_right (by linarith only) (by linarith only [hSR])
  have hA₁ : (A₁ : ℝ) ≤ P3 := by
    have : (A₁ : ℝ) ≤ A₁ * S := le_mul_of_one_le_right hA₁0 hSR
    linarith only [this, hA₁S]
  have hDS : (D : ℝ) * S ^ 2 ≤ P1 :=
    mul_le_mul_of_nonneg_right (by linarith only) (by positivity)
  have hTl : (T : ℝ) * Real.log 2 ≤ P4 :=
    mul_le_mul (by linarith only) hlT hlog2.le (by linarith only [hT0])
  have hP4' : Real.log 2 ≤ P4 := by
    have : 1 * Real.log 2 ≤ P4 := mul_le_mul (by linarith only [hT0]) hlT hlog2.le
      (by linarith only [hT0])
    linarith only [this]
  -- Step A: `M_R ≤ exp (KR S²)`
  set KX : ℝ := Real.log Cl + 2 * Aa + 2 * Real.log H with hKX
  set KR : ℝ := Real.log C'l + 2 * KX + 2 * Real.log Mξ + cc * (1 + Y) ^ 2 with hKR
  have hHX' : Cl * Real.exp (Aa * S ^ 2) ^ 2 * H ^ 2 ≤ Real.exp (KX * S ^ 2) := by
    have h1 : Cl ≤ Real.exp (Real.log Cl * S ^ 2) := le_exp_sq (by linarith) le_rfl hlogCl hSR
    have h2 : Real.exp (Aa * S ^ 2) ^ 2 = Real.exp (2 * Aa * S ^ 2) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have h3 : H ^ 2 ≤ Real.exp (2 * Real.log H * S ^ 2) :=
      le_exp_sq (by positivity) (by rw [Real.log_pow]; push_cast; ring_nf; rfl) (by positivity) hSR
    calc Cl * Real.exp (Aa * S ^ 2) ^ 2 * H ^ 2
        ≤ Real.exp (Real.log Cl * S ^ 2 + 2 * Aa * S ^ 2 + 2 * Real.log H * S ^ 2) := by
          rw [h2]
          refine mul_le_exp (by positivity) (mul_le_exp (by positivity) h1 le_rfl) h3
      _ = Real.exp (KX * S ^ 2) := by rw [hKX]; ring_nf
  set HX' := Cl * Real.exp (Aa * S ^ 2) ^ 2 * H ^ 2 with hHX'def
  have hHX'1 : 1 ≤ HX' := by
    rw [hHX'def]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCl
      (one_le_pow₀ (Real.one_le_exp (by positivity)))) (one_le_pow₀ hH)
  have hMR : C'l * HX' ^ 2 * Mξ ^ 2 * Real.exp (cc * (1 + S * Y) ^ 2) ≤ Real.exp (KR * S ^ 2) := by
    have h1 : C'l ≤ Real.exp (Real.log C'l * S ^ 2) := le_exp_sq (by linarith) le_rfl hlogC'l hSR
    have h2 : HX' ^ 2 ≤ Real.exp (2 * KX * S ^ 2) := by
      calc HX' ^ 2 ≤ Real.exp (KX * S ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hHX' 2
        _ = _ := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have h3 : Mξ ^ 2 ≤ Real.exp (2 * Real.log Mξ * S ^ 2) :=
      le_exp_sq (by positivity) (by rw [Real.log_pow]; push_cast; ring_nf; rfl) (by positivity) hSR
    have h4 : Real.exp (cc * (1 + S * Y) ^ 2) ≤ Real.exp (cc * (1 + Y) ^ 2 * S ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have : (1 + S * Y) ^ 2 ≤ (1 + Y) ^ 2 * S ^ 2 := by
        have : 1 + S * Y ≤ (1 + Y) * S := by nlinarith only [hSR, hY]
        have h0 : 0 ≤ 1 + S * Y := by nlinarith only [hSR, hY]
        calc (1 + S * Y) ^ 2 ≤ ((1 + Y) * S) ^ 2 := pow_le_pow_left₀ h0 this 2
          _ = (1 + Y) ^ 2 * S ^ 2 := by ring
      calc cc * (1 + S * Y) ^ 2 ≤ cc * ((1 + Y) ^ 2 * S ^ 2) := mul_le_mul_of_nonneg_left this hcc
        _ = cc * (1 + Y) ^ 2 * S ^ 2 := by ring
    calc C'l * HX' ^ 2 * Mξ ^ 2 * Real.exp (cc * (1 + S * Y) ^ 2)
        ≤ Real.exp (Real.log C'l * S ^ 2 + 2 * KX * S ^ 2 + 2 * Real.log Mξ * S ^ 2 +
            cc * (1 + Y) ^ 2 * S ^ 2) :=
          mul_le_exp (by positivity) (mul_le_exp (by positivity)
            (mul_le_exp (by positivity) h1 h2) h3) h4
      _ = Real.exp (KR * S ^ 2) := by rw [hKR]; ring_nf
  have hKX0 : 0 ≤ KX := by positivity
  have hKR0 : 0 ≤ KR := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hd00 : (0 : ℝ) ≤ d0 := Nat.cast_nonneg d0
  have hd10 : (0 : ℝ) ≤ d1 := Nat.cast_nonneg d1
  have hμ0 : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ
  have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
  have hdeg0 : (0 : ℝ) ≤ deg := Nat.cast_nonneg deg
  -- `a₁`
  have hA1 : (C'l * HX' ^ 2 * Mξ ^ 2 * Real.exp (cc * (1 + S * Y) ^ 2)) ^ (m * D) ≤
      Real.exp (m * KR * P1) := by
    refine (pow_le_pow_left₀ (by positivity) hMR _).trans ?_
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    have : (D : ℝ) * (KR * S ^ 2) ≤ KR * P1 := by
      have := mul_le_mul_of_nonneg_left hDS hKR0; linarith only [this]
    have := mul_le_mul_of_nonneg_left this hm0
    linarith only [this]
  -- Step B: the radius
  set cρ : ℝ := (1 + Wn) / ρ₁ with hcρ
  have hcρ1 : 1 ≤ cρ := by rw [hcρ, le_div_iff₀ hρ₁]; linarith only [hρ₁1, hWn]
  set Kρ : ℝ := 1 + Real.log cρ / Real.log 2 with hKρ
  have hA2 : (1 / (ρ₁ / (1 + nv))) ^ k ≤ Real.exp (Kρ * P4) := by
    have h1 : 1 / (ρ₁ / (1 + nv)) ≤ cρ * (T + 1) := by
      rw [one_div_div, hcρ, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hρ₁]
      nlinarith only [hnv, hWn, hT0, hnv0]
    calc (1 / (ρ₁ / (1 + nv))) ^ k ≤ (cρ * (T + 1)) ^ k :=
          pow_le_pow_left₀ (by positivity) h1 k
      _ ≤ Real.exp (Kρ * P4) := natPow_le_exp hcρ1 k T hk.le
  -- Step C: denominators
  set KeE : ℝ := 36 * Real.log l + 4 * Aa + 6 * Real.log d with hKeE
  have hKeE0 : 0 ≤ KeE := by positivity
  have hpow_d : ∀ n : ℕ, (d : ℝ) ^ n = Real.exp (n * Real.log d) := fun n =>
    natCast_pow_eq_exp (by positivity) n
  have hC1 : ((d : ℝ)) ^ (d0 * A₀) ≤ Real.exp ((d0 * Real.log d / Real.log 2) * P2) := by
    rw [hpow_d]; refine Real.exp_le_exp.mpr ?_; push_cast
    have e : (d0 : ℝ) * A₀ * Real.log d = (d0 * Real.log d / Real.log 2) * (A₀ * Real.log 2) := by
      field_simp
    rw [e]; exact mul_le_mul_of_nonneg_left hA₀ (by positivity)
  have hC2 : ((d : ℝ) ^ (μ * S)) ^ (d1 * A₁) ≤ Real.exp (d1 * μ * Real.log d * P3) := by
    rw [← pow_mul, hpow_d]; refine Real.exp_le_exp.mpr ?_; push_cast
    have e : (μ : ℝ) * S * (d1 * A₁) * Real.log d = (d1 * μ * Real.log d) * (A₁ * S) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left hA₁S (by positivity)
  have heE : ((eE l (l ^ 12 * dX ^ 2 * d ^ 2) d : ℕ) : ℝ) ≤ Real.exp (KeE * S ^ 2) := by
    simp only [eE]; push_cast
    have e : (l : ℝ) ^ 12 * ((l : ℝ) ^ 12 * (dX : ℝ) ^ 2 * (d : ℝ) ^ 2) ^ 2 * 1 *
        ((d : ℝ) * d) = (l : ℝ) ^ 36 * ((dX : ℝ) ^ 4 * (d : ℝ) ^ 6) := by ring
    rw [e]
    have h1 : (l : ℝ) ^ 36 ≤ Real.exp (36 * Real.log l * S ^ 2) :=
      le_exp_sq (by positivity) (by rw [Real.log_pow]; push_cast; ring_nf; rfl) (by positivity) hSR
    have h2 : (dX : ℝ) ^ 4 ≤ Real.exp (4 * Aa * S ^ 2) := by
      calc (dX : ℝ) ^ 4 ≤ Real.exp (Aa * S ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) hdX 4
        _ = _ := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have h3 : (d : ℝ) ^ 6 ≤ Real.exp (6 * Real.log d * S ^ 2) :=
      le_exp_sq (by positivity) (by rw [Real.log_pow]; push_cast; ring_nf; rfl) (by positivity) hSR
    calc (l : ℝ) ^ 36 * ((dX : ℝ) ^ 4 * (d : ℝ) ^ 6)
        ≤ Real.exp (36 * Real.log l * S ^ 2 + (4 * Aa * S ^ 2 + 6 * Real.log d * S ^ 2)) :=
          mul_le_exp (by positivity) h1 (mul_le_exp (by positivity) h2 h3)
      _ = Real.exp (KeE * S ^ 2) := by rw [hKeE]; ring_nf
  have hC3 : ((eE l (l ^ 12 * dX ^ 2 * d ^ 2) d : ℕ) : ℝ) ^ (m * 3 * D) ≤
      Real.exp (3 * m * KeE * P1) := by
    refine (pow_le_pow_left₀ (by positivity) heE _).trans ?_
    rw [← Real.exp_nat_mul]; refine Real.exp_le_exp.mpr ?_; push_cast
    have := mul_le_mul_of_nonneg_left hDS (by positivity : (0 : ℝ) ≤ 3 * m * KeE)
    linarith only [this]
  have hE : ((∏ f, efac (d0 := d0) (d1 := d1) (m := m) d (d ^ (μ * S)) l
      (l ^ 12 * dX ^ 2 * d ^ 2) f ^ Nfac A₀ A₁ D f : ℕ) : ℝ) ≤
        Real.exp ((d0 * Real.log d / Real.log 2) * P2 + d1 * μ * Real.log d * P3 +
          3 * m * KeE * P1) := by
    rw [prod_efac_pow]; push_cast
    exact mul_le_exp (by positivity) (mul_le_exp (by positivity) hC1 hC2) hC3
  -- Step D, E
  have hD' : ((d : ℝ) ^ 2) ^ k ≤ Real.exp ((2 * Real.log d / Real.log 2) * P4) := by
    rw [← pow_mul, hpow_d]; refine Real.exp_le_exp.mpr ?_; push_cast
    have e1 : (2 : ℝ) * k * Real.log d ≤ 2 * T * Real.log d := by
      have := mul_le_mul_of_nonneg_right hkT hlogd; linarith only [this]
    have e2 : (2 : ℝ) * T * Real.log d = (2 * Real.log d / Real.log 2) * (T * Real.log 2) := by
      field_simp
    have e3 := mul_le_mul_of_nonneg_left hTl
      (by positivity : (0 : ℝ) ≤ 2 * Real.log d / Real.log 2)
    linarith only [e1, e2, e3]
  have hE' : (k.factorial : ℝ) ≤ Real.exp P4 := factorial_le_exp k T hk.le
  -- Step F
  set Ka : ℝ := 1 + Real.log ((μ + 1) * H) / Real.log 2 with hKa
  set KAE : ℝ := Real.log 144 + Real.log Cl + 2 * KX + 2 * Real.log H with hKAE
  have hμH : (1 : ℝ) ≤ (μ + 1) * H :=
    one_le_mul_of_one_le_of_one_le (by linarith only [hμ0]) hH
  have hKa0 : 0 ≤ Ka := by have := Real.log_nonneg hμH; positivity
  have hKAE0 : 0 ≤ KAE := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 144 by norm_num); positivity
  have hF1 : (2 : ℝ) ^ (d0 * A₀ + d1 * A₁ + m * 3 * D) ≤
      Real.exp (d0 * P2 + d1 * P3 + 3 * m * P1) := by
    rw [natCast_pow_eq_exp (by norm_num : (0 : ℝ) < 2)]; refine Real.exp_le_exp.mpr ?_
    push_cast
    have e1 := mul_le_mul_of_nonneg_left hA₀ hd00
    have e2 : (A₁ : ℝ) * Real.log 2 ≤ P3 := by
      have := mul_le_mul_of_nonneg_left hlog2le hA₁0; linarith only [this, hA₁]
    have e2' := mul_le_mul_of_nonneg_left e2 hd10
    have e3 : (D : ℝ) * Real.log 2 ≤ P1 := by
      have h1 := mul_le_mul_of_nonneg_left hlog2le hD0
      have h2 : (D : ℝ) ≤ D * S ^ 2 := le_mul_of_one_le_right hD0 hS2
      linarith only [h1, h2, hDS]
    have e3' := mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℝ) ≤ 3 * m)
    nlinarith only [e1, e2', e3']
  have hF2 : (S * (μ + 1) * H : ℝ) ^ (d0 * A₀) ≤ Real.exp (d0 * Ka * P2) := by
    have hlog : Real.log ((S : ℝ) * ((μ + 1) * H)) ≤ Ka * Real.log (S + 1) :=
      log_mul_le_log_succ hSR hμH
    rw [show (S * (μ + 1) * H : ℝ) = S * ((μ + 1) * H) by ring]
    refine (pow_le_exp_of_log_le (by positivity) hlog _).trans (Real.exp_le_exp.mpr ?_)
    push_cast
    have : (A₀ : ℝ) * Real.log (S + 1) ≤ P2 :=
      mul_le_mul_of_nonneg_right (by linarith only) (by linarith only [hlS, hlog2])
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ d0 * Ka)
    linarith only [this]
  have hF3 : ((H : ℝ) ^ (μ * S)) ^ (d1 * A₁) ≤ Real.exp (d1 * μ * Real.log H * P3) := by
    rw [← pow_mul, natCast_pow_eq_exp (by linarith only [hH])]
    refine Real.exp_le_exp.mpr ?_; push_cast
    have e : (μ : ℝ) * S * (d1 * A₁) * Real.log H = (d1 * μ * Real.log H) * (A₁ * S) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left hA₁S (by positivity)
  have hAE : AE Cl HX' H ≤ Real.exp (KAE * S ^ 2) := by
    unfold AE
    have h0 : (144 : ℝ) ≤ Real.exp (Real.log 144 * S ^ 2) :=
      le_exp_sq (by norm_num) le_rfl (Real.log_nonneg (by norm_num)) hSR
    have h1 : Cl ≤ Real.exp (Real.log Cl * S ^ 2) := le_exp_sq (by linarith) le_rfl hlogCl hSR
    have h2 : HX' ^ 2 ≤ Real.exp (2 * KX * S ^ 2) := by
      calc HX' ^ 2 ≤ Real.exp (KX * S ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hHX' 2
        _ = _ := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have h3 : H ^ 2 ≤ Real.exp (2 * Real.log H * S ^ 2) :=
      le_exp_sq (by positivity) (by rw [Real.log_pow]; push_cast; ring_nf; rfl) (by positivity) hSR
    calc 24 * (6 * Cl * HX' ^ 2) * H ^ 2 = 144 * Cl * HX' ^ 2 * H ^ 2 := by ring
      _ ≤ Real.exp (Real.log 144 * S ^ 2 + Real.log Cl * S ^ 2 + 2 * KX * S ^ 2 +
            2 * Real.log H * S ^ 2) :=
          mul_le_exp (by positivity) (mul_le_exp (by positivity)
            (mul_le_exp (by positivity) h0 h1) h2) h3
      _ = Real.exp (KAE * S ^ 2) := by rw [hKAE]; ring_nf
  have hF4 : AE Cl HX' H ^ (m * 3 * D) ≤ Real.exp (3 * m * KAE * P1) := by
    refine (pow_le_pow_left₀ (by unfold AE; positivity) hAE _).trans ?_
    rw [← Real.exp_nat_mul]; refine Real.exp_le_exp.mpr ?_; push_cast
    have := mul_le_mul_of_nonneg_left hDS (by positivity : (0 : ℝ) ≤ 3 * m * KAE)
    linarith only [this]
  have hL1 : ((L : ℝ) + 1) = Real.exp (Real.log (L + 1)) :=
    (Real.exp_log (by positivity)).symm
  have hF : ((L : ℝ) + 1) * Real.exp B * (2 ^ (∑ f : Fct d0 d1 m, Nfac A₀ A₁ D f) *
      ∏ f, Afac (d0 := d0) (d1 := d1) (m := m) (S * (μ + 1) * H) (H ^ (μ * S)) Cl HX' H f ^
        Nfac A₀ A₁ D f) ≤ Real.exp (Real.log (L + 1) + B + (d0 * P2 + d1 * P3 + 3 * m * P1) +
          d0 * Ka * P2 + d1 * μ * Real.log H * P3 + 3 * m * KAE * P1) := by
    rw [sum_Nfac, prod_Afac_pow, hL1]
    have hA : 0 ≤ AE Cl HX' H := by unfold AE; positivity
    calc Real.exp (Real.log (L + 1)) * Real.exp B * (2 ^ (d0 * A₀ + d1 * A₁ + m * 3 * D) *
          ((S * (μ + 1) * H) ^ (d0 * A₀) * (H ^ (μ * S)) ^ (d1 * A₁) * AE Cl HX' H ^ (m * 3 * D)))
        ≤ Real.exp (Real.log (L + 1) + B) * Real.exp ((d0 * P2 + d1 * P3 + 3 * m * P1) +
            (d0 * Ka * P2 + d1 * μ * Real.log H * P3 + 3 * m * KAE * P1)) := by
          rw [← Real.exp_add]
          refine mul_le_mul_of_nonneg_left (mul_le_exp (by positivity) hF1
            (mul_le_exp (by positivity) (mul_le_exp (by positivity) hF2 hF3) hF4)) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; simp only [Real.log_exp]; push_cast; ring
  -- Step G
  set KB : ℝ := 1 + Real.log (4 * (1 + 7 * τ * H ^ 2)) / Real.log 2 with hKB
  have hc4 : (1 : ℝ) ≤ 4 * (1 + 7 * τ * H ^ 2) := by
    have : 0 ≤ 7 * (τ : ℝ) * H ^ 2 := by positivity
    linarith only [this]
  have hKB0 : 0 ≤ KB := by have := Real.log_nonneg hc4; positivity
  have hG : (2 * (2 * (1 + 7 * (T * τ * H) * H)) : ℝ) ^ k ≤ Real.exp (KB * P4) := by
    have h1 : (2 * (2 * (1 + 7 * (T * τ * H) * H)) : ℝ) ≤ 4 * (1 + 7 * τ * H ^ 2) * (T + 1) := by
      have : 0 ≤ 7 * (τ : ℝ) * H ^ 2 := by positivity
      nlinarith only [this, hT0]
    exact (pow_le_pow_left₀ (by positivity) h1 k).trans (natPow_le_exp hc4 k T hk.le)
  -- assembling `Q`
  set a₃ : ℝ := ((d0 * Real.log d / Real.log 2) * P2 + d1 * μ * Real.log d * P3 +
      3 * m * KeE * P1) + (2 * Real.log d / Real.log 2) * P4 + P4 +
    (Real.log (L + 1) + B + (d0 * P2 + d1 * P3 + 3 * m * P1) + d0 * Ka * P2 +
      d1 * μ * Real.log H * P3 + 3 * m * KAE * P1) + KB * P4 with ha₃
  have hAfac0 : 0 ≤ ∏ f, Afac (d0 := d0) (d1 := d1) (m := m) (S * (μ + 1) * H) (H ^ (μ * S)) Cl
      HX' H f ^ Nfac A₀ A₁ D f := by
    refine prod_nonneg fun f _ => pow_nonneg ?_ _
    rcases f with i | i | ⟨k', c⟩
    · show (0 : ℝ) ≤ S * (μ + 1) * H; positivity
    · show (0 : ℝ) ≤ H ^ (μ * S); positivity
    · show (0 : ℝ) ≤ AE Cl HX' H; unfold AE; positivity
  have hY0' : 0 ≤ ((L : ℝ) + 1) * Real.exp B * (2 ^ (∑ f : Fct d0 d1 m, Nfac A₀ A₁ D f) *
      ∏ f, Afac (d0 := d0) (d1 := d1) (m := m) (S * (μ + 1) * H) (H ^ (μ * S)) Cl HX' H f ^
        Nfac A₀ A₁ D f) * (2 * (2 * (1 + 7 * (T * τ * H) * H))) ^ k := by positivity
  have hQ : ((((∏ f, efac (d0 := d0) (d1 := d1) (m := m) d (d ^ (μ * S)) l
        (l ^ 12 * dX ^ 2 * d ^ 2) f ^ Nfac A₀ A₁ D f) * (d ^ 2) ^ k * k.factorial : ℕ) : ℝ) *
        (((L : ℝ) + 1) * Real.exp B * (2 ^ (∑ f : Fct d0 d1 m, Nfac A₀ A₁ D f) *
          ∏ f, Afac (d0 := d0) (d1 := d1) (m := m) (S * (μ + 1) * H) (H ^ (μ * S)) Cl HX' H f ^
            Nfac A₀ A₁ D f) * (2 * (2 * (1 + 7 * (T * τ * H) * H))) ^ k)) ≤ Real.exp a₃ := by
    have hprod := mul_le_exp hY0' (mul_le_exp (by positivity) (mul_le_exp (by positivity) hE hD')
      hE') (mul_le_exp (by positivity) hF hG)
    refine le_trans (le_of_eq ?_) (hprod.trans (Real.exp_le_exp.mpr (le_of_eq ?_)))
    · push_cast; ring
    · rw [ha₃]; push_cast; ring
  -- the final inequality
  have hlL : 0 ≤ Real.log (L + 1) :=
    Real.log_nonneg (by linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
  have hP10 : 0 ≤ P1 := by positivity
  have hP20 : 0 ≤ P2 := by rw [hP2]; have := hlog2.le.trans hlS; positivity
  have hP30 : 0 ≤ P3 := by positivity
  have hKρ0 : 0 ≤ Kρ := by have := Real.log_nonneg hcρ1; positivity
  have hfin : m * KR * P1 + Kρ * P4 + deg * a₃ < U := by
    set Λ := B + Real.log (L + 1) + P2 + P3 + P1 + P4 with hΛ
    have hΛpos : 0 < Λ := by linarith only [hB, hlL, hP10, hP20, hP30, hP4', hlog2]
    set κ1 := m * KR + deg * (3 * m * KeE + 3 * m * (1 + KAE)) with hκ1d
    set κ2 := deg * (d0 * Real.log d / Real.log 2 + d0 + d0 * Ka) with hκ2d
    set κ3 := deg * (d1 * μ * Real.log d + d1 + d1 * μ * Real.log H) with hκ3d
    set κ4 := Kρ + deg * (2 * Real.log d / Real.log 2 + 1 + KB) with hκ4d
    have hκ1 : 0 ≤ κ1 := by positivity
    have hκ2 : 0 ≤ κ2 := by positivity
    have hκ3 : 0 ≤ κ3 := by positivity
    have hκ4 : 0 ≤ κ4 := by positivity
    have hid : m * KR * P1 + Kρ * P4 + deg * a₃ =
        κ1 * P1 + κ2 * P2 + κ3 * P3 + κ4 * P4 + deg * B + deg * Real.log (L + 1) := by
      rw [ha₃, hκ1d, hκ2d, hκ3d, hκ4d]; ring
    have i1 := mul_le_mul_of_nonneg_left
      (show P1 ≤ Λ by linarith only [hB, hlL, hP20, hP30, hP4', hlog2]) hκ1
    have i2 := mul_le_mul_of_nonneg_left
      (show P2 ≤ Λ by linarith only [hB, hlL, hP10, hP30, hP4', hlog2]) hκ2
    have i3 := mul_le_mul_of_nonneg_left
      (show P3 ≤ Λ by linarith only [hB, hlL, hP10, hP20, hP4', hlog2]) hκ3
    have i4 := mul_le_mul_of_nonneg_left
      (show P4 ≤ Λ by linarith only [hB, hlL, hP10, hP20, hP30]) hκ4
    have i5 := mul_le_mul_of_nonneg_left
      (show B ≤ Λ by linarith only [hlL, hP10, hP20, hP30, hP4', hlog2]) hdeg0
    have i6 := mul_le_mul_of_nonneg_left
      (show Real.log (L + 1) ≤ Λ by linarith only [hB, hP10, hP20, hP30, hP4', hlog2]) hdeg0
    have hb' : (2 + Y + κ1 + κ2 + κ3 + κ4 + 2 * deg) * Λ ≤ U := hbud
    have hY' : 0 < (2 + Y) * Λ := mul_pos (by linarith only [hY]) hΛpos
    nlinarith only [hid, i1, i2, i3, i4, i5, i6, hb', hY']
  exact small_of_bounds (mul_le_mul_of_nonneg_right hA1 (Real.exp_pos _).le) (by positivity) hA2
    (mul_nonneg (by positivity) hY0') hQ hfin

end LSG.Aux
