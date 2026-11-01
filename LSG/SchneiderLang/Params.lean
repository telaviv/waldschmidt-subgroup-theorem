/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Schneider–Lang: the parameter inequality

With `M = m n²` equations, `L = 2 m n` (so `L² ≥ 2 m M` unknowns), any order `s ≥ M` and the
radius `R = s^{1/(2ρ)}`, the product of the analytic upper bound and the `(d-1)`-st power of the
house bound is `< 1` once `n` is large, provided `m > 4 d ρ`. All logarithmic terms are
`s log s` with total coefficient `2d - m/(2ρ) ≤ -1/(2ρ)`; everything else is `O(s)`.
-/

open Real

namespace LSG.SL

theorem pow_eq_exp_mul_log {x : ℝ} (hx : 0 < x) (k : ℕ) : x ^ k = exp (k * log x) := by
  rw [← exp_log (pow_pos hx k), log_pow]

theorem le_exp_self (x : ℝ) : x ≤ exp x := by linarith [add_one_le_exp x]

theorem sq_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ exp (2 * x) := by
  calc x ^ 2 ≤ exp x ^ 2 := pow_le_pow_left₀ hx (le_exp_self x) 2
    _ = exp (2 * x) := by rw [← exp_nat_mul]; norm_num

theorem factorial_le_exp {s : ℕ} (hs : 1 ≤ s) : (s.factorial : ℝ) ≤ exp (s * log s) := by
  have h1 : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by exact_mod_cast Nat.factorial_le_pow s
  have h2 : (0 : ℝ) < s := by exact_mod_cast hs
  rwa [pow_eq_exp_mul_log h2] at h1

/-- The radius `R = s^{1/(2ρ)}`. -/
noncomputable def Rad (ρ s : ℕ) : ℝ := exp (log s / (2 * ρ))

/-- The bound `(β (2L + kδ))^k Y^{2L + kδ}` for the values of `Dop^k (X^a Y^b)`. -/
noncomputable def Abd (β Y : ℝ) (δ L k : ℕ) : ℝ :=
  (β * (2 * (L : ℝ) + k * δ)) ^ k * Y ^ (2 * L + k * δ)

/-- Siegel's bound with `L²` unknowns. -/
noncomputable def Hbd (c : ℝ) (L : ℕ) (A : ℝ) : ℝ := c * (1 + c * ((L * L : ℕ) : ℝ) * A)

theorem one_le_Abd {β Y : ℝ} (hβ : 1 ≤ β) (hY : 1 ≤ Y) (δ L k : ℕ) (hL : 1 ≤ L) :
    1 ≤ Abd β Y δ L k := by
  unfold Abd
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : 1 ≤ β * (2 * (L : ℝ) + k * δ) := by
    have : (1 : ℝ) ≤ 2 * (L : ℝ) + k * δ := by
      have : (0 : ℝ) ≤ k * δ := by positivity
      linarith
    nlinarith
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_pow₀ hY)

theorem Abd_le {β Y : ℝ} (hβ : 1 ≤ β) (hY : 1 ≤ Y) {δ L k s : ℕ} (hL : L ≤ s) (hk : k ≤ s)
    (hs : 1 ≤ s) :
    Abd β Y δ L k ≤ exp (s * log s + s * (log (β * (2 + δ)) + (2 + δ) * log Y)) := by
  unfold Abd
  have hS : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hL' : (L : ℝ) ≤ s := by exact_mod_cast hL
  have hk' : (k : ℝ) ≤ s := by exact_mod_cast hk
  have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
  have hb1 : 1 ≤ β * (2 + δ) := by nlinarith
  set X : ℝ := β * (2 + δ) * s with hX
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le hb1 hS
  have h1 : β * (2 * (L : ℝ) + k * δ) ≤ X := by
    have : (2 * (L : ℝ) + k * δ) ≤ (2 + δ) * s := by nlinarith
    calc β * (2 * (L : ℝ) + k * δ) ≤ β * ((2 + δ) * s) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = X := by rw [hX]; ring
  have h2 : (β * (2 * (L : ℝ) + k * δ)) ^ k ≤ X ^ s :=
    (pow_le_pow_left₀ (by positivity) h1 k).trans (pow_le_pow_right₀ hX1 hk)
  have h3 : Y ^ (2 * L + k * δ) ≤ Y ^ ((2 + δ) * s) := by
    refine pow_le_pow_right₀ hY ?_
    have : k * δ ≤ s * δ := Nat.mul_le_mul_right δ hk
    nlinarith
  have h4 : X ^ s = exp (s * (log (β * (2 + δ)) + log s)) := by
    rw [pow_eq_exp_mul_log (by linarith), hX, log_mul (by positivity) (by positivity)]
  have h5 : Y ^ ((2 + δ) * s) = exp ((2 + δ) * s * log Y) := by
    rw [pow_eq_exp_mul_log (by linarith)]
    push_cast; ring_nf
  calc (β * (2 * (L : ℝ) + k * δ)) ^ k * Y ^ (2 * L + k * δ) ≤ X ^ s * Y ^ ((2 + δ) * s) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = _ := by rw [h4, h5, ← exp_add]; congr 1; ring

theorem Hbd_le {c : ℝ} (hc : 0 ≤ c) {L : ℕ} (hL : 1 ≤ L) {A : ℝ} (hA : 1 ≤ A) :
    Hbd c L A ≤ (1 + c) ^ 2 * ((L : ℝ) ^ 2 * A) := by
  unfold Hbd
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hX : 1 ≤ (L : ℝ) ^ 2 * A := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL') hA
  push_cast
  have : 1 + c * ((L : ℝ) * L) * A ≤ (1 + c) * ((L : ℝ) ^ 2 * A) := by nlinarith
  calc c * (1 + c * ((L : ℝ) * L) * A) ≤ (1 + c) * ((1 + c) * ((L : ℝ) ^ 2 * A)) :=
        mul_le_mul (by linarith) this (by positivity) (by linarith)
    _ = _ := by ring

set_option maxHeartbeats 2000000 in
/-- **The parameter inequality.** -/
theorem final_ineq {d m ρ δ d₀ : ℕ} {β Y c C r h₀ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (hm : 4 * d * ρ < m) (hd₀ : 1 ≤ d₀) (hβ : 1 ≤ β) (hY : 1 ≤ Y) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hr : 1 ≤ r) (hh₀ : 0 < h₀) (hh₀1 : h₀ ≤ 1) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n, n₀ ≤ n → ∀ L M : ℕ, L = 2 * m * n → M = m * n ^ 2 →
      ∀ s : ℕ, M ≤ s →
        2 * r ≤ Rad ρ s ∧
        (d₀ : ℝ) ^ (δ * s) * s.factorial *
            (((L * L : ℕ) : ℝ) * Hbd c L (Abd β Y δ L M) * (d₀ : ℝ) ^ (2 * L) *
              exp (C * (1 + Rad ρ s) ^ ρ) ^ (2 * L) *
              (2 * r / (Rad ρ s - r)) ^ (s * m)) / h₀ ^ (2 * L) *
          (((L * L : ℕ) : ℝ) * Hbd c L (Abd β Y δ L M) * Abd β Y δ L s) ^ (d - 1) < 1 := by
  -- constants
  set KA : ℝ := log (β * (2 + δ)) + (2 + δ) * log Y with hKA
  set a : ℝ := log (1 + c) with ha
  have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
  have hKA0 : 0 ≤ KA := by
    have : 0 ≤ log (β * (2 + δ)) := log_nonneg (by nlinarith)
    have : 0 ≤ log Y := log_nonneg hY
    positivity
  have ha0 : 0 ≤ a := log_nonneg (by linarith)
  have hd₀r : (1 : ℝ) ≤ d₀ := by exact_mod_cast hd₀
  have hld₀ : 0 ≤ log (d₀ : ℝ) := log_nonneg hd₀r
  have hlr : 0 ≤ log (4 * r) := log_nonneg (by linarith)
  have hlh : 0 ≤ log (1 / h₀) := log_nonneg (by rw [le_div_iff₀ hh₀]; linarith)
  have hρr : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  set K : ℝ := δ * log d₀ + 4 + KA + 2 * log d₀ + 2 ^ (ρ + 2) * C * m + m * log (4 * r) +
    2 * log (1 / h₀) + 2 * a + ((d : ℝ) - 1) * (4 + 2 * a + 2 * KA) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ((d : ℝ) - 1) * (4 + 2 * a + 2 * KA) := mul_nonneg (by linarith) (by positivity)
    positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 + exp (2 * ρ * K) + exp (2 * ρ * log (2 * r)))
  refine ⟨n₀, ?_, ?_⟩
  · have : (2 : ℝ) < n₀ := by linarith [exp_pos (2 * ρ * K), exp_pos (2 * ρ * log (2 * r))]
    exact_mod_cast this.le
  intro n hn L M hL hM s hs
  -- basic facts
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : 1 ≤ m := by
    have : 0 < 4 * d * ρ := by positivity
    omega
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) < n := by linarith [exp_pos (2 * ρ * K), exp_pos (2 * ρ * log (2 * r))]
    exact_mod_cast this.le
  have hns : n ≤ s := by
    have : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
    have : n ^ 2 ≤ m * n ^ 2 := Nat.le_mul_of_pos_left _ hm1
    omega
  have hMs : M ≤ s := hs
  have hLs : L ≤ s := by
    have : 2 * n ≤ n ^ 2 := by nlinarith
    have : L ≤ M := by rw [hL, hM]; nlinarith
    omega
  have hL1 : 1 ≤ L := by rw [hL]; nlinarith
  have hs1 : 1 ≤ s := le_trans (by omega) hns
  set S : ℝ := (s : ℝ) with hSdef
  have hS1 : (1 : ℝ) ≤ S := by rw [hSdef]; exact_mod_cast hs1
  have hS0 : (0 : ℝ) < S := by linarith
  set ℓ : ℝ := log S with hℓ
  have hℓ0 : 0 ≤ ℓ := log_nonneg hS1
  have hLS : (L : ℝ) ≤ S := by rw [hSdef]; exact_mod_cast hLs
  have hnS : (n₀ : ℝ) ≤ S := hn'.trans (by rw [hSdef]; exact_mod_cast hns)
  have hℓK : 2 * ρ * K < ℓ := by
    have h1 : exp (2 * ρ * K) < S := by
      linarith [exp_pos (2 * ρ * log (2 * r))]
    have := log_lt_log (exp_pos _) h1
    rwa [log_exp] at this
  have hℓr : 2 * ρ * log (2 * r) ≤ ℓ := by
    have h1 : exp (2 * ρ * log (2 * r)) ≤ S := by
      linarith [exp_pos (2 * ρ * K)]
    have := log_le_log (exp_pos _) h1
    rwa [log_exp] at this
  -- the radius
  set R : ℝ := Rad ρ s with hRdef
  have hR : R = exp (ℓ / (2 * ρ)) := rfl
  have hlogR : log R = ℓ / (2 * ρ) := by rw [hR, log_exp]
  have h2r : 2 * r ≤ R := by
    have : log (2 * r) ≤ ℓ / (2 * ρ) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc 2 * r = exp (log (2 * r)) := (exp_log (by linarith)).symm
      _ ≤ R := by rw [hR]; exact exp_le_exp.mpr this
  refine ⟨h2r, ?_⟩
  have hR1 : 1 ≤ R := by linarith
  have hRpow : R ^ ρ = exp (ℓ / 2) := by
    rw [hR, ← exp_nat_mul]; congr 1; field_simp
  have hsq : exp (ℓ / 2) ^ 2 = S := by
    rw [← exp_nat_mul]; push_cast
    rw [show (2 : ℝ) * (ℓ / 2) = ℓ by ring, hℓ, exp_log hS0]
  have hnE : (n : ℝ) ≤ exp (ℓ / 2) := by
    have h1 : (n : ℝ) ^ 2 ≤ exp (ℓ / 2) ^ 2 := by
      rw [hsq, hSdef]
      have : n ^ 2 ≤ s := le_trans (Nat.le_mul_of_pos_left _ hm1) (hM ▸ hMs)
      exact_mod_cast this
    exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (exp_pos _).le two_ne_zero).mp h1
  -- B1 .. B10
  have B1 : (d₀ : ℝ) ^ (δ * s) = exp (δ * S * log d₀) := by
    rw [pow_eq_exp_mul_log (by linarith), hSdef]; push_cast; ring_nf
  have B2 : (s.factorial : ℝ) ≤ exp (S * ℓ) := factorial_le_exp hs1
  have B3 : ((L * L : ℕ) : ℝ) ≤ exp (2 * S) := by
    push_cast
    calc (L : ℝ) * L = (L : ℝ) ^ 2 := by ring
      _ ≤ exp (2 * L) := sq_le_exp (Nat.cast_nonneg _)
      _ ≤ exp (2 * S) := exp_le_exp.mpr (by linarith)
  have hA1 : 1 ≤ Abd β Y δ L M := one_le_Abd hβ hY δ L M hL1
  have B4 : Abd β Y δ L M ≤ exp (S * ℓ + S * KA) := Abd_le hβ hY hLs hMs hs1
  have B10 : Abd β Y δ L s ≤ exp (S * ℓ + S * KA) := Abd_le hβ hY hLs le_rfl hs1
  have hH0 : 0 ≤ Hbd c L (Abd β Y δ L M) := by unfold Hbd; positivity
  have B5 : Hbd c L (Abd β Y δ L M) ≤ exp (2 * a + 2 * S + (S * ℓ + S * KA)) := by
    refine (Hbd_le hc hL1 hA1).trans ?_
    have e1 : (1 + c) ^ 2 = exp (2 * a) := by
      rw [pow_eq_exp_mul_log (by linarith)]; push_cast; rfl
    have e2 : (L : ℝ) ^ 2 ≤ exp (2 * S) :=
      (sq_le_exp (Nat.cast_nonneg _)).trans (exp_le_exp.mpr (by linarith))
    rw [e1, exp_add, exp_add, mul_assoc (exp (2 * a))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul e2 B4 (by linarith) (exp_pos _).le)
      (exp_pos _).le
  have B6 : (d₀ : ℝ) ^ (2 * L) ≤ exp (2 * S * log d₀) := by
    rw [pow_eq_exp_mul_log (by linarith)]
    refine exp_le_exp.mpr ?_
    push_cast
    nlinarith
  have B7 : exp (C * (1 + R) ^ ρ) ^ (2 * L) ≤ exp (2 ^ (ρ + 2) * C * m * S) := by
    rw [← exp_nat_mul]
    refine exp_le_exp.mpr ?_
    have h1 : (1 + R) ^ ρ ≤ 2 ^ ρ * exp (ℓ / 2) := by
      rw [← hRpow, ← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) ρ
    have h2 : (2 * L : ℝ) * exp (ℓ / 2) ≤ 4 * m * S := by
      rw [hL, ← hsq]; push_cast
      have : (0 : ℝ) ≤ m * exp (ℓ / 2) := by positivity
      nlinarith
    have h3 : (0 : ℝ) ≤ 2 * L := by positivity
    calc ((2 * L : ℕ) : ℝ) * (C * (1 + R) ^ ρ) ≤ (2 * L : ℝ) * (C * (2 ^ ρ * exp (ℓ / 2))) := by
          push_cast
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hC) h3
      _ = C * 2 ^ ρ * ((2 * L : ℝ) * exp (ℓ / 2)) := by ring
      _ ≤ C * 2 ^ ρ * (4 * m * S) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ (ρ + 2) * C * m * S := by rw [pow_add]; ring
  have B8 : (2 * r / (R - r)) ^ (s * m) ≤ exp (S * m * (log (4 * r) - ℓ / (2 * ρ))) := by
    have hRr : 0 < R - r := by linarith
    have h1 : 2 * r / (R - r) ≤ 4 * r / R := by
      rw [div_le_div_iff₀ hRr (by linarith)]; nlinarith
    have h2 : 0 < 4 * r / R := by positivity
    calc (2 * r / (R - r)) ^ (s * m) ≤ (4 * r / R) ^ (s * m) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = exp (S * m * (log (4 * r) - ℓ / (2 * ρ))) := by
          rw [pow_eq_exp_mul_log h2, log_div (by linarith) (by linarith), hlogR, hSdef]
          push_cast; ring_nf
  have B9 : 1 / h₀ ^ (2 * L) ≤ exp (2 * S * log (1 / h₀)) := by
    rw [← one_div_pow, pow_eq_exp_mul_log (by positivity)]
    refine exp_le_exp.mpr ?_
    push_cast
    nlinarith
  -- assemble
  set EH : ℝ := 2 * a + 2 * S + (S * ℓ + S * KA) with hEH
  set EU : ℝ := δ * S * log d₀ + S * ℓ + (2 * S + EH + 2 * S * log d₀ + 2 ^ (ρ + 2) * C * m * S +
    S * m * (log (4 * r) - ℓ / (2 * ρ))) + 2 * S * log (1 / h₀) with hEU
  set EV : ℝ := 2 * S + EH + (S * ℓ + S * KA) with hEV
  have hAs0 : 0 ≤ Abd β Y δ L s := by unfold Abd; positivity
  have hP8 : 0 ≤ (2 * r / (R - r)) ^ (s * m) :=
    pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have i1 := mul_le_mul B3 B5 hH0 (exp_pos _).le
  have i2 := mul_le_mul i1 B6 (by positivity) (by positivity)
  have i3 := mul_le_mul i2 B7 (by positivity) (by positivity)
  have i4 := mul_le_mul i3 B8 hP8 (by positivity)
  have hX0 : 0 ≤ ((L * L : ℕ) : ℝ) * Hbd c L (Abd β Y δ L M) * (d₀ : ℝ) ^ (2 * L) *
      exp (C * (1 + R) ^ ρ) ^ (2 * L) * (2 * r / (R - r)) ^ (s * m) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hH0) (by positivity))
      (by positivity)) hP8
  have i5 := mul_le_mul (mul_le_mul (le_of_eq B1) B2 (by positivity) (by positivity)) i4 hX0
    (by positivity)
  have i6 := mul_le_mul i5 B9 (by positivity) (by positivity)
  have hU : (d₀ : ℝ) ^ (δ * s) * s.factorial *
      (((L * L : ℕ) : ℝ) * Hbd c L (Abd β Y δ L M) * (d₀ : ℝ) ^ (2 * L) *
        exp (C * (1 + R) ^ ρ) ^ (2 * L) * (2 * r / (R - r)) ^ (s * m)) / h₀ ^ (2 * L) ≤
      exp EU := by
    rw [div_eq_mul_one_div]
    refine i6.trans (le_of_eq ?_)
    simp only [← exp_add]
    exact congrArg exp (by rw [hEU, hEH])
  have hV : ((L * L : ℕ) : ℝ) * Hbd c L (Abd β Y δ L M) * Abd β Y δ L s ≤ exp EV := by
    refine (mul_le_mul i1 B10 hAs0 (by positivity)).trans (le_of_eq ?_)
    simp only [← exp_add]
    exact congrArg exp (by rw [hEV, hEH])
  have hV0 : 0 ≤ ((L * L : ℕ) : ℝ) * Hbd c L (Abd β Y δ L M) * Abd β Y δ L s :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hH0) hAs0
  have hUV := mul_le_mul hU (pow_le_pow_left₀ hV0 hV (d - 1)) (by positivity) (exp_pos _).le
  refine lt_of_le_of_lt hUV ?_
  rw [← exp_nat_mul, ← exp_add, exp_lt_one_iff]
  -- the exponent is negative
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; simp
  rw [hd1]
  have hmρ : 2 * d + 1 / (2 * ρ) ≤ (m : ℝ) / (2 * ρ) := by
    have : (4 * d * ρ + 1 : ℝ) ≤ m := by exact_mod_cast (show 4 * d * ρ + 1 ≤ m by omega)
    rw [le_div_iff₀ (by positivity)]
    have e : (2 * d + 1 / (2 * ρ)) * (2 * ρ) = (4 * d * ρ + 1 : ℝ) := by field_simp; ring
    rw [e]; exact this
  set P : ℝ := S * ℓ with hP
  have hP0 : 0 ≤ P := by positivity
  have hmP : (2 * d + 1 / (2 * ρ)) * P ≤ (m : ℝ) / (2 * ρ) * P :=
    mul_le_mul_of_nonneg_right hmρ hP0
  have hPK : S * K < P * (1 / (2 * ρ)) := by
    have : K < ℓ * (1 / (2 * ρ)) := by
      rw [mul_one_div, lt_div_iff₀ (by positivity)]; linarith
    calc S * K < S * (ℓ * (1 / (2 * ρ))) := mul_lt_mul_of_pos_left this hS0
      _ = P * (1 / (2 * ρ)) := by rw [hP]; ring
  have haS : a ≤ a * S := le_mul_of_one_le_right ha0 hS1
  have hdS : 0 ≤ ((d : ℝ) - 1) := by linarith
  have e1 : S * m * (log (4 * r) - ℓ / (2 * ρ)) = S * m * log (4 * r) - (m : ℝ) / (2 * ρ) * P := by
    rw [hP]; ring
  have hKS : S * K = δ * S * log d₀ + 4 * S + S * KA + 2 * S * log d₀ + 2 ^ (ρ + 2) * C * m * S +
      S * m * log (4 * r) + 2 * S * log (1 / h₀) + 2 * a * S +
      ((d : ℝ) - 1) * (4 * S + 2 * a * S + 2 * S * KA) := by rw [hK]; ring
  have hdaS : ((d : ℝ) - 1) * (2 * a) ≤ ((d : ℝ) - 1) * (2 * a * S) := by
    apply mul_le_mul_of_nonneg_left _ hdS; linarith
  have hexp : EU + ((d : ℝ) - 1) * EV =
      (2 * d) * P - (m : ℝ) / (2 * ρ) * P + (δ * S * log d₀ + 4 * S + S * KA + 2 * S * log d₀ +
        2 ^ (ρ + 2) * C * m * S + S * m * log (4 * r) + 2 * S * log (1 / h₀) + 2 * a) +
        ((d : ℝ) - 1) * (4 * S + 2 * a + 2 * S * KA) := by
    rw [hEU, hEV, hEH, e1, hP]; ring
  rw [hexp]
  linarith [hmP, hPK, haS, hdaS, hKS]

end LSG.SL
