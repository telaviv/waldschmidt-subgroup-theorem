/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LemmaUBounds

/-!
# A5.5b: the bookkeeping of Lemma U (`STAGE_A5.md` D2)

All quantities of the Cauchy–Liouville step are bounded by `exp (K · Bud)`, with

  `Bud = B + log (L + 1) + (A₀ + 1) log (S + 1) + (A₁ + 1) S + (D + 1) S² + (T + 1) log (T + 2)`

(`budU`, the elliptic Lemma U budget) and constants `K` that do not depend on `B, L, A₀, A₁, D, S, T`:
`le_bud_A` (sizes), `le_bud_e` (denominators), `le_bud_cauchy` (radius), `le_bud_unit` (the unit), and
`small_of_bud` (the final inequality).
-/

open Real

noncomputable section

namespace LSG.AuxA

/-- **The Lemma U budget.** -/
def budU (Bp : ℝ) (L A₀ A₁ D S T : ℕ) : ℝ :=
  Bp + Real.log (L + 1) + (A₀ + 1) * Real.log (S + 1) + (A₁ + 1) * S + (D + 1) * (S : ℝ) ^ 2 +
    (T + 1) * Real.log (T + 2)

section

variable {Bp : ℝ} {L A₀ A₁ D S T : ℕ}

lemma log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
lemma log2_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith

lemma log_S_ge (S : ℕ) : Real.log 2 ≤ Real.log (S + 1) ∨ S = 0 := by
  rcases Nat.eq_zero_or_pos S with h | h
  · exact Or.inr h
  · left; exact Real.log_le_log (by norm_num) (by have : (1 : ℝ) ≤ S := by exact_mod_cast h
                                                  linarith)

lemma log_T_ge (T : ℕ) : Real.log 2 ≤ Real.log (T + 2) :=
  Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])

/-- The six terms are nonnegative, so each is at most `budU`. -/
lemma bud_terms (hS : 1 ≤ S) (hBp : 0 ≤ Bp) :
    0 ≤ Bp ∧ 0 ≤ Real.log (L + 1) ∧ Real.log 2 ≤ Real.log (S + 1) ∧ 0 ≤ (A₁ + 1) * (S : ℝ) ∧
      0 ≤ (D + 1) * (S : ℝ) ^ 2 ∧ Real.log 2 ≤ Real.log (T + 2) := by
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  refine ⟨hBp, Real.log_nonneg (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]),
    Real.log_le_log (by norm_num) (by linarith), by positivity, by positivity, log_T_ge T⟩

lemma bud_pos (hS : 1 ≤ S) (hBp : 0 ≤ Bp) : 0 < budU Bp L A₀ A₁ D S T := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bud_terms (L := L) (A₁ := A₁) (D := D) (T := T) hS hBp
  have := log2_pos
  have hA : 0 < ((A₀ : ℝ) + 1) * Real.log (S + 1) := mul_pos (by positivity) (lt_of_lt_of_le this h3)
  have hT : 0 ≤ ((T : ℝ) + 1) * Real.log (T + 2) := mul_nonneg (by positivity) (le_trans this.le h6)
  unfold budU; linarith

/-- The individual terms. -/
lemma le_bud (hS : 1 ≤ S) (hBp : 0 ≤ Bp) :
    Bp + Real.log (L + 1) ≤ budU Bp L A₀ A₁ D S T ∧
    (A₀ : ℝ) * Real.log 2 ≤ budU Bp L A₀ A₁ D S T ∧
    ((A₀ : ℝ) + 1) * Real.log (S + 1) ≤ budU Bp L A₀ A₁ D S T ∧
    (A₁ : ℝ) * S ≤ budU Bp L A₀ A₁ D S T ∧ (A₁ : ℝ) ≤ budU Bp L A₀ A₁ D S T ∧
    (D : ℝ) * (S : ℝ) ^ 2 ≤ budU Bp L A₀ A₁ D S T ∧ (D : ℝ) ≤ budU Bp L A₀ A₁ D S T ∧
    (S : ℝ) ^ 2 ≤ budU Bp L A₀ A₁ D S T ∧
    ((T : ℝ) + 1) * Real.log (T + 2) ≤ budU Bp L A₀ A₁ D S T ∧
    (T : ℝ) * Real.log 2 ≤ budU Bp L A₀ A₁ D S T := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bud_terms (L := L) (A₁ := A₁) (D := D) (T := T) hS hBp
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have l2 := log2_pos
  have hA : 0 ≤ ((A₀ : ℝ) + 1) * Real.log (S + 1) := mul_nonneg (by positivity) (le_trans l2.le h3)
  have hT : 0 ≤ ((T : ℝ) + 1) * Real.log (T + 2) := mul_nonneg (by positivity) (le_trans l2.le h6)
  have hA0 : (0 : ℝ) ≤ A₀ := Nat.cast_nonneg _
  have hA1 : (0 : ℝ) ≤ A₁ := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hS2 : (1 : ℝ) ≤ (S : ℝ) ^ 2 := one_le_pow₀ hSR
  unfold budU
  refine ⟨by linarith, ?_, by linarith, ?_, ?_, ?_, ?_, ?_, by linarith, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith [log_T_ge T]

end

/-! ### The pieces -/

section Pieces

variable {Bp : ℝ} {L A₀ A₁ D S T : ℕ}

lemma exp_mul_exp_le {x y a b : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ Real.exp a) (hy : y ≤ Real.exp b) :
    x * y ≤ Real.exp (a + b) := by
  rw [Real.exp_add]; exact mul_le_mul hx hy hy0 (Real.exp_pos a).le

lemma pow_le_exp_bud {c : ℝ} (hc : 1 ≤ c) {n : ℕ} {X a Bud : ℝ} (hn : (n : ℝ) * X ≤ a * Bud)
    (hX : Real.log c ≤ X) : c ^ n ≤ Real.exp (a * Bud) := by
  rw [← Real.exp_log (by linarith : (0 : ℝ) < c), ← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr (le_trans ?_ hn)
  exact mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg n)

/-- `c^{A₀} ≤ exp (log c / log 2 · Bud)` for `c ≥ 1`. -/
lemma pow_A0_le (hS : 1 ≤ S) (hBp : 0 ≤ Bp) {c : ℝ} (hc : 1 ≤ c) :
    c ^ A₀ ≤ Real.exp (Real.log c / Real.log 2 * budU Bp L A₀ A₁ D S T) := by
  have h := (le_bud (L := L) (A₀ := A₀) (A₁ := A₁) (D := D) (T := T) hS hBp).2.1
  refine pow_le_exp_bud hc ?_ le_rfl
  have hl := Real.log_nonneg hc
  have l2 := log2_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ l2]
  nlinarith

/-- **Sizes**: `(L + 1) e^B 2^{d₀A₀ + d₁A₁ + G D} (S h)^{d₀A₀} (H^{μS})^{d₁A₁} P^D (c (T+1))^j ≤ exp (K Bud)`. -/
lemma le_bud_A (hS : 1 ≤ S) (hBp : 0 ≤ Bp) {d₀ d₁ G μ j : ℕ} (hj : j ≤ T) {h H P c : ℝ} (hh : 1 ≤ h)
    (hH : 1 ≤ H) (hP : 1 ≤ P) (hc : 1 ≤ c) :
    ((L : ℝ) + 1) * Real.exp Bp * (2 : ℝ) ^ (d₀ * A₀ + d₁ * A₁ + G * D) * ((S : ℝ) * h) ^ (d₀ * A₀) *
        (H ^ (μ * S)) ^ (d₁ * A₁) * P ^ D * (c * (T + 1)) ^ j ≤
      Real.exp ((1 + d₀ + d₁ + G + d₀ * (1 + Real.log h / Real.log 2) + d₁ * μ * Real.log H +
        Real.log P + (1 + Real.log c / Real.log 2)) * budU Bp L A₀ A₁ D S T) := by
  obtain ⟨hL, hA0, hA0S, hA1S, hA1, hDS, hD, -, hT, -⟩ :=
    le_bud (L := L) (A₀ := A₀) (A₁ := A₁) (D := D) (T := T) hS hBp
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have l2 := log2_pos
  have l21 := log2_le_one
  have hlh := Real.log_nonneg hh
  have hlH := Real.log_nonneg hH
  have hlP := Real.log_nonneg hP
  have hlc := Real.log_nonneg hc
  have hbud := bud_pos (L := L) (A₀ := A₀) (A₁ := A₁) (D := D) (T := T) hS hBp
  set Bud := budU Bp L A₀ A₁ D S T
  -- the six factors
  have f1 : ((L : ℝ) + 1) * Real.exp Bp ≤ Real.exp (1 * Bud) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < L + 1), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have f2 : (2 : ℝ) ^ (d₀ * A₀ + d₁ * A₁ + G * D) ≤ Real.exp ((d₀ + d₁ + G) * Bud) := by
    refine pow_le_exp_bud one_le_two ?_ le_rfl
    push_cast
    have e1 : (d₀ : ℝ) * A₀ * Real.log 2 ≤ d₀ * Bud := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hA0 (Nat.cast_nonneg _)
    have e2 : (d₁ : ℝ) * A₁ * Real.log 2 ≤ d₁ * Bud := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg _)
    have e3 : (G : ℝ) * D * Real.log 2 ≤ G * Bud := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg _)
    nlinarith
  have f3 : ((S : ℝ) * h) ^ (d₀ * A₀) ≤ Real.exp (d₀ * (1 + Real.log h / Real.log 2) * Bud) := by
    refine pow_le_exp_bud (one_le_mul_of_one_le_of_one_le hSR hh) ?_
      (LSG.Aux.log_mul_le_log_succ hSR hh)
    push_cast
    have : (A₀ : ℝ) * Real.log (S + 1) ≤ Bud := by nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ S + 1)]
    have hk : 0 ≤ 1 + Real.log h / Real.log 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hk, (Nat.cast_nonneg d₀ : (0 : ℝ) ≤ d₀)]
  have f4 : (H ^ (μ * S)) ^ (d₁ * A₁) ≤ Real.exp (d₁ * μ * Real.log H * Bud) := by
    rw [← pow_mul]
    refine pow_le_exp_bud hH ?_ le_rfl
    push_cast
    have : (A₁ : ℝ) * S * (d₁ * μ * Real.log H) ≤ Bud * (d₁ * μ * Real.log H) :=
      mul_le_mul_of_nonneg_right hA1S (by positivity)
    nlinarith
  have f5 : P ^ D ≤ Real.exp (Real.log P * Bud) := by
    refine pow_le_exp_bud hP ?_ le_rfl
    nlinarith
  have f6 : (c * (T + 1)) ^ j ≤ Real.exp ((1 + Real.log c / Real.log 2) * Bud) := by
    refine (LSG.Aux.natPow_le_exp hc j T hj).trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_left hT (by positivity)
  have p1 := exp_mul_exp_le (by positivity) (by positivity) f1 f2
  have p2 := exp_mul_exp_le (by positivity) (by positivity) p1 f3
  have p3 := exp_mul_exp_le (by positivity) (by positivity) p2 f4
  have p4 := exp_mul_exp_le (by positivity) (by positivity) p3 f5
  have p5 := exp_mul_exp_le (by positivity) (by positivity) p4 f6
  refine p5.trans (Real.exp_le_exp.mpr (le_of_eq ?_))
  ring

/-- **Denominators**: `(d²)^{d₀A₀} (d^{μS})^{d₁A₁} Q^D δ^j j! ≤ exp (K Bud)`. -/
lemma le_bud_e (hS : 1 ≤ S) (hBp : 0 ≤ Bp) {d₀ d₁ μ j d Q δ : ℕ} (hj : j ≤ T) (hd : 1 ≤ d) (hQ : 1 ≤ Q)
    (hδ : 1 ≤ δ) :
    ((d * d : ℕ) : ℝ) ^ (d₀ * A₀) * ((d : ℝ) ^ (μ * S)) ^ (d₁ * A₁) * (Q : ℝ) ^ D * (δ : ℝ) ^ j *
        (j.factorial : ℝ) ≤
      Real.exp ((d₀ * (2 * Real.log d / Real.log 2) + d₁ * μ * Real.log d + Real.log Q +
        Real.log δ / Real.log 2 + 1) * budU Bp L A₀ A₁ D S T) := by
  obtain ⟨-, hA0, -, hA1S, -, -, hD, -, hT, hTl⟩ :=
    le_bud (L := L) (A₀ := A₀) (A₁ := A₁) (D := D) (T := T) hS hBp
  have l2 := log2_pos
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hld := Real.log_nonneg hdR
  have hlQ := Real.log_nonneg hQR
  have hlδ := Real.log_nonneg hδR
  set Bud := budU Bp L A₀ A₁ D S T
  have f1 : ((d * d : ℕ) : ℝ) ^ (d₀ * A₀) ≤ Real.exp (d₀ * (2 * Real.log d / Real.log 2) * Bud) := by
    have h1 : (1 : ℝ) ≤ ((d * d : ℕ) : ℝ) := by push_cast; nlinarith
    rw [pow_mul']
    refine (pow_le_pow_left₀ (by positivity) (pow_A0_le (L := L) (A₁ := A₁) (D := D) (T := T)
      hS hBp h1) d₀).trans ?_
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr (le_of_eq ?_)
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]; ring
  have f2 : ((d : ℝ) ^ (μ * S)) ^ (d₁ * A₁) ≤ Real.exp (d₁ * μ * Real.log d * Bud) := by
    rw [← pow_mul]
    refine pow_le_exp_bud hdR ?_ le_rfl
    push_cast
    have : (A₁ : ℝ) * S * (d₁ * μ * Real.log d) ≤ Bud * (d₁ * μ * Real.log d) :=
      mul_le_mul_of_nonneg_right hA1S (by positivity)
    nlinarith
  have f3 : (Q : ℝ) ^ D ≤ Real.exp (Real.log Q * Bud) := by
    refine pow_le_exp_bud hQR ?_ le_rfl
    nlinarith
  have f4 : (δ : ℝ) ^ j ≤ Real.exp (Real.log δ / Real.log 2 * Bud) := by
    refine pow_le_exp_bud hδR ?_ le_rfl
    have hjT : (j : ℝ) ≤ T := by exact_mod_cast hj
    rw [div_mul_eq_mul_div, le_div_iff₀ l2]
    have : (j : ℝ) * Real.log 2 ≤ Bud := le_trans (by nlinarith) hTl
    nlinarith
  have f5 : (j.factorial : ℝ) ≤ Real.exp (1 * Bud) :=
    (LSG.Aux.factorial_le_exp j T hj).trans (Real.exp_le_exp.mpr (by linarith))
  have p1 := exp_mul_exp_le (by positivity) (by positivity) f1 f2
  have p2 := exp_mul_exp_le (by positivity) (by positivity) p1 f3
  have p3 := exp_mul_exp_le (by positivity) (by positivity) p2 f4
  have p4 := exp_mul_exp_le (by positivity) (by positivity) p3 f5
  refine p4.trans (Real.exp_le_exp.mpr (le_of_eq ?_))
  ring

/-- **The unit**: `exp (m D (a S² + b S + c)) ≤ exp (m (a + b + c) Bud)` for `a, b, c ≥ 0`. -/
lemma le_bud_unit (hS : 1 ≤ S) (hBp : 0 ≤ Bp) {m : ℕ} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.exp (m * D * (a * (S : ℝ) ^ 2 + b * S + c)) ≤ Real.exp (m * (a + b + c) * budU Bp L A₀ A₁ D S T) := by
  obtain ⟨-, -, -, -, -, hDS, -, -, -, -⟩ := le_bud (L := L) (A₀ := A₀) (A₁ := A₁) (D := D) (T := T) hS hBp
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hS2 : (S : ℝ) ≤ (S : ℝ) ^ 2 := by nlinarith
  apply Real.exp_le_exp.mpr
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h1 : (D : ℝ) * (a * (S : ℝ) ^ 2 + b * S + c) ≤ (a + b + c) * (D * (S : ℝ) ^ 2) := by
    nlinarith [mul_nonneg hD0 hb, mul_nonneg hD0 hc, mul_nonneg (mul_nonneg hD0 hc) (by nlinarith : (0 : ℝ) ≤ (S : ℝ) ^ 2 - 1)]
  have h2 : (a + b + c) * (D * (S : ℝ) ^ 2) ≤ (a + b + c) * budU Bp L A₀ A₁ D S T :=
    mul_le_mul_of_nonneg_left hDS (by positivity)
  calc (m : ℝ) * D * (a * (S : ℝ) ^ 2 + b * S + c) = m * (D * (a * (S : ℝ) ^ 2 + b * S + c)) := by ring
    _ ≤ m * ((a + b + c) * budU Bp L A₀ A₁ D S T) := mul_le_mul_of_nonneg_left (h1.trans h2) hm0
    _ = _ := by ring

/-- **The radius**: `((1 + T W)/ρ₀)^j ≤ exp (K Bud)` for `0 < ρ₀ ≤ 1`, `W ≥ 0`. -/
lemma le_bud_cauchy (hS : 1 ≤ S) (hBp : 0 ≤ Bp) {j : ℕ} (hj : j ≤ T) {W ρ₀ : ℝ} (hW : 0 ≤ W)
    (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ ≤ 1) :
    ((1 + T * W) / ρ₀) ^ j ≤
      Real.exp ((1 + Real.log ((1 + W) / ρ₀) / Real.log 2) * budU Bp L A₀ A₁ D S T) := by
  obtain ⟨-, -, -, -, -, -, -, -, hT, -⟩ := le_bud (L := L) (A₀ := A₀) (A₁ := A₁) (D := D) (T := T) hS hBp
  have hc : 1 ≤ (1 + W) / ρ₀ := by rw [le_div_iff₀ hρ₀]; linarith
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have h1 : (1 + T * W) / ρ₀ ≤ (1 + W) / ρ₀ * (T + 1) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hρ₀.le
  refine (pow_le_pow_left₀ (by positivity) h1 j).trans ?_
  refine (LSG.Aux.natPow_le_exp hc j T hj).trans (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_left hT (by have := Real.log_nonneg hc; have := log2_pos; positivity)

/-- **The final inequality.** -/
lemma small_of_bud {M ρ U Bud X Y KU Kρ KX KY : ℝ} {j deg : ℕ} (hρ : 0 < ρ) (hBud : 0 < Bud)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hM : M ≤ Real.exp (-U + KU * Bud)) (hρj : (1 / ρ) ^ j ≤ Real.exp (Kρ * Bud))
    (hX : X ≤ Real.exp (KX * Bud)) (hY : Y ≤ Real.exp (KY * Bud))
    (hU : (KU + Kρ + deg * (KX + KY) + 1) * Bud ≤ U) :
    M / ρ ^ j * (X * Y) ^ deg < 1 := by
  have hXY : (X * Y) ^ deg ≤ Real.exp (deg * (KX + KY) * Bud) := by
    have := exp_mul_exp_le hX0 hY0 hX hY
    refine (pow_le_pow_left₀ (by positivity) this deg).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]; ring_nf
  have hMρ : M / ρ ^ j ≤ Real.exp (-U + KU * Bud) * Real.exp (Kρ * Bud) := by
    rw [div_eq_mul_one_div, ← one_div_pow]
    have hM0 : 0 ≤ (1 / ρ) ^ j := by positivity
    by_cases hM0' : 0 ≤ M
    · exact mul_le_mul hM hρj hM0 (Real.exp_pos _).le
    · push Not at hM0'
      exact (mul_nonpos_of_nonpos_of_nonneg hM0'.le hM0).trans (by positivity)
  have hprod : M / ρ ^ j * (X * Y) ^ deg ≤
      Real.exp (-U + KU * Bud) * Real.exp (Kρ * Bud) * Real.exp (deg * (KX + KY) * Bud) := by
    by_cases h0 : 0 ≤ M / ρ ^ j
    · exact mul_le_mul hMρ hXY (by positivity) (by positivity)
    · push Not at h0
      exact (mul_nonpos_of_nonpos_of_nonneg h0.le (by positivity)).trans (by positivity)
  refine lt_of_le_of_lt hprod ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith)

end Pieces

end LSG.AuxA
