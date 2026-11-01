/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Prop61Arith

/-!
# The final inequality of W88 §7: (7.2) ⇒ (7.3) ⇒ (4.1)

All in logarithmic form, with `LS = log S`, `ℓℓ = log log S`, `LΔ = log Δ`,
`q LΔ = log C + e LS + 2 d₀ ℓℓ` (W88's `Δ^{d−n} = C S^{d₁+2d₂−κ} (log S)^{b d₀}` with `b = 2`).

* **`core_ineq`**: from
  `(λ + δ₁ + 2δ₂) LS ≤ K₀ + (δ − τ) LΔ + (τ − 2δ₀) ℓℓ` (the logarithm of (7.2)) and `S` large
  (`K_b + B_b ℓℓ < LS`, `K_b < ℓℓ`) follow `q(λ + δ₁ + 2δ₂) ≤ e(δ − τ)` and, if `δ ≥ 1`, `τ < δ`.
* `eventually_log_big`: the "`S` large" conditions hold eventually.
* `log_delta61`, `log_succ_le_of_le`, `floor_ge_half`: the parameter estimates.
-/

open Real Filter

noncomputable section

namespace LSG.W88

/-- `K + B log x < x` and `K < log x` for large `x`. -/
theorem eventually_log_lt (K B : ℝ) :
    ∀ᶠ x : ℝ in atTop, K + B * Real.log x < x ∧ K < Real.log x := by
  refine ((tendsto_log_atTop.eventually_gt_atTop K).and
    ((eventually_ge_atTop ((2 * |B| + |K| + 1) ^ 2)).and (eventually_ge_atTop 1))).mono ?_
  rintro x ⟨hK, hx, hx1⟩
  refine ⟨?_, hK⟩
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hs1 : 2 * |B| + |K| + 1 ≤ Real.sqrt x := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * |B| + |K| + 1)]
    exact Real.sqrt_le_sqrt hx
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [show (2 : ℝ) * Real.log (Real.sqrt x) = ((2 : ℕ) : ℝ) * Real.log (Real.sqrt x) by
        norm_num, ← Real.log_pow, Real.sq_sqrt (by linarith)]
    have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos (by nlinarith)
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hB : B * Real.log x ≤ |B| * (2 * Real.sqrt x) :=
    (le_abs_self B |>.trans le_rfl) |> fun h => by
      calc B * Real.log x ≤ |B| * Real.log x := mul_le_mul_of_nonneg_right (le_abs_self B) hlog0
        _ ≤ |B| * (2 * Real.sqrt x) := mul_le_mul_of_nonneg_left hlog (abs_nonneg B)
  have hKa : K ≤ |K| := le_abs_self K
  nlinarith [abs_nonneg B, abs_nonneg K]

/-- The "`S` large" conditions in terms of `S : ℕ`. -/
theorem eventually_log_big (K B : ℝ) :
    ∀ᶠ S : ℕ in atTop, K + B * Real.log (Real.log S) < Real.log S ∧ K < Real.log (Real.log S) :=
  (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_log_lt K B)

/-- **The core of (7.2) ⇒ (7.3) ⇒ (4.1).** -/
theorem core_ineq {q e d0 lam τ δ0 δ1 δ2 : ℕ} (hq : 1 ≤ q) (he : 1 ≤ e)
    {LS ℓℓ LΔ K0 Kb Bb logC : ℝ}
    (h1 : ((lam + δ1 + 2 * δ2 : ℕ) : ℝ) * LS ≤
      K0 + (((δ0 + δ1 + δ2 : ℕ) : ℝ) - τ) * LΔ + ((τ : ℝ) - 2 * δ0) * ℓℓ)
    (h2 : (q : ℝ) * LΔ = logC + e * LS + 2 * d0 * ℓℓ)
    (hK : q * K0 + (((δ0 + δ1 + δ2 : ℕ) : ℝ) - τ) * logC ≤ Kb)
    (hB : 2 * d0 * (((δ0 + δ1 + δ2 : ℕ) : ℝ) - τ) + q * ((τ : ℝ) - 2 * δ0) ≤ Bb)
    (hLS : 0 ≤ LS) (hℓ : 0 ≤ ℓℓ) (hbig : Kb + Bb * ℓℓ < LS) (hbig2 : Kb < ℓℓ) :
    ((q * (lam + δ1 + 2 * δ2) : ℕ) : ℤ) ≤ (e : ℤ) * ((δ0 + δ1 + δ2 : ℕ) - (τ : ℤ)) ∧
      (1 ≤ δ0 + δ1 + δ2 → τ < δ0 + δ1 + δ2) := by
  set δ := δ0 + δ1 + δ2 with hδ
  set Dr : ℝ := (δ : ℝ) - τ with hDr
  set Ar : ℝ := (q : ℝ) * ((lam + δ1 + 2 * δ2 : ℕ) : ℝ) - e * Dr with hAr
  -- `A · LS ≤ K_b + B_b ℓℓ`
  have hmain : Ar * LS ≤ (q * K0 + Dr * logC) + (2 * d0 * Dr + q * ((τ : ℝ) - 2 * δ0)) * ℓℓ := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have := mul_le_mul_of_nonneg_left h1 hq0
    have e1 : (q : ℝ) * (K0 + Dr * LΔ + ((τ : ℝ) - 2 * δ0) * ℓℓ) =
        q * K0 + Dr * (q * LΔ) + q * ((τ : ℝ) - 2 * δ0) * ℓℓ := by ring
    rw [e1, h2] at this
    rw [hAr]
    nlinarith [this]
  have hBℓ : (2 * d0 * Dr + q * ((τ : ℝ) - 2 * δ0)) * ℓℓ ≤ Bb * ℓℓ :=
    mul_le_mul_of_nonneg_right hB hℓ
  have hAle : Ar * LS < LS := by linarith
  -- `A ≤ 0`
  have hA : ((q * (lam + δ1 + 2 * δ2) : ℕ) : ℤ) ≤ (e : ℤ) * ((δ : ℕ) - (τ : ℤ)) := by
    by_contra hcon
    push Not at hcon
    have hA1 : (1 : ℝ) ≤ Ar := by
      have : (1 : ℤ) ≤ ((q * (lam + δ1 + 2 * δ2) : ℕ) : ℤ) - (e : ℤ) * ((δ : ℕ) - (τ : ℤ)) := by
        omega
      have h' : ((((q * (lam + δ1 + 2 * δ2) : ℕ) : ℤ) - (e : ℤ) * ((δ : ℕ) - (τ : ℤ)) : ℤ) : ℝ) =
          Ar := by
        rw [hAr, hDr]; push_cast; ring
      rw [← h']; exact_mod_cast this
    nlinarith
  refine ⟨hA, fun hδ1 => ?_⟩
  by_contra hτ
  push Not at hτ
  -- then `λ = δ₁ = δ₂ = 0` and `δ = τ = δ₀`
  have hnn : (e : ℤ) * ((δ : ℕ) - (τ : ℤ)) ≤ 0 := by
    have : ((δ : ℕ) : ℤ) - (τ : ℤ) ≤ 0 := by omega
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  have hzero : q * (lam + δ1 + 2 * δ2) = 0 := by omega
  have hl0 : lam + δ1 + 2 * δ2 = 0 := by
    rcases Nat.mul_eq_zero.mp hzero with h | h
    · omega
    · exact h
  have hδτ : δ = τ := by
    have : (e : ℤ) * ((δ : ℕ) - (τ : ℤ)) = 0 := by omega
    rcases mul_eq_zero.mp this with h | h
    · omega
    · omega
  have hδ0 : δ0 = δ := by omega
  have hDr0 : Dr = 0 := by rw [hDr, hδτ, sub_self]
  -- `0 ≤ q K₀ − q δ₀ ℓℓ ≤ K_b − ℓℓ`
  have hAr0 : Ar = 0 := by
    rw [hAr, hDr0]
    have : ((lam + δ1 + 2 * δ2 : ℕ) : ℝ) = 0 := by exact_mod_cast hl0
    rw [this]; ring
  rw [hAr0, zero_mul, hDr0] at hmain
  have hK' : (q : ℝ) * K0 ≤ Kb := by rw [hDr0] at hK; linarith
  have hτ0 : (τ : ℝ) - 2 * δ0 = -(δ0 : ℝ) := by
    have : (τ : ℝ) = δ0 := by exact_mod_cast (hδτ.symm.trans hδ0.symm)
    rw [this]; ring
  rw [hτ0] at hmain
  have hqδ : (1 : ℝ) ≤ (q : ℝ) * δ0 := by
    have : 1 ≤ q * δ0 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  nlinarith

/-- The logarithm of `Δ`. -/
theorem log_delta61 {C : ℝ} (hC : 0 < C) {e d q S : ℕ} (hq : 1 ≤ q) (hS : 3 ≤ S) :
    0 < delta61 C e d q S ∧
      (q : ℝ) * Real.log (delta61 C e d q S) =
        Real.log C + e * Real.log S + d * Real.log (Real.log S) := by
  have hl := log_ge_one hS
  have hS0 : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
  have hpos : 0 < C * (S : ℝ) ^ e * Real.log S ^ d := by positivity
  have hΔ : 0 < delta61 C e d q S := by unfold delta61; exact Real.rpow_pos_of_pos hpos _
  refine ⟨hΔ, ?_⟩
  rw [← Real.log_pow, delta_pow hC.le hq, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]

/-- `log (n + 1) ≤ log X + log (1 + e^{−c})` for `n ≤ X`, `log X ≥ c`. -/
theorem log_succ_le_of_le {X c : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ X) (hX : c ≤ Real.log X)
    (hX0 : 0 < X) : Real.log ((n : ℝ) + 1) ≤ Real.log X + Real.log (1 + Real.exp (-c)) := by
  rw [← Real.log_mul hX0.ne' (by positivity)]
  apply Real.log_le_log (by positivity)
  have h1 : 1 ≤ X * Real.exp (-c) := by
    have : Real.exp c ≤ X := by rwa [← Real.exp_log hX0, Real.exp_le_exp]
    rw [Real.exp_neg]
    rw [le_mul_inv_iff₀ (Real.exp_pos c)]; linarith
  nlinarith

/-- `⌊X⌋₊ ≥ 1` and `log ⌊X⌋₊ ≥ log X − log 2` for `X ≥ 2`. -/
theorem floor_ge_half {X : ℝ} (hX : 2 ≤ X) :
    1 ≤ ⌊X⌋₊ ∧ Real.log X - Real.log 2 ≤ Real.log (⌊X⌋₊ : ℝ) := by
  have h1 : X - 1 < (⌊X⌋₊ : ℝ) := Nat.sub_one_lt_floor X
  have h2 : (1 : ℝ) ≤ ⌊X⌋₊ := by linarith
  refine ⟨by exact_mod_cast h2, ?_⟩
  rw [← Real.log_div (by linarith) (by norm_num)]
  exact Real.log_le_log (by linarith) (by linarith)

end LSG.W88
