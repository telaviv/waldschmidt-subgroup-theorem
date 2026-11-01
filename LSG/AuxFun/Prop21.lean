/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Siegel
import LSG.AuxFun.Grid
import LSG.AuxFun.Reps

/-!
# W83 Prop. 2.1 (the auxiliary function with periods), Tier 1

Waldschmidt, Ann. Math. 117 (1983), Prop. 2.1 and the Remark on p. 636, for periods that are
`ℂ`-linearly independent, stated in adapted coordinates: the periods are the first `κ` unit vectors
of `ℂⁿ` (`STAGE3_D2.md`, §3 O1–O2, §4.1).

Let `ψ_1, …, ψ_L` be entire functions on `ℂⁿ` with a common multiplier under `ℤ^κ × 0`
(hypothesis `QuasiPeriodic`, the abstract form of `ψ_λ = σ^D φ_λ` with `σ` a theta function and
`φ_λ` periodic). If

  `U ≥ Δ`, `R/r ≥ c₁`, `r ≥ c₁`, `U ≥ r log(R/r)`, `U ≥ D r²`, `Σ_λ |ψ_λ|_R ≤ e^U`,
  `c₂ U^{n+1} ≤ L Δ r^κ (log R/r)^n`,

then there are integers `p_λ`, not all zero, `|p_λ| ≤ e^Δ`, with `|Σ p_λ ψ_λ|_r ≤ e^{−U}`
(sup norm on `ℂⁿ`, i.e. W83's polydisc norm). The factor `r^κ` is the κ-saving.

Proof: Siegel's lemma (`siegel_approx`) on the condition set of `LSG.Aux.condIdx` (a fundamental
domain of the periods, `K^κ N^{n−κ}` points); transfer to the whole grid by the multiplier
(`grid_decomp`); interpolation on the product grid (`grid_interp`, `prog_constants`).
Constants: `c₁ = exp (6000 (n + 1))`, `c₂ = 2 (6 + 9a) 60ⁿ`.

* `LSG.Aux.QuasiPeriodic`, `LSG.Aux.prop21`.
-/

open Complex Finset

namespace LSG.Aux

/-- **Hypothesis (QP), single-constant form.** A common multiplier under every period
`ω ∈ ℤ^κ × 0`, bounded by `exp (b (|z| + |ω|)²)`. -/
def QuasiPeriodicB {n L : ℕ} (κ : ℕ) (b : ℝ) (ψ : Fin L → (Fin n → ℂ) → ℂ) : Prop :=
  ∀ k : Fin n → ℤ, (∀ i : Fin n, κ ≤ i.val → k i = 0) → ∀ z : Fin n → ℂ,
    ∃ m : ℂ, ‖m‖ ≤ Real.exp (b * (‖z‖ + ‖(fun i => (k i : ℂ))‖) ^ 2) ∧
      ∀ l, ψ l (z + fun i => (k i : ℂ)) = m * ψ l z

/-- **Hypothesis (QP).** The `ψ_λ` have a common multiplier under every period `ω ∈ ℤ^κ × 0`,
bounded by `exp (a D (|z| + |ω|)²)` (for `ψ_λ = σ^D φ_λ`, `σ` a theta function for a lattice
containing the image of the periods, this is the factor of automorphy of `σ^D`). -/
def QuasiPeriodic {n L : ℕ} (κ : ℕ) (a : ℝ) (D : ℕ) (ψ : Fin L → (Fin n → ℂ) → ℂ) : Prop :=
  ∀ k : Fin n → ℤ, (∀ i : Fin n, κ ≤ i.val → k i = 0) → ∀ z : Fin n → ℂ,
    ∃ m : ℂ, ‖m‖ ≤ Real.exp (a * D * (‖z‖ + ‖(fun i => (k i : ℂ))‖) ^ 2) ∧
      ∀ l, ψ l (z + fun i => (k i : ℂ)) = m * ψ l z

/-- The counting inequality behind the κ-saving. -/
lemma count_arith {n κ K N : ℕ} (hκ : κ ≤ n) {r ℓ U : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ)
    (hN : (N : ℝ) ≤ 3 * (r * K)) (hK : r * K * ℓ ≤ 20 * U) :
    ((K ^ κ * N ^ (n - κ) : ℕ) : ℝ) * r ^ κ * ℓ ^ n ≤ 60 ^ n * U ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hκ
  rw [Nat.add_sub_cancel_left]
  have h0 : 0 ≤ r * K * ℓ := by positivity
  push_cast
  calc (K : ℝ) ^ κ * N ^ m * r ^ κ * ℓ ^ (κ + m)
      ≤ (K : ℝ) ^ κ * (3 * (r * K)) ^ m * r ^ κ * ℓ ^ (κ + m) := by gcongr
    _ = 3 ^ m * (r * K * ℓ) ^ (κ + m) := by ring
    _ ≤ 3 ^ (κ + m) * (20 * U) ^ (κ + m) := by
        gcongr
        · norm_num
        · omega
    _ = 60 ^ (κ + m) * U ^ (κ + m) := by rw [← mul_pow, ← mul_pow, ← mul_assoc]; norm_num

/-- The final numerical inequality. -/
lemma final_arith {n N : ℕ} {U ℓ Δ q : ℝ} (hU : 6000 * ((n : ℝ) + 1) ≤ U)
    (hℓ : 6000 * ((n : ℝ) + 1) ≤ ℓ) (hN1 : 10 * U / ℓ ≤ N) (hN2 : (N : ℝ) ≤ 60 * U / ℓ)
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-(ℓ / 2))) (hΔ : Δ ≤ U) :
    ((100 : ℝ) ^ N) ^ n * (2 * Real.exp (-(3 * U)) + n * q ^ N * Real.exp (Δ + U)) ≤
      Real.exp (-U) := by
  have hℓ0 : 0 < ℓ := by nlinarith
  have hlog : Real.log 100 ≤ 99 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100); linarith
  have hlog0 : 0 ≤ Real.log 100 := Real.log_nonneg (by norm_num)
  -- `100^{Nn} ≤ e^U`
  have h100 : ((100 : ℝ) ^ N) ^ n ≤ Real.exp U := by
    have he : ((100 : ℝ) ^ N) ^ n = Real.exp ((N * n : ℕ) * Real.log 100) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num), ← pow_mul]
    rw [he, Real.exp_le_exp]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h1 : (N : ℝ) * ℓ ≤ 60 * U := by rwa [le_div_iff₀ hℓ0] at hN2
    have h2 : (n : ℝ) * 5940 ≤ ℓ := by nlinarith
    push_cast
    calc (N : ℝ) * n * Real.log 100 ≤ N * n * 99 := by gcongr
      _ ≤ U := by nlinarith
  -- `q^N ≤ e^{−5U}`
  have hqN : q ^ N ≤ Real.exp (-(5 * U)) := by
    calc q ^ N ≤ Real.exp (-(ℓ / 2)) ^ N := by gcongr
      _ = Real.exp (N * (-(ℓ / 2))) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp (-(5 * U)) := by
          rw [Real.exp_le_exp]
          have : 10 * U ≤ N * ℓ := by rwa [div_le_iff₀ hℓ0] at hN1
          linarith
  have hn2 : (n : ℝ) + 2 ≤ Real.exp U := by
    have := Real.add_one_le_exp U; nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ((100 : ℝ) ^ N) ^ n * (2 * Real.exp (-(3 * U)) + n * q ^ N * Real.exp (Δ + U))
      ≤ Real.exp U * (2 * Real.exp (-(3 * U)) + n * Real.exp (-(5 * U)) * Real.exp (U + U)) := by
        gcongr
    _ = (2 + n) * Real.exp (-(2 * U)) := by
        have e1 : Real.exp U * Real.exp (-(3 * U)) = Real.exp (-(2 * U)) := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp U * Real.exp (-(5 * U)) * Real.exp (U + U) = Real.exp (-(2 * U)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        calc Real.exp U * (2 * Real.exp (-(3 * U)) + n * Real.exp (-(5 * U)) * Real.exp (U + U))
            = 2 * (Real.exp U * Real.exp (-(3 * U))) +
                n * (Real.exp U * Real.exp (-(5 * U)) * Real.exp (U + U)) := by ring
          _ = (2 + n) * Real.exp (-(2 * U)) := by rw [e1, e2]; ring
    _ ≤ Real.exp U * Real.exp (-(2 * U)) := by gcongr; linarith
    _ = Real.exp (-U) := by rw [← Real.exp_add]; ring_nf

/-- The Siegel count: the box of unknowns beats the cells. -/
lemma siegel_count {L c B : ℕ} {Δ U ν ε : ℝ} (hL : 1 ≤ L) (hU : 5 ≤ U) (hν : 0 ≤ ν)
    (hΔU : Δ ≤ U) (hB : B = ⌊Real.exp Δ⌋₊) (hε : ε = Real.exp (-(ν * U)))
    (hcnt : 2 * (c : ℝ) * ((ν + 3) * U) ≤ L * Δ) :
    (2 * ⌈(B : ℝ) * Real.exp U / ε⌉₊ + 2) ^ (2 * c) < (B + 1) ^ L := by
  have hε0 : 0 < ε := hε ▸ Real.exp_pos _
  have hB0 : (B : ℝ) ≤ Real.exp Δ := hB ▸ Nat.floor_le (Real.exp_pos Δ).le
  have hB1 : Real.exp Δ < (B : ℝ) + 1 := hB ▸ Nat.lt_floor_add_one _
  have hy0 : 0 ≤ (B : ℝ) * Real.exp U / ε := by positivity
  have hy : (B : ℝ) * Real.exp U / ε ≤ Real.exp ((ν + 2) * U) := by
    rw [div_le_iff₀ hε0, hε, ← Real.exp_add]
    have h1 : (B : ℝ) * Real.exp U ≤ Real.exp U * Real.exp U :=
      mul_le_mul_of_nonneg_right (hB0.trans (Real.exp_le_exp.mpr hΔU)) (Real.exp_pos U).le
    refine h1.trans (le_of_eq ?_)
    rw [← Real.exp_add]; ring_nf
  have he6 : 6 ≤ Real.exp U := by have := Real.add_one_le_exp U; linarith
  set E : ℝ := Real.exp ((ν + 2) * U)
  have h3 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hbase : ((2 * ⌈(B : ℝ) * Real.exp U / ε⌉₊ + 2 : ℕ) : ℝ) ≤ Real.exp ((ν + 3) * U) := by
    have h1 := Nat.ceil_lt_add_one hy0
    have h2 : Real.exp ((ν + 3) * U) = E * Real.exp U := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    push_cast
    have h4 : (⌈(B : ℝ) * Real.exp U / ε⌉₊ : ℝ) ≤ E + 1 := by linarith
    calc 2 * (⌈(B : ℝ) * Real.exp U / ε⌉₊ : ℝ) + 2 ≤ 2 * (E + 1) + 2 := by linarith
      _ ≤ E * 6 := by linarith
      _ ≤ E * Real.exp U := by gcongr
  have hreal : ((2 * ⌈(B : ℝ) * Real.exp U / ε⌉₊ + 2 : ℕ) : ℝ) ^ (2 * c) < ((B : ℝ) + 1) ^ L := by
    calc ((2 * ⌈(B : ℝ) * Real.exp U / ε⌉₊ + 2 : ℕ) : ℝ) ^ (2 * c)
        ≤ Real.exp ((ν + 3) * U) ^ (2 * c) := by gcongr
      _ = Real.exp (2 * c * ((ν + 3) * U)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (L * Δ) := Real.exp_le_exp.mpr hcnt
      _ = Real.exp Δ ^ L := by rw [← Real.exp_nat_mul]
      _ < ((B : ℝ) + 1) ^ L := pow_lt_pow_left₀ hB1 (Real.exp_pos Δ).le (by omega)
  exact_mod_cast hreal

/-- The count of conditions, from the hypothesis `c₂ U^{n+1} ≤ L Δ r^κ ℓ^n`. -/
lemma count_final {n κ K N L : ℕ} (hκ : κ ≤ n) {r ℓ U Δ ν : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ)
    (hN : (N : ℝ) ≤ 3 * (r * K)) (hK : r * K * ℓ ≤ 20 * U) (hU : 0 ≤ U) (hν : 0 ≤ ν)
    (hc₂ : 2 * (ν + 3) * 60 ^ n * U ^ (n + 1) ≤ L * Δ * r ^ κ * ℓ ^ n) :
    2 * ((K ^ κ * N ^ (n - κ) : ℕ) : ℝ) * ((ν + 3) * U) ≤ L * Δ := by
  have h1 := count_arith hκ hr hℓ hN hK
  set c : ℝ := ((K ^ κ * N ^ (n - κ) : ℕ) : ℝ)
  have hpos : 0 < r ^ κ * ℓ ^ n := by positivity
  have h2 : 2 * c * ((ν + 3) * U) * (r ^ κ * ℓ ^ n) ≤ L * Δ * (r ^ κ * ℓ ^ n) := by
    calc 2 * c * ((ν + 3) * U) * (r ^ κ * ℓ ^ n)
        = 2 * (ν + 3) * U * (c * r ^ κ * ℓ ^ n) := by ring
      _ ≤ 2 * (ν + 3) * U * (60 ^ n * U ^ n) := by gcongr
      _ = 2 * (ν + 3) * 60 ^ n * U ^ (n + 1) := by ring
      _ ≤ L * Δ * r ^ κ * ℓ ^ n := hc₂
      _ = L * Δ * (r ^ κ * ℓ ^ n) := by ring
  exact le_of_mul_le_mul_right h2 hpos

/-- Transfer by the multiplier: small on the condition set ⇒ small on the whole grid. -/
lemma grid_small {n L κ A K : ℕ} {a b r U ε : ℝ} (ψ : Fin L → (Fin n → ℂ) → ℂ) (p : Fin L → ℤ)
    (hK0 : K ≠ 0) (hr1 : 1 ≤ r) (hAK : (A : ℝ) / K ≤ r) (hb0 : 0 ≤ b) (hbU : b * r ^ 2 ≤ a * U)
    (hQP : QuasiPeriodicB κ b ψ)
    (hS : ∀ k ∈ condIdx n κ K (2 * A + 1), ‖∑ l, (p l : ℂ) * ψ l (condPt κ A K k)‖ ≤ 2 * ε)
    (g : Fin n → ℂ) (hg : ∀ j, g j ∈ progNodes A K) :
    ‖∑ l, (p l : ℂ) * ψ l g‖ ≤ Real.exp (9 * a * U) * (2 * ε) := by
  obtain ⟨k, hk, q, hq0, rfl, hqn⟩ := grid_decomp (κ := κ) hK0 hg
  obtain ⟨μ, hμ, hψq⟩ := hQP q hq0 (condPt κ A K k)
  have hmul : ∑ l, (p l : ℂ) * ψ l (condPt κ A K k + fun i => (q i : ℂ)) =
      μ * ∑ l, (p l : ℂ) * ψ l (condPt κ A K k) := by
    simp only [hψq, mul_sum]
    exact sum_congr rfl fun l _ => by ring
  have hs : ‖condPt κ A K k‖ ≤ r := norm_condPt_le hK0 rfl hk hr1 hAK
  have hμ' : ‖μ‖ ≤ Real.exp (9 * a * U) := by
    refine hμ.trans (Real.exp_le_exp.mpr ?_)
    set u : ℝ := ‖condPt κ A K k‖ + ‖(fun i => (q i : ℂ))‖
    have h1 : u ≤ 3 * r := by simp only [u]; linarith
    have h0 : 0 ≤ u := by positivity
    have h2 : u ^ 2 ≤ 9 * r ^ 2 := by nlinarith
    calc b * u ^ 2 ≤ b * (9 * r ^ 2) := by gcongr
      _ = 9 * (b * r ^ 2) := by ring
      _ ≤ 9 * (a * U) := by gcongr
      _ = 9 * a * U := by ring
  rw [hmul, norm_mul]
  exact mul_le_mul hμ' (hS k hk) (norm_nonneg _) (Real.exp_pos _).le

/-- The bound on the polydisc of radius `R`. -/
lemma norm_combo_le {n L B : ℕ} {Δ U R : ℝ} (ψ : Fin L → (Fin n → ℂ) → ℂ) (p : Fin L → ℤ)
    (hpB : ∀ l, |p l| ≤ B) (hB : (B : ℝ) ≤ Real.exp Δ)
    (hψR : ∀ z, ‖z‖ ≤ R → ∑ l, ‖ψ l z‖ ≤ Real.exp U) (z : Fin n → ℂ) (hz : ‖z‖ ≤ R) :
    ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ Real.exp (Δ + U) := by
  have hpl : ∀ l, ‖(p l : ℂ)‖ ≤ Real.exp Δ := fun l => by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact (show ((|p l| : ℤ) : ℝ) ≤ B by exact_mod_cast hpB l).trans hB
  calc ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ ∑ l, ‖(p l : ℂ) * ψ l z‖ := norm_sum_le _ _
    _ ≤ ∑ l, Real.exp Δ * ‖ψ l z‖ := by
        gcongr with l; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hpl l) (norm_nonneg _)
    _ = Real.exp Δ * ∑ l, ‖ψ l z‖ := by rw [mul_sum]
    _ ≤ Real.exp Δ * Real.exp U := by gcongr; exact hψR z hz
    _ = Real.exp (Δ + U) := by rw [Real.exp_add]

/-- `2r/(R − r) ≤ e^{−ℓ/2}` for `ℓ = log (R/r) ≥ 6`. -/
lemma q_le {r R : ℝ} (hr : 0 < r) (hR : 4 * r ≤ R) (hℓ : 6 ≤ Real.log (R / r)) :
    2 * r / (R - r) ≤ Real.exp (-(Real.log (R / r) / 2)) := by
  set ℓ := Real.log (R / r)
  have hR0 : 0 < R := by linarith
  have hRr_eq : R / r = Real.exp ℓ := (Real.exp_log (by positivity)).symm
  have h1 : 2 * r / (R - r) ≤ 4 * r / R := by
    rw [div_le_div_iff₀ (by linarith) hR0]; nlinarith
  have h2 : 4 * r / R = 4 * Real.exp (-ℓ) := by
    rw [Real.exp_neg, ← hRr_eq]; field_simp
  have h4 : 4 ≤ Real.exp (ℓ / 2) := by have := Real.add_one_le_exp (ℓ / 2); linarith
  have h5 : Real.exp (-ℓ) = Real.exp (-(ℓ / 2)) * Real.exp (-(ℓ / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have h6 : Real.exp (ℓ / 2) * Real.exp (-(ℓ / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : 4 * Real.exp (-ℓ) ≤ Real.exp (-(ℓ / 2)) := by
    rw [h5]; nlinarith [Real.exp_pos (-(ℓ / 2))]
  linarith

/-- The parameters `K`, `A` of the grid. -/
lemma exists_params {r ℓ U : ℝ} (hr1 : 1 ≤ r) (hℓ0 : 0 < ℓ) (hU : r * ℓ ≤ U) :
    ∃ K A : ℕ, 1 ≤ A ∧ (A : ℝ) ≤ r * K ∧ r * K < A + 1 ∧ 10 * U / ℓ ≤ r * K ∧
      r * K * ℓ ≤ 20 * U := by
  have hr0 : 0 < r := by linarith
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 10 * U / (r * ℓ) := ⟨_, rfl⟩
  have hx1 : 10 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]; nlinarith
  have hxK : x ≤ ⌈x⌉₊ := Nat.le_ceil x
  refine ⟨⌈x⌉₊, ⌊r * ⌈x⌉₊⌋₊, ?_, Nat.floor_le (by positivity), Nat.lt_floor_add_one _, ?_, ?_⟩
  · have : (1 : ℝ) ≤ r * ⌈x⌉₊ := by nlinarith
    exact Nat.le_floor (by exact_mod_cast this)
  · calc 10 * U / ℓ = r * x := by rw [hx]; field_simp
      _ ≤ r * ⌈x⌉₊ := by gcongr
  · have hKx : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
      have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x); linarith
    calc r * ⌈x⌉₊ * ℓ ≤ r * (2 * x) * ℓ := by gcongr
      _ = 20 * U := by rw [hx]; field_simp; ring

/-- **W83 Prop. 2.1 (+ Remark p. 636) for periods `e_1, …, e_κ` of `ℂⁿ`, single multiplier
constant `b` with `b r² ≤ a U`.** -/
theorem prop21B (n κ : ℕ) (hκ : κ ≤ n) (a : ℝ) (ha : 0 ≤ a) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L : ℕ) (b Δ U R r : ℝ) (ψ : Fin L → (Fin n → ℂ) → ℂ),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → r * Real.log (R / r) ≤ U →
      0 ≤ b → b * r ^ 2 ≤ a * U →
      (∀ l, Differentiable ℂ (ψ l)) → (∀ z, ‖z‖ ≤ R → ∑ l, ‖ψ l z‖ ≤ Real.exp U) →
      QuasiPeriodicB κ b ψ →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ Real.exp (-U) := by
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = 3 + 9 * a := ⟨_, rfl⟩
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  refine ⟨Real.exp (6000 * ((n : ℝ) + 1)), 2 * (ν + 3) * 60 ^ n, Real.exp_pos _,
    by positivity, ?_⟩
  intro L b Δ U R r ψ hL hΔ hΔU hRr hr hU hb0 hbU hψd hψR hQP hc₂
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 6000 * ((n : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hX] at hRr hr
  have hX0 : 6000 ≤ X := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [hX]; nlinarith
  have hexpX : X + 1 ≤ Real.exp X := Real.add_one_le_exp X
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := by
    have : 0 < R / r := by linarith
    exact (div_pos_iff_of_pos_right hr0).mp this
  have hRr4 : 4 * r ≤ R := by
    have : 4 ≤ R / r := by linarith
    rw [le_div_iff₀ hr0] at this; linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log (R / r) := ⟨_, rfl⟩
  rw [← hℓdef] at hU hc₂
  have hℓX : X ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp X]
    exact Real.log_le_log (Real.exp_pos X) hRr
  have hℓ0 : 0 < ℓ := by linarith
  have hUℓ : ℓ ≤ U := le_trans (le_mul_of_one_le_left hℓ0.le hr1) hU
  have hUX : X ≤ U := hℓX.trans hUℓ
  have hU0 : 0 < U := by linarith
  -- the grid
  obtain ⟨K, A, hA1, hA_le, hA_lt, hrK, hrKℓ⟩ := exists_params hr1 hℓ0 hU
  obtain ⟨hK0, hcard, hZr, hΛr, hΛR, hC⟩ := prog_constants hA1 hr0 hA_le hA_lt hRr4
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0
  have hrK1 : 1 ≤ r * K := by
    have : 10 ≤ 10 * U / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
    linarith
  have hNeq : ((2 * A + 1 : ℕ) : ℝ) = 2 * A + 1 := by push_cast; ring
  have hN_lo : 10 * U / ℓ ≤ ((2 * A + 1 : ℕ) : ℝ) := by rw [hNeq]; linarith
  have hN_hi : ((2 * A + 1 : ℕ) : ℝ) ≤ 3 * (r * K) := by rw [hNeq]; linarith
  have hN_hi' : ((2 * A + 1 : ℕ) : ℝ) ≤ 60 * U / ℓ := by
    rw [le_div_iff₀ hℓ0]
    have := mul_le_mul_of_nonneg_right hN_hi hℓ0.le
    linarith
  have hAK : (A : ℝ) / K ≤ r := by rw [div_le_iff₀ hKpos]; linarith
  -- Siegel's lemma on the condition set
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = ⌊Real.exp Δ⌋₊ := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = Real.exp (-(ν * U)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ Real.exp_pos _
  let J : Finset (Fin n → ℕ) := condIdx n κ K (2 * A + 1)
  let a' : J → Fin L → ℂ := fun k l => ψ l (condPt κ A K k.1)
  have hY : ∀ k : J, ∑ l, ‖a' k l‖ ≤ Real.exp U := fun k =>
    hψR _ ((norm_condPt_le hK0 rfl k.2 hr1 hAK).trans (by linarith))
  have hcardJ : Fintype.card J = K ^ κ * (2 * A + 1) ^ (n - κ) := by
    rw [Fintype.card_coe]; exact card_condIdx hκ K _
  have hcnt := count_final (L := L) (Δ := Δ) hκ hr0 hℓ0 hN_hi hrKℓ hU0.le hν0 hc₂
  rw [← hcardJ] at hcnt
  have hcount := siegel_count hL (by linarith) hν0 hΔU hB hε hcnt
  obtain ⟨p, hp0, hpB, hpS⟩ := siegel_approx a' B hε0 hY hcount
  have hBΔ : (B : ℝ) ≤ Real.exp Δ := hB ▸ Nat.floor_le (Real.exp_pos Δ).le
  refine ⟨p, hp0, fun l => ?_, ?_⟩
  · have h1 : |(p l : ℝ)| ≤ B := by
      rw [← Int.cast_abs]; exact_mod_cast hpB l
    exact h1.trans hBΔ
  -- the auxiliary function is small on the grid
  have hgrid : ∀ g : Fin n → ℂ, (∀ j, g j ∈ progNodes A K) →
      ‖∑ l, (p l : ℂ) * ψ l g‖ ≤ 2 * Real.exp (-(3 * U)) := by
    intro g hg
    refine (grid_small ψ p hK0 hr1 hAK hb0 hbU hQP (fun k hk => hpS ⟨k, hk⟩) g hg).trans
      (le_of_eq ?_)
    rw [hε, mul_left_comm, ← Real.exp_add, hν]; ring_nf
  -- interpolation on the grid
  intro z hz
  have hC1 : (1 : ℝ) ≤ 100 ^ (2 * A + 1) := one_le_pow₀ (by norm_num)
  have hΨd : Differentiable ℂ (fun z => ∑ l, (p l : ℂ) * ψ l z) :=
    Differentiable.fun_sum fun l _ => (hψd l).const_mul _
  have hint := grid_interp (fun z => ∑ l, (p l : ℂ) * ψ l z) hΨd (progNodes A K) hr0.le
    (by linarith) hZr hΛr hΛR hC hC1 (by positivity) (Real.exp_pos _).le hgrid
    (norm_combo_le ψ p hpB hBΔ hψR) hz
  rw [hcard] at hint
  have hq := q_le hr0 hRr4 (by rw [← hℓdef]; linarith)
  rw [← hℓdef] at hq
  have hq0 : 0 ≤ 2 * r / (R - r) := div_nonneg (by linarith) (by linarith)
  exact hint.trans (final_arith (hX ▸ hUX) (hX ▸ hℓX) hN_lo hN_hi' hq0 hq hΔU)

/-- **W83 Prop. 2.1 (+ Remark p. 636) for periods `e_1, …, e_κ` of `ℂⁿ`.** -/
theorem prop21 (n κ : ℕ) (hκ : κ ≤ n) (a : ℝ) (ha : 0 ≤ a) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L D : ℕ) (Δ U R r : ℝ) (ψ : Fin L → (Fin n → ℂ) → ℂ),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → r * Real.log (R / r) ≤ U →
      (D : ℝ) * r ^ 2 ≤ U →
      (∀ l, Differentiable ℂ (ψ l)) → (∀ z, ‖z‖ ≤ R → ∑ l, ‖ψ l z‖ ≤ Real.exp U) →
      QuasiPeriodic κ a D ψ →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ Real.exp (-U) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := prop21B n κ hκ a ha
  refine ⟨c₁, c₂, hc₁, hc₂, fun L D Δ U R r ψ hL hΔ hΔU hRr hr hU hDU hψd hψR hQP hc => ?_⟩
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  exact h L (a * D) Δ U R r ψ hL hΔ hΔU hRr hr hU (by positivity)
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hDU ha) hψd hψR hQP hc

end LSG.Aux
