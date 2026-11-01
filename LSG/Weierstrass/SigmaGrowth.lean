/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.SigmaQuasiPeriod
import LSG.Weierstrass.SigmaGrowthBasic

/-!
# `σ` has order two

Write `z = x + m ω₁ + n ω₂` with `x` in the closed fundamental parallelogram and iterate the
quasi-periodicity `σ(z ± ωᵢ) = -exp (± ηᵢ (z ± ωᵢ/2)) σ(z)`: each step costs a factor
`exp (A (1 + ‖z‖))`, and `|m|, |n| = O(1 + ‖z‖)`, so `‖σ(z)‖ ≤ exp (C (1 + ‖z‖)²)`.
The Cauchy estimates then give the same for `σ'`, `σ''`, `σ'''`.

## Main results
* `LSG.Weierstrass.growthLE_sigma`: `GrowthLE 2 (sigma L)`.
* `LSG.Weierstrass.growthLE_deriv_sigma` (and `_deriv_deriv_`, `_deriv_deriv_deriv_`).
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

/-! ### Iterating a one-step bound -/

/-- If `‖f (z + ω)‖ ≤ exp (A (1 + ‖z‖)) ‖f z‖` for all `z`, then
`‖f (z + k ω)‖ ≤ exp (A k (1 + ‖z‖ + k ‖ω‖)) ‖f z‖`. -/
lemma norm_add_nat_mul_le {f : ℂ → ℂ} {ω : ℂ} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ z, ‖f (z + ω)‖ ≤ Real.exp (A * (1 + ‖z‖)) * ‖f z‖) (k : ℕ) (z : ℂ) :
    ‖f (z + k * ω)‖ ≤ Real.exp (A * k * (1 + ‖z‖ + k * ‖ω‖)) * ‖f z‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z + ((k + 1 : ℕ) : ℂ) * ω = (z + k * ω) + ω := by push_cast; ring
    have hn : ‖z + k * ω‖ ≤ ‖z‖ + k * ‖ω‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_natCast]
    rw [e]
    refine (h _).trans ?_
    calc Real.exp (A * (1 + ‖z + k * ω‖)) * ‖f (z + k * ω)‖
        ≤ Real.exp (A * (1 + (‖z‖ + k * ‖ω‖))) *
            (Real.exp (A * k * (1 + ‖z‖ + k * ‖ω‖)) * ‖f z‖) := by
          gcongr
      _ = Real.exp (A * (k + 1) * (1 + ‖z‖ + k * ‖ω‖)) * ‖f z‖ := by
          rw [← mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (A * ((k + 1 : ℕ) : ℝ) * (1 + ‖z‖ + ((k + 1 : ℕ) : ℝ) * ‖ω‖)) * ‖f z‖ := by
          push_cast
          gcongr
          linarith

/-- Integer version of `norm_add_nat_mul_le`, given one-step bounds in both directions. -/
lemma norm_add_int_mul_le {f : ℂ → ℂ} {ω : ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hplus : ∀ z, ‖f (z + ω)‖ ≤ Real.exp (A * (1 + ‖z‖)) * ‖f z‖)
    (hminus : ∀ z, ‖f (z - ω)‖ ≤ Real.exp (A * (1 + ‖z‖)) * ‖f z‖) (m : ℤ) (z : ℂ) :
    ‖f (z + m * ω)‖ ≤ Real.exp (A * m.natAbs * (1 + ‖z‖ + m.natAbs * ‖ω‖)) * ‖f z‖ := by
  rcases Int.natAbs_eq m with hm | hm
  · rw [hm]
    simpa using norm_add_nat_mul_le hA hplus m.natAbs z
  · have hminus' : ∀ z, ‖f (z + -ω)‖ ≤ Real.exp (A * (1 + ‖z‖)) * ‖f z‖ := by
      simpa [← sub_eq_add_neg] using hminus
    have := norm_add_nat_mul_le hA hminus' m.natAbs z
    rw [norm_neg] at this
    have hc : (m : ℂ) = -(m.natAbs : ℂ) := by
      rw [show (m : ℂ) = ((-(m.natAbs : ℤ) : ℤ) : ℂ) from congrArg _ hm, Int.cast_neg,
        Int.cast_natCast]
    have e : z + (m : ℂ) * ω = z + (m.natAbs : ℂ) * -ω := by rw [hc]; ring
    rw [e]
    exact this

/-! ### Decomposition of a point modulo the lattice -/

variable (L : PeriodPair)

/-- Every `z` is `x + m ω₁ + n ω₂` with `‖x‖ ≤ ‖ω₁‖ + ‖ω₂‖` and `|m|, |n| ≤ B (1 + ‖z‖)`. -/
lemma exists_decomp : ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, ∃ m n : ℤ,
    ‖z - m * L.ω₁ - n * L.ω₂‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ ∧
    (m.natAbs : ℝ) ≤ B * (1 + ‖z‖) ∧ (n.natAbs : ℝ) ≤ B * (1 + ‖z‖) := by
  let c : Fin 2 → (ℂ →L[ℝ] ℝ) := fun i ↦ LinearMap.toContinuousLinearMap (L.basis.coord i)
  refine ⟨‖c 0‖ + ‖c 1‖ + 1, by positivity, fun z ↦ ?_⟩
  set a := L.basis.repr z 0
  set b := L.basis.repr z 1
  have hz : z = (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ := by
    conv_lhs => rw [← L.basis.sum_repr z]
    simp [Fin.sum_univ_two, a, b, Complex.real_smul]
  have ha : |a| ≤ ‖c 0‖ * ‖z‖ := by
    have := (c 0).le_opNorm z
    simpa [c, a, Real.norm_eq_abs] using this
  have hb : |b| ≤ ‖c 1‖ * ‖z‖ := by
    have := (c 1).le_opNorm z
    simpa [c, b, Real.norm_eq_abs] using this
  have hfl : ∀ t : ℝ, ((⌊t⌋).natAbs : ℝ) ≤ |t| + 1 := by
    intro t
    rw [Nat.cast_natAbs, Int.cast_abs]
    have h1 := Int.floor_le t
    have h2 := Int.sub_one_lt_floor t
    rw [abs_le]
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  refine ⟨⌊a⌋, ⌊b⌋, ?_, ?_, ?_⟩
  · have hx : z - (⌊a⌋ : ℤ) * L.ω₁ - (⌊b⌋ : ℤ) * L.ω₂ =
        ((Int.fract a : ℝ) : ℂ) * L.ω₁ + ((Int.fract b : ℝ) : ℂ) * L.ω₂ := by
      rw [hz]; simp only [Int.fract]; push_cast; ring
    rw [hx]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg a), abs_of_nonneg (Int.fract_nonneg b)]
    have := Int.fract_lt_one a
    have := Int.fract_lt_one b
    have := Int.fract_nonneg a
    have := Int.fract_nonneg b
    nlinarith [norm_nonneg L.ω₁, norm_nonneg L.ω₂]
  · refine (hfl a).trans ?_
    have : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [norm_nonneg (c 0), norm_nonneg (c 1)]
  · refine (hfl b).trans ?_
    have : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [norm_nonneg (c 0), norm_nonneg (c 1)]

/-! ### One-step bounds for `σ` -/

lemma norm_exp_le (w : ℂ) : ‖exp w‖ ≤ Real.exp ‖w‖ := Complex.norm_exp_le_exp_norm w

/-- The one-step constant for `ω` with `ω/2 ∉ Λ`. -/
lemma norm_sigma_add_le {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) (z : ℂ) :
    ‖sigma L (z + ω)‖ ≤ Real.exp (‖eta L ω‖ * (1 + ‖ω‖) * (1 + ‖z‖)) * ‖sigma L z‖ := by
  rw [sigma_add_of_half_notMem L hω hω2, norm_mul, norm_neg]
  gcongr
  refine (norm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
  rw [norm_mul]
  have h1 : ‖z + ω / 2‖ ≤ ‖z‖ + ‖ω‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_ofNat]
    linarith [norm_nonneg ω]
  have h2 : ‖z‖ + ‖ω‖ ≤ (1 + ‖ω‖) * (1 + ‖z‖) := by
    nlinarith [norm_nonneg z, norm_nonneg ω]
  calc ‖eta L ω‖ * ‖z + ω / 2‖ ≤ ‖eta L ω‖ * ((1 + ‖ω‖) * (1 + ‖z‖)) := by
        gcongr; exact h1.trans h2
    _ = _ := by ring

lemma norm_sigma_sub_le {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) (z : ℂ) :
    ‖sigma L (z - ω)‖ ≤ Real.exp (‖eta L ω‖ * (1 + ‖ω‖) * (1 + ‖z‖)) * ‖sigma L z‖ := by
  rw [sigma_sub_of_half_notMem L hω hω2, norm_mul, norm_neg]
  gcongr
  refine (norm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
  rw [norm_neg, norm_mul]
  have h1 : ‖z - ω / 2‖ ≤ ‖z‖ + ‖ω‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, Complex.norm_ofNat]
    linarith [norm_nonneg ω]
  have h2 : ‖z‖ + ‖ω‖ ≤ (1 + ‖ω‖) * (1 + ‖z‖) := by
    nlinarith [norm_nonneg z, norm_nonneg ω]
  calc ‖eta L ω‖ * ‖z - ω / 2‖ ≤ ‖eta L ω‖ * ((1 + ‖ω‖) * (1 + ‖z‖)) := by
        gcongr; exact h1.trans h2
    _ = _ := by ring

/-! ### The growth bound -/

/-- **`σ` has order at most two**: `‖σ(z)‖ ≤ exp (C (1 + ‖z‖)²)`. -/
theorem growthLE_sigma : GrowthLE 2 (sigma L) := by
  obtain ⟨B, hB, hdec⟩ := exists_decomp L
  set R := ‖L.ω₁‖ + ‖L.ω₂‖
  set P := ‖L.ω₁‖ + ‖L.ω₂‖
  set A := ‖eta L L.ω₁‖ * (1 + ‖L.ω₁‖) + ‖eta L L.ω₂‖ * (1 + ‖L.ω₂‖)
  have hA : 0 ≤ A := by positivity
  have hP : 0 ≤ P := by positivity
  -- one-step bounds with the common constant `A`
  have step : ∀ (ω : ℂ), ω ∈ L.lattice → ω / 2 ∉ L.lattice → ‖eta L ω‖ * (1 + ‖ω‖) ≤ A →
      ∀ m : ℤ, ∀ z, ‖sigma L (z + m * ω)‖ ≤
        Real.exp (A * m.natAbs * (1 + ‖z‖ + m.natAbs * ‖ω‖)) * ‖sigma L z‖ := by
    intro ω hω hω2 hle
    refine norm_add_int_mul_le hA (fun z ↦ (norm_sigma_add_le L hω hω2 z).trans ?_)
      (fun z ↦ (norm_sigma_sub_le L hω hω2 z).trans ?_)
    all_goals gcongr
  have step₁ := step L.ω₁ L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice
    (le_add_of_nonneg_right (by positivity))
  have step₂ := step L.ω₂ L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice
    (le_add_of_nonneg_left (by positivity))
  -- bound on the fundamental region
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (differentiable_sigma L).continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Metric.mem_closedBall_self (by positivity)))
  refine growthLE_two_of (A * B * (1 + R + 2 * B * P) + A * B * (1 + R + B * P) + M) fun z ↦ ?_
  obtain ⟨m, n, hx, hm, hn⟩ := hdec z
  set x := z - m * L.ω₁ - n * L.ω₂
  set T := 1 + ‖z‖
  have hT : 1 ≤ T := by simp [T]
  have hxM : ‖sigma L x‖ ≤ M := hM x (by simpa using hx)
  have hz : z = (x + m * L.ω₁) + n * L.ω₂ := by simp only [x]; ring
  have hxm : ‖x + m * L.ω₁‖ ≤ R + B * T * P := by
    refine (norm_add_le _ _).trans ?_
    have hcast : |(m : ℝ)| = (m.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [norm_mul, Complex.norm_intCast, hcast]
    have : ‖L.ω₁‖ ≤ P := le_add_of_nonneg_right (norm_nonneg _)
    have := mul_le_mul hm this (norm_nonneg _) (by positivity)
    linarith
  have hω₂ : ‖L.ω₂‖ ≤ P := le_add_of_nonneg_left (norm_nonneg _)
  have hω₁ : ‖L.ω₁‖ ≤ P := le_add_of_nonneg_right (norm_nonneg _)
  -- exponents
  have E2 : A * n.natAbs * (1 + ‖x + m * L.ω₁‖ + n.natAbs * ‖L.ω₂‖) ≤
      A * B * (1 + R + 2 * B * P) * T ^ 2 := by
    have h1 : (1 + ‖x + m * L.ω₁‖ + n.natAbs * ‖L.ω₂‖) ≤ (1 + R + 2 * B * P) * T := by
      have := mul_le_mul hn hω₂ (norm_nonneg _) (by positivity)
      have hRP : 0 ≤ 1 + R := by positivity
      nlinarith
    calc A * n.natAbs * (1 + ‖x + m * L.ω₁‖ + n.natAbs * ‖L.ω₂‖)
        ≤ A * (B * T) * ((1 + R + 2 * B * P) * T) := by
          gcongr
      _ = A * B * (1 + R + 2 * B * P) * T ^ 2 := by ring
  have E1 : A * m.natAbs * (1 + ‖x‖ + m.natAbs * ‖L.ω₁‖) ≤
      A * B * (1 + R + B * P) * T ^ 2 := by
    have h1 : (1 + ‖x‖ + m.natAbs * ‖L.ω₁‖) ≤ (1 + R + B * P) * T := by
      have := mul_le_mul hm hω₁ (norm_nonneg _) (by positivity)
      have hRP : 0 ≤ 1 + R := by positivity
      nlinarith
    calc A * m.natAbs * (1 + ‖x‖ + m.natAbs * ‖L.ω₁‖)
        ≤ A * (B * T) * ((1 + R + B * P) * T) := by
          gcongr
      _ = A * B * (1 + R + B * P) * T ^ 2 := by ring
  have E0 : M ≤ Real.exp (M * T ^ 2) := by
    have := Real.add_one_le_exp (M * T ^ 2)
    have : M ≤ M * T ^ 2 := le_mul_of_one_le_right hM0 (one_le_pow₀ hT)
    linarith
  rw [hz]
  calc ‖sigma L (x + m * L.ω₁ + n * L.ω₂)‖
      ≤ Real.exp (A * n.natAbs * (1 + ‖x + m * L.ω₁‖ + n.natAbs * ‖L.ω₂‖)) *
          ‖sigma L (x + m * L.ω₁)‖ := step₂ n _
    _ ≤ Real.exp (A * n.natAbs * (1 + ‖x + m * L.ω₁‖ + n.natAbs * ‖L.ω₂‖)) *
          (Real.exp (A * m.natAbs * (1 + ‖x‖ + m.natAbs * ‖L.ω₁‖)) * ‖sigma L x‖) := by
        gcongr; exact step₁ m x
    _ ≤ Real.exp (A * B * (1 + R + 2 * B * P) * T ^ 2) *
          (Real.exp (A * B * (1 + R + B * P) * T ^ 2) * Real.exp (M * T ^ 2)) := by
        gcongr
        exact hxM.trans E0
    _ = Real.exp ((A * B * (1 + R + 2 * B * P) + A * B * (1 + R + B * P) + M) * T ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf

theorem growthLE_deriv_sigma : GrowthLE 2 (deriv (sigma L)) :=
  growthLE_deriv (differentiable_sigma L) (growthLE_sigma L)

theorem growthLE_deriv_deriv_sigma : GrowthLE 2 (deriv (deriv (sigma L))) :=
  growthLE_deriv_deriv (differentiable_sigma L) (growthLE_sigma L)

theorem growthLE_deriv_deriv_deriv_sigma : GrowthLE 2 (deriv (deriv (deriv (sigma L)))) :=
  growthLE_deriv_deriv_deriv (differentiable_sigma L) (growthLE_sigma L)

end LSG.Weierstrass
