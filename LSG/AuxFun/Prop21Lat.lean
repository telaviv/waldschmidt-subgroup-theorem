/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Prop21
import LSG.AuxFun.Grid2
import LSG.AuxFun.Reps2

/-!
# W83 Prop. 2.1 for periods in a product of lattices (Tier 2)

Coordinates `ℂⁿ`, lattices `ℤα_j + ℤβ_j` (`Im(ᾱ_j β_j) ≠ 0`), periods
`ω_i = perVec α β (P i)` (`i < κ`) with integer coordinates `P i`, of rank `κ` in the sense that a
`κ × κ` minor `M = minorMat P I` has `det M ≠ 0`. The periods may be `ℂ`-linearly dependent
(e.g. `ϖ` and `iϖ` in one CM coordinate), and `κ ≤ 2n`.

This is W83 Prop. 2.1 with its hypothesis `U ≥ r² log(R/r)`, in the coordinates of
`STAGE3_D2.md` (O2, Tier 2): for the abelian class of `LSG/W88/Statement.lean`, `n` coordinate
forms of `T_G` restricted to `V` map the periods into `Π (0 | 2πiℤ | Λ_j)`, and every factor can be
completed to a lattice (`2πiℤ ⊂ ℤ + 2πiℤ`, `0 ⊂ ℤ + iℤ`).

Proof: as `prop21B`, with the lattice grids of `Lattice2.lean` (`(2A+1)²` nodes per coordinate,
`A ≍ √(U/log(R/r))`), interpolation `grid_interp2`, and the representatives of `Reps2.lean`.

* `LSG.Aux.prop21Lat`.
-/

open Complex Finset

namespace LSG.Aux

/-- Grid parameters for Tier 2. -/
lemma exists_params2 {r ℓ U S : ℝ} (hr1 : 1 ≤ r) (hℓ0 : 0 < ℓ) (hU : r ^ 2 * ℓ ≤ U)
    (hS : 1 ≤ S) :
    ∃ A K : ℕ, 1 ≤ A ∧ K ≠ 0 ∧ S * A / K ≤ r ∧ r * K ≤ 2 * S * A ∧
      10 * U / ℓ ≤ (((2 * A + 1) ^ 2 : ℕ) : ℝ) ∧ (((2 * A + 1) ^ 2 : ℕ) : ℝ) ≤ 360 * U / ℓ ∧
      (A : ℝ) ^ 2 ≤ 40 * U / ℓ := by
  have hr0 : 0 < r := by linarith
  set y : ℝ := Real.sqrt (10 * U / ℓ) with hy
  have hU0 : 0 ≤ 10 * U / ℓ := by
    have : 0 ≤ U := le_trans (by positivity) hU
    positivity
  have hy2 : y ^ 2 = 10 * U / ℓ := Real.sq_sqrt hU0
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hyr : r ≤ y := by
    have h1 : r ^ 2 ≤ y ^ 2 := by
      rw [hy2, le_div_iff₀ hℓ0]; nlinarith
    exact (pow_le_pow_iff_left₀ hr0.le hy0 two_ne_zero).mp h1
  have hy1 : 1 ≤ y := hr1.trans hyr
  set A : ℕ := ⌈y⌉₊
  have hyA : y ≤ A := Nat.le_ceil y
  have hAy : (A : ℝ) ≤ 2 * y := by
    have := Nat.ceil_lt_add_one hy0; linarith
  have hA1 : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith)
  have hA0 : (0 : ℝ) < A := by linarith
  set x : ℝ := S * A / r
  have hx1 : 1 ≤ x := by
    rw [le_div_iff₀ hr0]; nlinarith
  set K : ℕ := ⌈x⌉₊
  have hxK : x ≤ K := Nat.le_ceil x
  have hKx : (K : ℝ) ≤ 2 * x := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x); linarith
  have hK0 : K ≠ 0 := by
    intro h; rw [h] at hxK; simp at hxK; linarith
  have hKpos : (0 : ℝ) < K := by linarith
  have hNeq : (((2 * A + 1) ^ 2 : ℕ) : ℝ) = (2 * A + 1) ^ 2 := by push_cast; ring
  refine ⟨A, K, hA1, hK0, ?_, ?_, ?_, ?_, ?_⟩
  · have : S * A = r * x := by simp only [x]; field_simp
    rw [div_le_iff₀ hKpos, this]; exact mul_le_mul_of_nonneg_left hxK hr0.le
  · calc r * K ≤ r * (2 * x) := by gcongr
      _ = 2 * S * A := by simp only [x]; field_simp
  · rw [hNeq, ← hy2]; nlinarith
  · rw [hNeq, show 360 * U / ℓ = 36 * y ^ 2 by rw [hy2]; ring]; nlinarith
  · rw [show 40 * U / ℓ = 4 * y ^ 2 by rw [hy2]; ring]; nlinarith

/-- `2M ≤ 4^M`. -/
lemma two_mul_le_four_pow (M : ℕ) : 2 * M ≤ 4 ^ M := by
  have h := Nat.lt_two_pow_self (n := M)
  have : 4 ^ M = 2 ^ M * 2 ^ M := by rw [← mul_pow]; norm_num
  rw [this]
  have h1 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  nlinarith

/-- Combining the Lagrange constants. -/
lemma lag_C_le {M : ℕ} {G ρ q : ℝ} (hG : 1 ≤ G) (hρ : 0 ≤ ρ) (hq0 : 0 ≤ q) (hρq : ρ * q ≤ 4) :
    M * G ^ M + M * (G * ρ) ^ M * q ^ M ≤ (16 * G) ^ M := by
  have hG0 : 0 ≤ G := by linarith
  have h1 : (G * ρ) ^ M * q ^ M ≤ (4 * G) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith) M
  have h2 : G ^ M ≤ (4 * G) ^ M := by gcongr; linarith
  have h3 : (2 * M : ℝ) ≤ 4 ^ M := by exact_mod_cast two_mul_le_four_pow M
  calc (M : ℝ) * G ^ M + M * (G * ρ) ^ M * q ^ M
      = M * G ^ M + M * ((G * ρ) ^ M * q ^ M) := by ring
    _ ≤ M * (4 * G) ^ M + M * (4 * G) ^ M := by gcongr
    _ = (2 * M) * (4 * G) ^ M := by ring
    _ ≤ 4 ^ M * (4 * G) ^ M := by gcongr
    _ = (16 * G) ^ M := by rw [← mul_pow]; ring_nf

/-- Per-coordinate data of the lattice grid. -/
lemma lat_coord {α β : ℂ} (hD : ((starRingEnd ℂ) α * β).im ≠ 0) {A K : ℕ} (hA : 1 ≤ A)
    (hK : K ≠ 0) {r R S ci : ℝ} (hr : 0 < r) (hR : 4 * r ≤ R) (hs : ‖α‖ + ‖β‖ ≤ S)
    (hci : (‖α‖ + ‖β‖) / |((starRingEnd ℂ) α * β).im| ≤ ci) (hS1 : 1 ≤ S) (hci1 : 1 ≤ ci)
    (hSAK : S * A / K ≤ r) (hrK : r * K ≤ 2 * S * A) :
    (∀ ζ ∈ latNodes α β A K, ‖ζ‖ ≤ r) ∧
    (∀ ζ ∈ latNodes α β A K, ∀ w : ℂ, ‖w‖ ≤ r →
      ‖lagBasis (latNodes α β A K) ζ w‖ ≤ (3 * S * ci * Real.exp 2) ^ ((2 * A + 1) ^ 2)) ∧
    (∀ ζ ∈ latNodes α β A K, ∀ w : ℂ, ‖w‖ = R →
      ‖lagBasis (latNodes α β A K) ζ w‖ ≤
        (3 * S * ci * Real.exp 2 * (R / r)) ^ ((2 * A + 1) ^ 2)) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hDpos : 0 < |((starRingEnd ℂ) α * β).im| := abs_pos.mpr hD
  have hs0 : 0 < ‖α‖ + ‖β‖ := by
    rcases eq_or_ne α 0 with rfl | hα
    · simp at hD
    · have := norm_pos_iff.mpr hα; positivity
  have hRr : 1 ≤ R / r := by rw [le_div_iff₀ hr]; linarith
  have hR0 : 0 < R := by linarith
  -- `1 / c₀ ≤ ci`
  have hX : ∀ ρ : ℝ, 0 ≤ ρ →
      (ρ * K + (‖α‖ + ‖β‖) * A) / (|((starRingEnd ℂ) α * β).im| / (‖α‖ + ‖β‖) * A) ≤
        (ρ * K / A + S) * ci := by
    intro ρ hρ
    rw [div_le_iff₀ (by positivity)]
    have h1 : (‖α‖ + ‖β‖) ≤ ci * |((starRingEnd ℂ) α * β).im| := by
      rwa [div_le_iff₀ hDpos] at hci
    have e : (ρ * K / A + S) * ci * (|((starRingEnd ℂ) α * β).im| / (‖α‖ + ‖β‖) * A) =
        (ρ * K + S * A) * (ci * |((starRingEnd ℂ) α * β).im|) / (‖α‖ + ‖β‖) := by
      field_simp
    rw [e, le_div_iff₀ hs0]
    have h2 : 0 ≤ ρ * K := by positivity
    calc (ρ * K + (‖α‖ + ‖β‖) * A) * (‖α‖ + ‖β‖)
        ≤ (ρ * K + S * A) * (‖α‖ + ‖β‖) := by gcongr
      _ ≤ (ρ * K + S * A) * (ci * |((starRingEnd ℂ) α * β).im|) := by gcongr
  have hrKA : r * K / A ≤ 2 * S := by rw [div_le_iff₀ hA0]; linarith
  have hSci : 1 ≤ S * ci := one_le_mul_of_one_le_of_one_le hS1 hci1
  refine ⟨fun ζ hζ => ?_, fun ζ hζ w hw => ?_, fun ζ hζ w hw => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := mem_image.mp hζ
    refine (norm_lnode_le α β hp).trans ?_
    calc (‖α‖ + ‖β‖) * A / K ≤ S * A / K := by gcongr
      _ ≤ r := hSAK
  · obtain ⟨p, hp, rfl⟩ := mem_image.mp hζ
    refine (norm_lagBasis_lat_le hD hK hA hp hr.le hw).trans ?_
    gcongr
    refine max_le ?_ (by nlinarith [hSci])
    calc _ ≤ (r * K / A + S) * ci := hX r hr.le
      _ ≤ (2 * S + S) * ci := by gcongr
      _ = 3 * S * ci := by ring
  · obtain ⟨p, hp, rfl⟩ := mem_image.mp hζ
    refine (norm_lagBasis_lat_le hD hK hA hp hR0.le hw.le).trans ?_
    rw [show 3 * S * ci * Real.exp 2 * (R / r) = 3 * S * ci * (R / r) * Real.exp 2 by ring]
    gcongr
    refine max_le ?_ (by nlinarith [hSci])
    have hRK : R * K / A ≤ 2 * S * (R / r) := by
      calc R * K / A = (R / r) * (r * K / A) := by field_simp
        _ ≤ (R / r) * (2 * S) := by gcongr
        _ = 2 * S * (R / r) := by ring
    calc _ ≤ (R * K / A + S) * ci := hX R hR0.le
      _ ≤ (2 * S * (R / r) + S * (R / r)) * ci := by gcongr; nlinarith
      _ = 3 * S * ci * (R / r) := by ring

/-- The final numerical inequality, general base. -/
lemma final_arith2 {n Nn : ℕ} {U ℓ Δ q Bs : ℝ} (hBs : 1 ≤ Bs) (hU : (n : ℝ) + 2 ≤ U)
    (hℓ0 : 0 < ℓ) (hN1 : 10 * U / ℓ ≤ Nn) (hlog : n * Nn * Real.log Bs ≤ U)
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-(ℓ / 2))) (hΔ : Δ ≤ U) :
    (Bs ^ Nn) ^ n * (2 * Real.exp (-(3 * U)) + n * q ^ Nn * Real.exp (Δ + U)) ≤
      Real.exp (-U) := by
  have hB : (Bs ^ Nn) ^ n ≤ Real.exp U := by
    have he : (Bs ^ Nn) ^ n = Real.exp ((Nn * n : ℕ) * Real.log Bs) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith), ← pow_mul]
    rw [he, Real.exp_le_exp]; push_cast; linarith
  have hqN : q ^ Nn ≤ Real.exp (-(5 * U)) := by
    calc q ^ Nn ≤ Real.exp (-(ℓ / 2)) ^ Nn := by gcongr
      _ = Real.exp (Nn * (-(ℓ / 2))) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp (-(5 * U)) := by
          rw [Real.exp_le_exp]
          have : 10 * U ≤ Nn * ℓ := by rwa [div_le_iff₀ hℓ0] at hN1
          linarith
  have hn2 : (n : ℝ) + 2 ≤ Real.exp U := by
    have := Real.add_one_le_exp U; nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (Bs ^ Nn) ^ n * (2 * Real.exp (-(3 * U)) + n * q ^ Nn * Real.exp (Δ + U))
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

/-- The count of conditions for Tier 2. -/
lemma count_lat {n κ : ℕ} (hκ : κ ≤ 2 * n) {A K Kd Bn : ℕ} {r ℓ U S dd C : ℝ} (hr1 : 1 ≤ r)
    (hℓ0 : 0 < ℓ) (hS : 1 ≤ S) (hdd : 0 ≤ dd) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (hKd : (Kd : ℝ) = K * dd) (hBn : (Bn : ℝ) = A + C * (A + K)) (hrK : r * K ≤ 2 * S * A)
    (hA2 : (A : ℝ) ^ 2 ≤ 40 * U / ℓ) :
    ((Kd ^ κ * (2 * Bn + 1) ^ (2 * n - κ) : ℕ) : ℝ) * r ^ κ * ℓ ^ n ≤
      (2 * S * dd) ^ κ * (3 * (1 + 3 * C * S)) ^ (2 * n) * 40 ^ n * U ^ n := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hκ
  have hm' : 2 * n - κ = m := by omega
  rw [hm']
  have hr0 : 0 < r := by linarith
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hK : (K : ℝ) ≤ 2 * S * A := by nlinarith
  have hC4 : 1 ≤ 3 * (1 + 3 * C * S) := by nlinarith
  have hB : (2 * (Bn : ℝ) + 1) ≤ 3 * (1 + 3 * C * S) * A := by
    rw [hBn]
    have : C * (A + K) ≤ C * (3 * S * A) := by gcongr; nlinarith
    nlinarith
  have hKdr : (Kd : ℝ) * r ≤ 2 * S * dd * A := by rw [hKd]; nlinarith
  have hA2' : (A : ℝ) ^ 2 * ℓ ≤ 40 * U := by rwa [le_div_iff₀ hℓ0] at hA2
  push_cast
  have hB0 : (0 : ℝ) ≤ 2 * (Bn : ℝ) + 1 := by positivity
  calc (Kd : ℝ) ^ κ * (2 * (Bn : ℝ) + 1) ^ m * r ^ κ * ℓ ^ n
      = ((Kd : ℝ) * r) ^ κ * (2 * (Bn : ℝ) + 1) ^ m * ℓ ^ n := by ring
    _ ≤ (2 * S * dd * A) ^ κ * (3 * (1 + 3 * C * S) * A) ^ m * ℓ ^ n := by gcongr
    _ = (2 * S * dd) ^ κ * (3 * (1 + 3 * C * S)) ^ m * (A ^ (κ + m) * ℓ ^ n) := by
        rw [mul_pow (2 * S * dd) (A : ℝ) κ, mul_pow (3 * (1 + 3 * C * S)) (A : ℝ) m, pow_add]; ring
    _ = (2 * S * dd) ^ κ * (3 * (1 + 3 * C * S)) ^ m * ((A ^ 2 * ℓ) ^ n) := by
        rw [← hm, mul_pow (_ : ℝ) ℓ, ← pow_mul]
    _ ≤ (2 * S * dd) ^ κ * (3 * (1 + 3 * C * S)) ^ (2 * n) * ((40 * U) ^ n) := by
        gcongr
        omega
    _ = (2 * S * dd) ^ κ * (3 * (1 + 3 * C * S)) ^ (2 * n) * 40 ^ n * U ^ n := by
        rw [mul_pow]; ring

/-- Transfer by the multiplier for Tier 2. -/
lemma grid_small2 {n κ L A K : ℕ} {a b r U ε S C : ℝ} (α β : Fin n → ℂ)
    (P : Fin κ → Idx n → ℤ) (I : Fin κ → Idx n) (hd : (minorMat P I).det ≠ 0)
    (ψ : Fin L → (Fin n → ℂ) → ℂ) (p : Fin L → ℤ) (hK : K ≠ 0) (hr1 : 1 ≤ r)
    (hS0 : 0 ≤ S) (hS : ∀ j, ‖α j‖ + ‖β j‖ ≤ S) (hAK : (A : ℝ) / K ≤ r) (hC0 : 0 ≤ C)
    (hC : (C : ℝ) = ((cAdj P I * cP P : ℤ) : ℝ)) (hb0 : 0 ≤ b) (hbU : b * r ^ 2 ≤ a * U)
    (hQP : ∀ k : Fin κ → ℤ, ∀ z : Fin n → ℂ, ∃ m : ℂ,
      ‖m‖ ≤ Real.exp (b * (‖z‖ + ‖∑ i, (k i : ℂ) • perVec α β (P i)‖) ^ 2) ∧
      ∀ l, ψ l (z + ∑ i, (k i : ℂ) • perVec α β (P i)) = m * ψ l z)
    (Bn : ℕ) (hBn : (Bn : ℤ) = A + cAdj P I * cP P * (A + K))
    (hSc : ∀ s ∈ condIdx2 I ((K : ℤ) * (minorMat P I).det).natAbs Bn,
      ‖∑ l, (p l : ℂ) * ψ l (gpt α β K s)‖ ≤ 2 * ε)
    (g : Fin n → ℂ) (hg : ∀ j, g j ∈ latNodes (α j) (β j) A K) :
    ‖∑ l, (p l : ℂ) * ψ l g‖ ≤ Real.exp ((S * (1 + 4 * C)) ^ 2 * a * U) * (2 * ε) := by
  classical
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hr0 : 0 < r := by linarith
  choose pj hpj hpjg using fun j => mem_image.mp (hg j)
  set v : Idx n → ℤ := fun c => ((if c.2 = 0 then (pj c.1).1 else (pj c.1).2 : ℕ) : ℤ) - A
  have hgv : g = gpt α β K v := by
    rw [gpt_eq_lnode]; funext j; exact (hpjg j).symm
  have hv : ∀ c, |v c| ≤ A := by
    intro c
    have hb := hpj c.1
    simp only [latBox, mem_product, mem_range] at hb
    simp only [v]
    split_ifs <;> rw [abs_le] <;> constructor <;> omega
  obtain ⟨s, y, hvs, hsI, hsb, hxb⟩ := lat_decomp P I hd hK v hv
  set x : Idx n → ℤ := ∑ i, y i • P i with hx
  have hg' : g = gpt α β K s + ∑ i, (y i : ℂ) • perVec α β (P i) := by
    rw [hgv, hvs, gpt_add α β hK, perVec_sum]
  have hs_mem : s ∈ condIdx2 I ((K : ℤ) * (minorMat P I).det).natAbs Bn := by
    refine Fintype.mem_piFinset.mpr fun c => ?_
    split_ifs with hc
    · obtain ⟨t, -, rfl⟩ := mem_image.mp hc
      exact mem_Ico.mpr ⟨(hsI t).1, (hsI t).2⟩
    · have := hsb c
      rw [← hBn, abs_le] at this
      exact mem_Icc.mpr this
  obtain ⟨m, hm, hmψ⟩ := hQP y (gpt α β K s)
  have hmul : ∑ l, (p l : ℂ) * ψ l g = m * ∑ l, (p l : ℂ) * ψ l (gpt α β K s) := by
    rw [hg']
    simp only [hmψ, mul_sum]
    exact sum_congr rfl fun l _ => by ring
  -- norm bounds
  have hC' : ((cAdj P I : ℤ) : ℝ) * (cP P : ℝ) = C := by rw [hC]; push_cast; ring
  have hAK' : (A : ℝ) ≤ r * K := by rwa [div_le_iff₀ hKpos] at hAK
  have hKr : (K : ℝ) ≤ r * K := le_mul_of_one_le_left hKpos.le hr1
  set B : ℝ := A + C * (A + K)
  have hsB : ∀ c, |(s c : ℝ)| ≤ B := fun c => by
    have := hsb c
    have h' : ((|s c| : ℤ) : ℝ) ≤ ((A + cAdj P I * cP P * (A + K) : ℤ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    rw [hC'] at h'
    simpa [B] using h'
  have hgs : ‖gpt α β K s‖ ≤ S * (1 + 2 * C) * r := by
    refine (norm_gpt_le α β hK hS0 hS s (by positivity) hsB).trans ?_
    rw [div_le_iff₀ hKpos]
    have : S * B ≤ S * ((1 + 2 * C) * r * K) := by
      gcongr
      simp only [B]
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hAK' hKr) hC0]
    linarith
  have hxB : ∀ c, |(x c : ℝ)| ≤ C * (A + K) / K := fun c => by
    have := hxb c
    have h' : (((K : ℤ) * |x c| : ℤ) : ℝ) ≤ ((cAdj P I * cP P * (A + K) : ℤ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    rw [hC'] at h'
    rw [le_div_iff₀ hKpos]; linarith
  have hper : ‖∑ i, (y i : ℂ) • perVec α β (P i)‖ ≤ 2 * S * C * r := by
    rw [← perVec_sum]
    refine (norm_perVec_le α β hS0 hS x (by positivity) hxB).trans ?_
    have : C * (A + K) / K ≤ C * (r + 1) := by
      rw [div_le_iff₀ hKpos]
      nlinarith [mul_le_mul_of_nonneg_left hAK' hC0]
    calc S * (C * (A + K) / K) ≤ S * (C * (r + 1)) := by gcongr
      _ ≤ 2 * S * C * r := by
          have hSC := mul_nonneg hS0 hC0
          nlinarith [mul_le_mul_of_nonneg_left hr1 hSC]
  have hm' : ‖m‖ ≤ Real.exp ((S * (1 + 4 * C)) ^ 2 * a * U) := by
    refine hm.trans (Real.exp_le_exp.mpr ?_)
    set u := ‖gpt α β K s‖ + ‖∑ i, (y i : ℂ) • perVec α β (P i)‖
    have hu : u ≤ S * (1 + 4 * C) * r := by simp only [u]; linarith
    have hu0 : 0 ≤ u := by positivity
    calc b * u ^ 2 ≤ b * (S * (1 + 4 * C) * r) ^ 2 := by gcongr
      _ = (S * (1 + 4 * C)) ^ 2 * (b * r ^ 2) := by ring
      _ ≤ (S * (1 + 4 * C)) ^ 2 * (a * U) := by gcongr
      _ = (S * (1 + 4 * C)) ^ 2 * a * U := by ring
  rw [hmul, norm_mul]
  exact mul_le_mul hm' (hSc s hs_mem) (norm_nonneg _) (Real.exp_pos _).le

/-- **W83 Prop. 2.1 for periods in a product of lattices (Tier 2).** The periods
`ω_i = perVec α β (P i)` lie in `Π_j (ℤα_j + ℤβ_j)` and have rank `κ` (a nonzero `κ × κ` minor);
they need not be `ℂ`-linearly independent. -/
theorem prop21Lat (n κ : ℕ) (a : ℝ) (ha : 0 ≤ a) (α β : Fin n → ℂ)
    (hD : ∀ j, ((starRingEnd ℂ) (α j) * β j).im ≠ 0) (P : Fin κ → Idx n → ℤ)
    (I : Fin κ → Idx n) (hI : Function.Injective I) (hd : (minorMat P I).det ≠ 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L : ℕ) (b Δ U R r : ℝ) (ψ : Fin L → (Fin n → ℂ) → ℂ),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → r ^ 2 * Real.log (R / r) ≤ U →
      0 ≤ b → b * r ^ 2 ≤ a * U →
      (∀ l, Differentiable ℂ (ψ l)) → (∀ z, ‖z‖ ≤ R → ∑ l, ‖ψ l z‖ ≤ Real.exp U) →
      (∀ k : Fin κ → ℤ, ∀ z : Fin n → ℂ, ∃ m : ℂ,
        ‖m‖ ≤ Real.exp (b * (‖z‖ + ‖∑ i, (k i : ℂ) • perVec α β (P i)‖) ^ 2) ∧
        ∀ l, ψ l (z + ∑ i, (k i : ℂ) • perVec α β (P i)) = m * ψ l z) →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ Real.exp (-U) := by
  classical
  have hκ2 : κ ≤ 2 * n := by
    have := Fintype.card_le_of_injective I hI
    simp only [Fintype.card_fin, Fintype.card_prod] at this; linarith
  -- constants
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ j, (‖α j‖ + ‖β j‖) := ⟨_, rfl⟩
  have hSj : ∀ j, ‖α j‖ + ‖β j‖ ≤ S := fun j => by
    have := single_le_sum (f := fun j => ‖α j‖ + ‖β j‖) (fun j _ => by positivity) (mem_univ j)
    rw [hSdef]; linarith
  have hS1 : 1 ≤ S := by
    have := sum_nonneg fun j (_ : j ∈ univ) => (by positivity : 0 ≤ ‖α j‖ + ‖β j‖)
    rw [hSdef]; linarith
  obtain ⟨ci, hcidef⟩ : ∃ ci : ℝ,
      ci = 1 + ∑ j, (‖α j‖ + ‖β j‖) / |((starRingEnd ℂ) (α j) * β j).im| := ⟨_, rfl⟩
  have hcij : ∀ j, (‖α j‖ + ‖β j‖) / |((starRingEnd ℂ) (α j) * β j).im| ≤ ci := fun j => by
    have := single_le_sum (f := fun j => (‖α j‖ + ‖β j‖) / |((starRingEnd ℂ) (α j) * β j).im|)
      (fun j _ => by positivity) (mem_univ j)
    rw [hcidef]; linarith
  have hci1 : 1 ≤ ci := by
    have := sum_nonneg fun j (_ : j ∈ univ) =>
      (by positivity : 0 ≤ (‖α j‖ + ‖β j‖) / |((starRingEnd ℂ) (α j) * β j).im|)
    rw [hcidef]; linarith
  obtain ⟨dd, hdd⟩ : ∃ dd : ℝ, dd = |((minorMat P I).det : ℝ)| := ⟨_, rfl⟩
  have hdd0 : 0 ≤ dd := hdd ▸ abs_nonneg _
  have hcA0 : 0 ≤ cAdj P I := sum_nonneg fun i _ => sum_nonneg fun t _ => abs_nonneg _
  have hcP0 : 0 ≤ cP P := sum_nonneg fun i _ => sum_nonneg fun c _ => abs_nonneg _
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ((cAdj P I * cP P : ℤ) : ℝ) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; exact_mod_cast mul_nonneg hcA0 hcP0
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = 3 * S * ci * Real.exp 2 := ⟨_, rfl⟩
  have hG1 : 1 ≤ G := by
    have h1 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    have h2 : 1 ≤ S * ci := one_le_mul_of_one_le_of_one_le hS1 hci1
    have : 1 ≤ S * ci * Real.exp 2 := one_le_mul_of_one_le_of_one_le h2 h1
    rw [hGdef]; nlinarith
  have hBs1 : 1 ≤ 16 * G := by linarith
  obtain ⟨C₅, hC₅def⟩ : ∃ C₅ : ℝ,
      C₅ = (2 * S * dd) ^ κ * (3 * (1 + 3 * C * S)) ^ (2 * n) * 40 ^ n := ⟨_, rfl⟩
  have hC₅ : 0 ≤ C₅ := by rw [hC₅def]; positivity
  obtain ⟨C₆, hC₆def⟩ : ∃ C₆ : ℝ, C₆ = S * (dd + 1 + 2 * C) := ⟨_, rfl⟩
  obtain ⟨C₇, hC₇def⟩ : ∃ C₇ : ℝ, C₇ = S * (1 + 4 * C) := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = 3 + C₇ ^ 2 * a := ⟨_, rfl⟩
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hlogBs : 0 ≤ Real.log (16 * G) := Real.log_nonneg hBs1
  have hC₆0 : 0 ≤ C₆ := by rw [hC₆def]; positivity
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = n + 6 + 360 * n * Real.log (16 * G) + C₆ := ⟨_, rfl⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnlog : 0 ≤ 360 * n * Real.log (16 * G) := by positivity
  have hX6 : 6 ≤ X := by rw [hXdef]; linarith
  have hC6X : C₆ ≤ X := by rw [hXdef]; linarith
  have hlogX : 360 * n * Real.log (16 * G) ≤ X := by rw [hXdef]; linarith
  have hnX : (n : ℝ) + 2 ≤ X := by rw [hXdef]; linarith
  refine ⟨Real.exp X, 2 * (ν + 3) * (C₅ + 1), Real.exp_pos _, by positivity, ?_⟩
  intro L b Δ U R r ψ hL hΔ hΔU hRr hr hU hb0 hbU hψd hψR hQP hc₂
  have hexpX : X + 1 ≤ Real.exp X := Real.add_one_le_exp X
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hRr0 : 0 < R / r := by linarith
  have hR0 : 0 < R := (div_pos_iff_of_pos_right hr0).mp hRr0
  have hRr4 : 4 * r ≤ R := by
    have : 4 ≤ R / r := by linarith
    rw [le_div_iff₀ hr0] at this; linarith
  have hC₆r : C₆ * r ≤ R := by
    have : C₆ ≤ R / r := by linarith
    rwa [le_div_iff₀ hr0] at this
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log (R / r) := ⟨_, rfl⟩
  rw [← hℓdef] at hU hc₂
  have hℓX : X ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp X]
    exact Real.log_le_log (Real.exp_pos X) hRr
  have hℓ0 : 0 < ℓ := by linarith
  have hUℓ : ℓ ≤ U := le_trans (le_mul_of_one_le_left hℓ0.le (one_le_pow₀ hr1)) hU
  have hUX : X ≤ U := hℓX.trans hUℓ
  have hU0 : 0 < U := by linarith
  -- the grid
  obtain ⟨A, K, hA1, hK0, hSAK, hrK, hM1, hM2, hA2⟩ := exists_params2 hr1 hℓ0 hU hS1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0
  have hAK : (A : ℝ) / K ≤ r :=
    le_trans (div_le_div_of_nonneg_right (le_mul_of_one_le_left (Nat.cast_nonneg A) hS1)
      hKpos.le) hSAK
  have hcoord := fun j => lat_coord (hD j) hA1 hK0 hr0 hRr4 (hSj j) (hcij j) hS1 hci1 hSAK hrK
  rw [← hGdef] at hcoord
  -- the condition set
  set Kd : ℕ := ((K : ℤ) * (minorMat P I).det).natAbs
  have hKd : (Kd : ℝ) = K * dd := by
    simp only [Kd]
    rw [hdd, Nat.cast_natAbs, Int.cast_abs]; push_cast; rw [abs_mul, Nat.abs_cast]
  have hBnn : 0 ≤ (A : ℤ) + cAdj P I * cP P * (A + K) := by positivity
  set Bn : ℕ := ((A : ℤ) + cAdj P I * cP P * (A + K)).toNat
  have hBnZ : (Bn : ℤ) = A + cAdj P I * cP P * (A + K) := Int.toNat_of_nonneg hBnn
  have hBnR : (Bn : ℝ) = A + C * (A + K) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hBnZ
    simp only [Int.cast_natCast] at this
    rw [this, hCdef]; push_cast; ring
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hK0
  set Jc : Finset (Idx n → ℤ) := condIdx2 I Kd Bn
  have hJpt : ∀ s ∈ Jc, ‖gpt α β K s‖ ≤ R := by
    intro s hs
    have hsb : ∀ c, |(s c : ℝ)| ≤ Kd + Bn := by
      intro c
      have hsc := Fintype.mem_piFinset.mp hs c
      split_ifs at hsc with hc
      · obtain ⟨h1, h2⟩ := mem_Ico.mp hsc
        have : |s c| ≤ (Kd : ℤ) + Bn := by rw [abs_of_nonneg h1]; omega
        rw [← Int.cast_abs]; exact_mod_cast this
      · obtain ⟨h1, h2⟩ := mem_Icc.mp hsc
        have : |s c| ≤ (Kd : ℤ) + Bn := by rw [abs_le]; constructor <;> omega
        rw [← Int.cast_abs]; exact_mod_cast this
    refine (norm_gpt_le α β hK0 (by linarith) hSj s (by positivity) hsb).trans ?_
    refine le_trans ?_ hC₆r
    rw [div_le_iff₀ hKpos, hKd, hBnR]
    have hAK' : (A : ℝ) ≤ r * K := by rwa [div_le_iff₀ hKpos] at hAK
    have hKr : (K : ℝ) ≤ r * K := le_mul_of_one_le_left hKpos.le hr1
    have h1 : (K : ℝ) * dd ≤ r * K * dd := mul_le_mul_of_nonneg_right hKr hdd0
    have h2 : C * (A + K) ≤ C * (2 * (r * K)) := by gcongr; linarith
    have h3 : (K : ℝ) * dd + (A + C * (A + K)) ≤ (dd + 1 + 2 * C) * r * K := by
      have e : (dd + 1 + 2 * C) * r * K = r * K * dd + r * K + C * (2 * (r * K)) := by ring
      rw [e]; linarith
    calc S * ((K : ℝ) * dd + (A + C * (A + K))) ≤ S * ((dd + 1 + 2 * C) * r * K) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = C₆ * r * K := by rw [hC₆def]; ring
  -- Siegel
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = ⌊Real.exp Δ⌋₊ := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = Real.exp (-(ν * U)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ Real.exp_pos _
  let a' : Jc → Fin L → ℂ := fun k l => ψ l (gpt α β K k.1)
  have hY : ∀ k : Jc, ∑ l, ‖a' k l‖ ≤ Real.exp U := fun k => hψR _ (hJpt k.1 k.2)
  have hcardJ : Fintype.card Jc = Kd ^ κ * (2 * Bn + 1) ^ (2 * n - κ) := by
    rw [Fintype.card_coe]; exact card_condIdx2 hI Kd Bn
  have hcnt : 2 * (Fintype.card Jc : ℝ) * ((ν + 3) * U) ≤ L * Δ := by
    have h1 := count_lat (U := U) hκ2 hr1 hℓ0 hS1 hdd0 hC0 hA1 hKd hBnR hrK hA2
    rw [← hcardJ] at h1
    have hpos : 0 < r ^ κ * ℓ ^ n := by positivity
    have h2 : 2 * (Fintype.card Jc : ℝ) * ((ν + 3) * U) * (r ^ κ * ℓ ^ n) ≤
        L * Δ * (r ^ κ * ℓ ^ n) := by
      calc 2 * (Fintype.card Jc : ℝ) * ((ν + 3) * U) * (r ^ κ * ℓ ^ n)
          = 2 * (ν + 3) * U * ((Fintype.card Jc : ℝ) * r ^ κ * ℓ ^ n) := by ring
        _ ≤ 2 * (ν + 3) * U * (C₅ * U ^ n) := by rw [hC₅def]; gcongr
        _ = 2 * (ν + 3) * C₅ * U ^ (n + 1) := by ring
        _ ≤ 2 * (ν + 3) * (C₅ + 1) * U ^ (n + 1) := by gcongr; linarith
        _ ≤ L * Δ * r ^ κ * ℓ ^ n := hc₂
        _ = L * Δ * (r ^ κ * ℓ ^ n) := by ring
    exact le_of_mul_le_mul_right h2 hpos
  have hcount := siegel_count hL (by linarith) hν0 hΔU hB hε hcnt
  obtain ⟨p, hp0, hpB, hpS⟩ := siegel_approx a' B hε0 hY hcount
  have hBΔ : (B : ℝ) ≤ Real.exp Δ := hB ▸ Nat.floor_le (Real.exp_pos Δ).le
  refine ⟨p, hp0, fun l => ?_, ?_⟩
  · have h1 : |(p l : ℝ)| ≤ B := by
      rw [← Int.cast_abs]; exact_mod_cast hpB l
    exact h1.trans hBΔ
  -- smallness on the grid
  have hgrid : ∀ g : Fin n → ℂ, (∀ j, g j ∈ latNodes (α j) (β j) A K) →
      ‖∑ l, (p l : ℂ) * ψ l g‖ ≤ 2 * Real.exp (-(3 * U)) := by
    intro g hg
    refine (grid_small2 α β P I hd ψ p hK0 hr1 (by linarith) hSj hAK hC0 hCdef hb0 hbU hQP Bn
      hBnZ (fun s hs => hpS ⟨s, hs⟩) g hg).trans (le_of_eq ?_)
    rw [hε, mul_left_comm, ← Real.exp_add, hν, ← hC₇def]; ring_nf
  -- interpolation
  intro z hz
  have hΨd : Differentiable ℂ (fun z => ∑ l, (p l : ℂ) * ψ l z) :=
    Differentiable.fun_sum fun l _ => (hψd l).const_mul _
  have hq0 : 0 ≤ 2 * r / (R - r) := div_nonneg (by linarith) (by linarith)
  have hRq : R / r * (2 * r / (R - r)) ≤ 4 := by
    rw [show R / r * (2 * r / (R - r)) = 2 * R / (R - r) by field_simp]
    rw [div_le_iff₀ (by linarith)]; linarith
  have hC := lag_C_le (M := (2 * A + 1) ^ 2) hG1 hRr0.le hq0 hRq
  have hC1 : (1 : ℝ) ≤ (16 * G) ^ ((2 * A + 1) ^ 2) := one_le_pow₀ hBs1
  have hint := grid_interp2 (fun z => ∑ l, (p l : ℂ) * ψ l z) hΨd
    (fun j => latNodes (α j) (β j) A K) ((2 * A + 1) ^ 2)
    (fun j => card_latNodes (hD j) hK0) hr0.le (by linarith) (fun j => (hcoord j).1)
    (fun j => (hcoord j).2.1) (fun j => (hcoord j).2.2)
    hC hC1 (by positivity) (Real.exp_pos _).le hgrid
    (norm_combo_le ψ p hpB hBΔ hψR) hz
  have hq := q_le hr0 hRr4 (by rw [← hℓdef]; linarith)
  rw [← hℓdef] at hq
  have hlog : (n : ℝ) * ((2 * A + 1) ^ 2 : ℕ) * Real.log (16 * G) ≤ U := by
    have h1 : (((2 * A + 1) ^ 2 : ℕ) : ℝ) * ℓ ≤ 360 * U := by rwa [le_div_iff₀ hℓ0] at hM2
    have h2 : 360 * n * Real.log (16 * G) ≤ ℓ := by linarith
    have h3 : (0 : ℝ) ≤ (((2 * A + 1) ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : (n : ℝ) * (((2 * A + 1) ^ 2 : ℕ) : ℝ) * Real.log (16 * G) * 360 ≤ U * 360 := by
      calc (n : ℝ) * (((2 * A + 1) ^ 2 : ℕ) : ℝ) * Real.log (16 * G) * 360
          = (((2 * A + 1) ^ 2 : ℕ) : ℝ) * (360 * n * Real.log (16 * G)) := by ring
        _ ≤ (((2 * A + 1) ^ 2 : ℕ) : ℝ) * ℓ := by gcongr
        _ ≤ 360 * U := h1
        _ = U * 360 := by ring
    linarith
  exact hint.trans (final_arith2 hBs1 (by linarith) hℓ0 hM1 hlog hq0 hq hΔU)

end LSG.Aux
