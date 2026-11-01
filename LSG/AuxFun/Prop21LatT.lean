/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Prop21LatTAux

/-!
# W83 Prop. 2.1 with one polynomial direction (`STAGE6_MXP.md` §2.1)

Coordinates `(x, t) ∈ ℂⁿ × ℂ`. The functions `ψ_l` are entire in `x` and polynomials of degree
`≤ D` in `t`. The periods are `(perVec α β (P i), τ_i)`: their `x`-parts lie in the product of
lattices `Π_j (ℤα_j + ℤβ_j)` and have rank `κ`, their `t`-parts `τ_i` are arbitrary. The multiplier
depends on `x` only through its bound.

**`prop21LatT`**: as `prop21Lat`, with Siegel conditions at (representative, `t`-node) for the
`t`-grid `tGrid r D` (at most `10D + 15` nodes in the disc of radius `r`). Grid points are moved to
the representatives by the periods (`grid_smallT`); the resulting shift in `t` is `O(r)` and is
undone by exact Lagrange interpolation in `t`. The final smallness on `‖x‖, |t| ≤ r` comes from
`grid_interp2` in `x` at each `t`-node and Lagrange interpolation in `t`. The Lagrange losses are
`e^{O(D)}`, absorbed by `D r² ≤ aU` and `r ≥ c₁`; the condition count gains the factor `D + 1`.
-/

open Complex Finset Polynomial

namespace LSG.Aux

set_option maxHeartbeats 2000000 in -- long proof (as `prop21Lat`)
/-- **W83 Prop. 2.1 with one polynomial direction.** -/
theorem prop21LatT (n κ : ℕ) (a : ℝ) (ha : 0 ≤ a) (α β : Fin n → ℂ)
    (hD : ∀ j, ((starRingEnd ℂ) (α j) * β j).im ≠ 0) (P : Fin κ → Idx n → ℤ)
    (I : Fin κ → Idx n) (hI : Function.Injective I) (hd : (minorMat P I).det ≠ 0)
    (τ : Fin κ → ℂ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L D : ℕ) (b Δ U R r : ℝ)
      (ψ : Fin L → (Fin n → ℂ) → ℂ → ℂ),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → r ^ 2 * Real.log (R / r) ≤ U →
      0 ≤ b → b * r ^ 2 ≤ a * U → (D : ℝ) * r ^ 2 ≤ a * U →
      (∀ l t, Differentiable ℂ (fun x => ψ l x t)) →
      (∀ l x, ∃ Q : ℂ[X], Q.natDegree ≤ D ∧ ∀ t, ψ l x t = Q.eval t) →
      (∀ x t, ‖x‖ ≤ R → ‖t‖ ≤ R → ∑ l, ‖ψ l x t‖ ≤ Real.exp U) →
      (∀ k : Fin κ → ℤ, ∀ x : Fin n → ℂ, ∀ t : ℂ, ∃ m : ℂ,
        ‖m‖ ≤ Real.exp (b * (‖x‖ + ‖∑ i, (k i : ℂ) • perVec α β (P i)‖) ^ 2) ∧
        ∀ l, ψ l (x + ∑ i, (k i : ℂ) • perVec α β (P i)) (t + ∑ i, (k i : ℂ) * τ i) =
          m * ψ l x t) →
      c₂ * ((D : ℝ) + 1) * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ x t, ‖x‖ ≤ r → ‖t‖ ≤ r → ‖∑ l, (p l : ℂ) * ψ l x t‖ ≤ Real.exp (-U) := by
  classical
  have hκ2 : κ ≤ 2 * n := by
    have := Fintype.card_le_of_injective I hI
    simp only [Fintype.card_fin, Fintype.card_prod] at this; linarith
  -- constants (as `prop21Lat`)
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
  -- the `t`-direction constants
  obtain ⟨Ct, hCtdef⟩ : ∃ Ct : ℝ, Ct = 2 * ((cAdj P I : ℝ) * C) * ∑ i, ‖τ i‖ := ⟨_, rfl⟩
  have hca : (0 : ℝ) ≤ cAdj P I := by exact_mod_cast hcA0
  have hCt0 : 0 ≤ Ct := by
    rw [hCtdef]
    have := sum_nonneg fun i (_ : i ∈ univ) => norm_nonneg (τ i)
    positivity
  obtain ⟨Gt, hGtdef⟩ : ∃ Gt : ℝ, Gt = (8 + 4 * Ct) * Real.exp 2 := ⟨_, rfl⟩
  have hGt1 : 1 ≤ Gt := by
    have h1 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    rw [hGtdef]; nlinarith
  have hlg : 0 ≤ Real.log Gt := Real.log_nonneg hGt1
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = 4 + C₇ ^ 2 * a := ⟨_, rfl⟩
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hlogBs : 0 ≤ Real.log (16 * G) := Real.log_nonneg hBs1
  have hC₆0 : 0 ≤ C₆ := by rw [hC₆def]; positivity
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = n + 6 + 360 * n * Real.log (16 * G) + C₆ +
      60 * (a + 1) * (1 + Real.log Gt) + 2 * n := ⟨_, rfl⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnlog : 0 ≤ 360 * n * Real.log (16 * G) := by positivity
  have hXt : 0 ≤ 60 * (a + 1) * (1 + Real.log Gt) := by positivity
  have hX6 : 6 ≤ X := by rw [hXdef]; linarith
  have hC6X : C₆ ≤ X := by rw [hXdef]; linarith
  have hlogX : 360 * n * Real.log (16 * G) ≤ X := by rw [hXdef]; linarith
  have hnX : (n : ℝ) + 2 ≤ X := by rw [hXdef]; linarith
  have htX : 60 * (a + 1) * (1 + Real.log Gt) ≤ X := by rw [hXdef]; linarith
  have h2nX : 2 * ((n : ℝ) + 2) ≤ X := by rw [hXdef]; linarith
  refine ⟨Real.exp X, 30 * (ν + 3) * (C₅ + 1), Real.exp_pos _, by positivity, ?_⟩
  intro L D b Δ U R r ψ hL hΔ hΔU hRr hr hU hb0 hbU hDU hψd hψpoly hψR hQP hc₂
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
  have hrR : r ≤ R := by linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log (R / r) := ⟨_, rfl⟩
  rw [← hℓdef] at hU hc₂
  have hℓX : X ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp X]
    exact Real.log_le_log (Real.exp_pos X) hRr
  have hℓ0 : 0 < ℓ := by linarith
  have hUℓ : ℓ ≤ U := le_trans (le_mul_of_one_le_left hℓ0.le (one_le_pow₀ hr1)) hU
  have hUX : X ≤ U := hℓX.trans hUℓ
  have hU0 : 0 < U := by linarith
  -- the `t`-grid
  set Zt := tGrid r D with hZt
  set Nt := (2 * tA D + 1) ^ 2 with hNt
  have hZtc : Zt.card = Nt := card_tGrid hr0 D
  have hDNt : D < Nt := lt_card_tGrid D
  have hNtle : Nt ≤ 10 * D + 15 := card_tGrid_le D
  have hZtr : ∀ ζ ∈ Zt, ‖ζ‖ ≤ r := norm_tGrid_le hr0 D
  have hLag : ∀ ζ ∈ Zt, ∀ w : ℂ, ‖w‖ ≤ (1 + Ct) * r → ‖lagBasis Zt ζ w‖ ≤ Gt ^ Nt := by
    intro ζ hζ w hw
    rw [hGtdef]; exact lagBasis_tGrid_le hr0 hCt0 D ζ hζ w hw
  have hpoly : ∀ l x w, ψ l x w = ∑ ζ ∈ Zt, ψ l x ζ * lagBasis Zt ζ w := by
    intro l x w
    obtain ⟨Q, hQ, hQe⟩ := hψpoly l x
    rw [hQe, eval_eq_sum_lagBasis Zt Q (by omega) w]
    exact sum_congr rfl fun ζ _ => by rw [hQe]
  -- the Lagrange loss `N_t G_t^{N_t} ≤ e^{U/2}`
  have hloss : (Nt : ℝ) * Gt ^ Nt ≤ Real.exp (U / 2) := by
    have hNt1 : (1 : ℝ) ≤ Nt := by exact_mod_cast (show 1 ≤ Nt by omega)
    have h1 : (Nt : ℝ) * Gt ^ Nt = Real.exp (Real.log Nt + Nt * Real.log Gt) := by
      rw [Real.exp_add, Real.exp_log (by linarith), ← Real.rpow_natCast,
        Real.rpow_def_of_pos (by linarith)]
      ring_nf
    rw [h1, Real.exp_le_exp]
    have h2 : Real.log Nt ≤ Nt := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h3 : (Nt : ℝ) ≤ 10 * D + 15 := by exact_mod_cast hNtle
    have hr2 : 60 * (a + 1) * (1 + Real.log Gt) ≤ r ^ 2 := by
      have : r ≤ r ^ 2 := by nlinarith
      linarith
    have h4 : 10 * (D : ℝ) * (1 + Real.log Gt) ≤ U / 6 := by
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      have h5 : (D : ℝ) * (60 * (a + 1) * (1 + Real.log Gt)) ≤ (D : ℝ) * r ^ 2 := by gcongr
      have h6 : (D : ℝ) * r ^ 2 ≤ (a + 1) * U := by nlinarith
      have h7 : 0 < a + 1 := by linarith
      have h8 : (D : ℝ) * (60 * (1 + Real.log Gt)) ≤ U := by
        have : (a + 1) * ((D : ℝ) * (60 * (1 + Real.log Gt))) ≤ (a + 1) * U := by nlinarith
        exact le_of_mul_le_mul_left this h7
      linarith
    have h9 : 15 * (1 + Real.log Gt) ≤ U / 4 := by
      have : 60 * (1 + Real.log Gt) ≤ 60 * (a + 1) * (1 + Real.log Gt) := by nlinarith
      linarith
    nlinarith
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
  -- Siegel, with conditions at (representative, `t`-node)
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = ⌊Real.exp Δ⌋₊ := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = Real.exp (-(ν * U)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ Real.exp_pos _
  let a' : (Jc ×ˢ Zt : Finset ((Idx n → ℤ) × ℂ)) → Fin L → ℂ :=
    fun k l => ψ l (gpt α β K k.1.1) k.1.2
  have hY : ∀ k : (Jc ×ˢ Zt : Finset ((Idx n → ℤ) × ℂ)), ∑ l, ‖a' k l‖ ≤ Real.exp U := by
    intro k
    obtain ⟨h1, h2⟩ := mem_product.mp k.2
    exact hψR _ _ (hJpt _ h1) ((hZtr _ h2).trans hrR)
  have hcardJ : Fintype.card Jc = Kd ^ κ * (2 * Bn + 1) ^ (2 * n - κ) := by
    rw [Fintype.card_coe]; exact card_condIdx2 hI Kd Bn
  have hcardJt : Fintype.card (Jc ×ˢ Zt : Finset ((Idx n → ℤ) × ℂ)) =
      Fintype.card Jc * Nt := by
    rw [Fintype.card_coe, card_product, ← hZtc, Fintype.card_coe]
  have hcnt : 2 * (Fintype.card (Jc ×ˢ Zt : Finset ((Idx n → ℤ) × ℂ)) : ℝ) * ((ν + 3) * U) ≤
      L * Δ := by
    have h1 := count_lat (U := U) hκ2 hr1 hℓ0 hS1 hdd0 hC0 hA1 hKd hBnR hrK hA2
    rw [← hcardJ] at h1
    have hpos : 0 < r ^ κ * ℓ ^ n := by positivity
    have hNtR : (Nt : ℝ) ≤ 15 * ((D : ℝ) + 1) := by
      have : (Nt : ℝ) ≤ 10 * D + 15 := by exact_mod_cast hNtle
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      linarith
    have h2 : 2 * (Fintype.card (Jc ×ˢ Zt : Finset ((Idx n → ℤ) × ℂ)) : ℝ) * ((ν + 3) * U) *
        (r ^ κ * ℓ ^ n) ≤ L * Δ * (r ^ κ * ℓ ^ n) := by
      rw [hcardJt]
      push_cast
      calc 2 * ((Fintype.card Jc : ℝ) * Nt) * ((ν + 3) * U) * (r ^ κ * ℓ ^ n)
          = 2 * (ν + 3) * U * Nt * ((Fintype.card Jc : ℝ) * r ^ κ * ℓ ^ n) := by ring
        _ ≤ 2 * (ν + 3) * U * (15 * ((D : ℝ) + 1)) * (C₅ * U ^ n) := by
            rw [hC₅def]; gcongr
        _ = 30 * (ν + 3) * C₅ * ((D : ℝ) + 1) * U ^ (n + 1) := by ring
        _ ≤ 30 * (ν + 3) * (C₅ + 1) * ((D : ℝ) + 1) * U ^ (n + 1) := by gcongr; linarith
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
  have hgrid : ∀ ζ : ℂ, ‖ζ‖ ≤ r → ∀ g : Fin n → ℂ, (∀ j, g j ∈ latNodes (α j) (β j) A K) →
      ‖∑ l, (p l : ℂ) * ψ l g ζ‖ ≤ 2 * Real.exp (-(3 * U)) := by
    intro ζ hζ g hg
    refine (grid_smallT α β P I hd τ ψ p hK0 hr1 (by linarith) hSj hAK hC0 hCdef hb0 hbU hQP Zt
      hpoly (fun ζ' hζ' w hw => hLag ζ' hζ' w (by rw [hCtdef]; exact hw)) Bn hBnZ
      (fun s hs ζ' hζ' => hpS ⟨(s, ζ'), mem_product.mpr ⟨hs, hζ'⟩⟩) g hg ζ hζ).trans ?_
    rw [hZtc, ← hC₇def]
    have e1 : Real.exp (C₇ ^ 2 * a * U) * ((Nt : ℝ) * Gt ^ Nt * (2 * ε)) =
        2 * ((Nt : ℝ) * Gt ^ Nt) * Real.exp (C₇ ^ 2 * a * U - ν * U) := by
      rw [hε, sub_eq_add_neg, Real.exp_add]; ring_nf
    rw [e1]
    have e2 : C₇ ^ 2 * a * U - ν * U = -(4 * U) := by rw [hν]; ring
    rw [e2]
    calc 2 * ((Nt : ℝ) * Gt ^ Nt) * Real.exp (-(4 * U))
        ≤ 2 * Real.exp (U / 2) * Real.exp (-(4 * U)) := by gcongr
      _ = 2 * Real.exp (-(7 / 2 * U)) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ 2 * Real.exp (-(3 * U)) := by gcongr; linarith
  -- interpolation in `x` at each `t`-node, then Lagrange in `t`
  have hq0 : 0 ≤ 2 * r / (R - r) := div_nonneg (by linarith) (by linarith)
  have hRq : R / r * (2 * r / (R - r)) ≤ 4 := by
    rw [show R / r * (2 * r / (R - r)) = 2 * R / (R - r) by field_simp]
    rw [div_le_iff₀ (by linarith)]; linarith
  have hC := lag_C_le (M := (2 * A + 1) ^ 2) hG1 hRr0.le hq0 hRq
  have hC1 : (1 : ℝ) ≤ (16 * G) ^ ((2 * A + 1) ^ 2) := one_le_pow₀ hBs1
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
  have hnode : ∀ ζ ∈ Zt, ∀ x : Fin n → ℂ, ‖x‖ ≤ r →
      ‖∑ l, (p l : ℂ) * ψ l x ζ‖ ≤ (2 + n) * Real.exp (-(2 * U)) := by
    intro ζ hζ x hx
    have hΨd : Differentiable ℂ (fun z => ∑ l, (p l : ℂ) * ψ l z ζ) :=
      Differentiable.fun_sum fun l _ => (hψd l ζ).const_mul _
    have hint := grid_interp2 (fun z => ∑ l, (p l : ℂ) * ψ l z ζ) hΨd
      (fun j => latNodes (α j) (β j) A K) ((2 * A + 1) ^ 2)
      (fun j => card_latNodes (hD j) hK0) hr0.le (by linarith) (fun j => (hcoord j).1)
      (fun j => (hcoord j).2.1) (fun j => (hcoord j).2.2)
      hC hC1 (by positivity) (Real.exp_pos _).le (hgrid ζ (hZtr ζ hζ))
      (norm_combo_le (fun l z => ψ l z ζ) p hpB hBΔ
        (fun z hz => hψR z ζ hz ((hZtr ζ hζ).trans hrR))) hx
    exact hint.trans (final_arith2' hBs1 (by linarith) hℓ0 hM1 hlog hq0 hq hΔU)
  intro x t hx ht
  have hsplit : ∑ l, (p l : ℂ) * ψ l x t =
      ∑ ζ ∈ Zt, (∑ l, (p l : ℂ) * ψ l x ζ) * lagBasis Zt ζ t := by
    simp only [hpoly _ x t, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun ζ _ => sum_congr rfl fun l _ => by ring
  rw [hsplit]
  have htr : ‖t‖ ≤ (1 + Ct) * r := le_trans ht (le_mul_of_one_le_left hr0.le (by linarith))
  calc ‖∑ ζ ∈ Zt, (∑ l, (p l : ℂ) * ψ l x ζ) * lagBasis Zt ζ t‖
      ≤ ∑ ζ ∈ Zt, ‖(∑ l, (p l : ℂ) * ψ l x ζ) * lagBasis Zt ζ t‖ := norm_sum_le _ _
    _ ≤ ∑ ζ ∈ Zt, (2 + n) * Real.exp (-(2 * U)) * Gt ^ Nt := by
        refine sum_le_sum fun ζ hζ => ?_
        rw [norm_mul]
        exact mul_le_mul (hnode ζ hζ x hx) (hLag ζ hζ t htr) (norm_nonneg _) (by positivity)
    _ = ((Nt : ℝ) * Gt ^ Nt) * ((2 + n) * Real.exp (-(2 * U))) := by
        rw [sum_const, hZtc, nsmul_eq_mul]; ring
    _ ≤ Real.exp (U / 2) * (Real.exp (U / 2) * Real.exp (-(2 * U))) := by
        gcongr
        have : (n : ℝ) + 3 ≤ Real.exp (U / 2) := by
          have := Real.add_one_le_exp (U / 2); linarith
        linarith
    _ = Real.exp (-U) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf

end LSG.Aux
