/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Prop21GenDefs

/-!
# W83 Prop. 2.1 for general lattice blocks (Tier 3), conditional on Lemma L

**`LSG.Aux.prop21Gen_of_interp`.** Let `e : Idx n → ℂⁿ` (`2n` vectors; in the application an
`ℝ`-basis of `ℂⁿ`, e.g. block-diagonal: one-variable lattices for `G_a`, `G_m`, `E` and full
period lattices `Λ_A ⊂ ℂ^g` for the abelian blocks), and periods `ω_i = Σ_c P_i(c) e_c`
(`i < κ`) with integer coordinates `P i` and a nonzero `κ × κ` minor. Assume **Lemma L** for `e`
(`LSG.Aux.LemmaLInterp e`, an explicit hypothesis, not an axiom). Then the conclusion of
`LSG.Aux.prop21Lat` holds with `perVec α β (P i)` replaced by `ω_i`: under W83's hypotheses
(`U ≥ r² log(R/r)`, `b r² ≤ a U`, (QP), `c₂ U^{n+1} ≤ L Δ r^κ log(R/r)^n`) there are integers
`p_l`, not all zero, `|p_l| ≤ e^Δ`, with `|Σ p_l ψ_l| ≤ e^{−U}` on `‖z‖ ≤ r`.

Proof: as `prop21Lat`. The grid is `{gptL e K v : |v_c| ≤ A}` with `A ≍ √(U/log(R/r))` and
`A ≍ rK`; the condition representatives and their count come from `lat_decomp`/`condIdx2`
(which only see the integer coordinates, so they are reused verbatim), Siegel's lemma, the
multiplier transfer `grid_smallL`, and the interpolation step is Lemma L in place of
`grid_interp2`.

`prop21Lat` is recovered from this theorem and the proved product case of Lemma L
(`LSG.Aux.prop21Lat_of_gen`, `Prop21GenProd.lean`).

* `LSG.Aux.exists_paramsL`, `LSG.Aux.prop21Gen_of_interp`.
-/

open Complex Finset

namespace LSG.Aux

/-- Grid parameters for Tier 3: `A² ≍ D U/ℓ` and `A ≤ rK ≤ 2A`. -/
lemma exists_paramsL {r ℓ U D : ℝ} (hr1 : 1 ≤ r) (hℓ0 : 0 < ℓ) (hU : r ^ 2 * ℓ ≤ U)
    (hD : 1 ≤ D) :
    ∃ A K : ℕ, r ≤ A ∧ K ≠ 0 ∧ (A : ℝ) ≤ r * K ∧ r * K ≤ 2 * A ∧
      D * U / ℓ ≤ (A : ℝ) ^ 2 ∧ (A : ℝ) ^ 2 ≤ 4 * (D * U / ℓ) := by
  have hr0 : 0 < r := by linarith
  have hU0 : 0 ≤ U := le_trans (by positivity) hU
  set y : ℝ := Real.sqrt (D * U / ℓ) with hy
  have hy2 : y ^ 2 = D * U / ℓ := Real.sq_sqrt (by positivity)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hyr : r ≤ y := by
    have h1 : r ^ 2 ≤ y ^ 2 := by
      rw [hy2, le_div_iff₀ hℓ0]; nlinarith
    exact (pow_le_pow_iff_left₀ hr0.le hy0 two_ne_zero).mp h1
  set A : ℕ := ⌈y⌉₊
  have hyA : y ≤ A := Nat.le_ceil y
  have hAy : (A : ℝ) ≤ 2 * y := by
    have := Nat.ceil_lt_add_one hy0; linarith
  have hrA : r ≤ A := hyr.trans hyA
  have hx1 : 1 ≤ (A : ℝ) / r := by rw [le_div_iff₀ hr0]; linarith
  set K : ℕ := ⌈(A : ℝ) / r⌉₊
  have hxK : (A : ℝ) / r ≤ K := Nat.le_ceil _
  have hKx : (K : ℝ) < A / r + 1 := Nat.ceil_lt_add_one (by linarith)
  have hK0 : K ≠ 0 := (Nat.ceil_pos.mpr (by linarith)).ne'
  refine ⟨A, K, hrA, hK0, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hr0] at hxK; linarith
  · have h1 : r * K < r * (A / r + 1) := mul_lt_mul_of_pos_left hKx hr0
    have h2 : r * (A / r + 1) = A + r := by field_simp
    linarith
  · rw [← hy2]; nlinarith
  · rw [← hy2]; nlinarith

set_option maxHeartbeats 1000000 in -- long proof (as `prop21Lat`)
/-- **W83 Prop. 2.1 for general lattice blocks (Tier 3), conditional on Lemma L.** The periods
`ω_i = Σ_c P_i(c) e_c` lie in the lattice spanned by `e` and have rank `κ` (a nonzero `κ × κ`
minor of their integer coordinates); they need not be `ℂ`-linearly independent. The conclusion is
that of `LSG.Aux.prop21Lat`, word for word, with `perVec α β (P i)` replaced by `ω_i`. -/
theorem prop21Gen_of_interp (n κ : ℕ) (a : ℝ) (ha : 0 ≤ a) (e : Idx n → (Fin n → ℂ))
    (hL : LemmaLInterp e) (P : Fin κ → Idx n → ℤ) (I : Fin κ → Idx n)
    (hI : Function.Injective I) (hd : (minorMat P I).det ≠ 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L : ℕ) (b Δ U R r : ℝ) (ψ : Fin L → (Fin n → ℂ) → ℂ),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → r ^ 2 * Real.log (R / r) ≤ U →
      0 ≤ b → b * r ^ 2 ≤ a * U →
      (∀ l, Differentiable ℂ (ψ l)) → (∀ z, ‖z‖ ≤ R → ∑ l, ‖ψ l z‖ ≤ Real.exp U) →
      (∀ k : Fin κ → ℤ, ∀ z : Fin n → ℂ, ∃ m : ℂ,
        ‖m‖ ≤ Real.exp (b * (‖z‖ + ‖∑ i, (k i : ℂ) • ∑ c, (P i c : ℂ) • e c‖) ^ 2) ∧
        ∀ l, ψ l (z + ∑ i, (k i : ℂ) • ∑ c, (P i c : ℂ) • e c) = m * ψ l z) →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ Real.exp (-U) := by
  classical
  obtain ⟨c, CL, A₀, hc0, hCL1, hLI⟩ := hL
  have hCL0 : 0 < CL := by linarith
  have hlogCL : 0 ≤ Real.log CL := Real.log_nonneg hCL1
  have hκ2 : κ ≤ 2 * n := by
    have := Fintype.card_le_of_injective I hI
    simp only [Fintype.card_fin, Fintype.card_prod] at this; linarith
  -- constants
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ c, ‖e c‖ := ⟨_, rfl⟩
  have hS : ∑ c, ‖e c‖ ≤ S := by rw [hSdef]; linarith
  have hS1 : 1 ≤ S := by
    have := sum_nonneg fun c (_ : c ∈ univ) => norm_nonneg (e c)
    rw [hSdef]; linarith
  obtain ⟨dd, hdd⟩ : ∃ dd : ℝ, dd = |((minorMat P I).det : ℝ)| := ⟨_, rfl⟩
  have hdd0 : 0 ≤ dd := hdd ▸ abs_nonneg _
  have hcA0 : 0 ≤ cAdj P I := sum_nonneg fun i _ => sum_nonneg fun t _ => abs_nonneg _
  have hcP0 : 0 ≤ cP P := sum_nonneg fun i _ => sum_nonneg fun c _ => abs_nonneg _
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ((cAdj P I * cP P : ℤ) : ℝ) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; exact_mod_cast mul_nonneg hcA0 hcP0
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 10 / c + 1 := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by
    have : 0 ≤ 10 / c := by positivity
    rw [hDdef]; linarith
  have hcD : 10 ≤ c * D := by
    have h1 : c * (10 / c) = 10 := by field_simp
    rw [hDdef, mul_add, h1]; linarith
  obtain ⟨C₅, hC₅def⟩ : ∃ C₅ : ℝ,
      C₅ = (2 * 1 * dd) ^ κ * (3 * (1 + 3 * C * 1)) ^ (2 * n) * 40 ^ n * (D / 10) ^ n :=
    ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by linarith
  have hC₅ : 0 ≤ C₅ := by rw [hC₅def]; positivity
  obtain ⟨C₆, hC₆def⟩ : ∃ C₆ : ℝ, C₆ = S * (dd + 1 + 2 * C) := ⟨_, rfl⟩
  obtain ⟨C₇, hC₇def⟩ : ∃ C₇ : ℝ, C₇ = S * (1 + 4 * C) := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = 3 + C₇ ^ 2 * a := ⟨_, rfl⟩
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hC₆0 : 0 ≤ C₆ := by rw [hC₆def]; positivity
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = 6 + C₆ + CL + 4 * D * Real.log CL + A₀ := ⟨_, rfl⟩
  have hA₀0 : (0 : ℝ) ≤ A₀ := Nat.cast_nonneg A₀
  have hDlog : 0 ≤ 4 * D * Real.log CL := by positivity
  have hX6 : 6 ≤ X := by rw [hXdef]; linarith
  have hC6X : C₆ ≤ X := by rw [hXdef]; linarith
  have hCLX : CL ≤ X := by rw [hXdef]; linarith
  have hlogX : 4 * D * Real.log CL ≤ X := by rw [hXdef]; linarith
  have hA₀X : (A₀ : ℝ) ≤ X := by rw [hXdef]; linarith
  refine ⟨Real.exp X, 2 * (ν + 3) * (C₅ + 1), Real.exp_pos _, by positivity, ?_⟩
  intro L b Δ U R r ψ hL hΔ hΔU hRr hr hU hb0 hbU hψd hψR hQP hc₂
  have hexpX : X + 1 ≤ Real.exp X := Real.add_one_le_exp X
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hRr0 : 0 < R / r := by linarith
  have hR0 : 0 < R := (div_pos_iff_of_pos_right hr0).mp hRr0
  have hC₆r : C₆ * r ≤ R := by
    have : C₆ ≤ R / r := by linarith
    rwa [le_div_iff₀ hr0] at this
  have hCLr : CL * r ≤ R := by
    have : CL ≤ R / r := by linarith
    rwa [le_div_iff₀ hr0] at this
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log (R / r) := ⟨_, rfl⟩
  rw [← hℓdef] at hU hc₂
  have hRrℓ : R / r = Real.exp ℓ := by rw [hℓdef, Real.exp_log hRr0]
  have hℓX : X ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp X]
    exact Real.log_le_log (Real.exp_pos X) hRr
  have hℓ0 : 0 < ℓ := by linarith
  have hUℓ : ℓ ≤ U := le_trans (le_mul_of_one_le_left hℓ0.le (one_le_pow₀ hr1)) hU
  have hUX : X ≤ U := hℓX.trans hUℓ
  have hU0 : 0 < U := by linarith
  -- the grid
  obtain ⟨A, K, hrA, hK0, hArK, hrK2, hA2lo, hA2hi⟩ := exists_paramsL hr1 hℓ0 hU hD1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0
  have hA1 : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith)
  have hAA₀ : A₀ ≤ A := by
    have : (A₀ : ℝ) ≤ A := by linarith
    exact_mod_cast this
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
  set Jc : Finset (Idx n → ℤ) := condIdx2 I Kd Bn
  have hJpt : ∀ s ∈ Jc, ‖gptL e K s‖ ≤ R := by
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
    refine (norm_gptL_le e hK0 hS s (by positivity) hsb).trans ?_
    refine le_trans ?_ hC₆r
    rw [div_le_iff₀ hKpos, hKd, hBnR]
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
  let a' : Jc → Fin L → ℂ := fun k l => ψ l (gptL e K k.1)
  have hY : ∀ k : Jc, ∑ l, ‖a' k l‖ ≤ Real.exp U := fun k => hψR _ (hJpt k.1 k.2)
  have hcardJ : Fintype.card Jc = Kd ^ κ * (2 * Bn + 1) ^ (2 * n - κ) := by
    rw [Fintype.card_coe]; exact card_condIdx2 hI Kd Bn
  have hcnt : 2 * (Fintype.card Jc : ℝ) * ((ν + 3) * U) ≤ L * Δ := by
    have hA2' : (A : ℝ) ^ 2 ≤ 40 * (D * U / 10) / ℓ := by
      rw [show 40 * (D * U / 10) / ℓ = 4 * (D * U / ℓ) by ring]; exact hA2hi
    have h1 := count_lat (U := D * U / 10) hκ2 hr1 hℓ0 le_rfl hdd0 hC0 hA1 hKd hBnR
      (by linarith) hA2'
    rw [← hcardJ] at h1
    have hpos : 0 < r ^ κ * ℓ ^ n := by positivity
    have h2 : 2 * (Fintype.card Jc : ℝ) * ((ν + 3) * U) * (r ^ κ * ℓ ^ n) ≤
        L * Δ * (r ^ κ * ℓ ^ n) := by
      calc 2 * (Fintype.card Jc : ℝ) * ((ν + 3) * U) * (r ^ κ * ℓ ^ n)
          = 2 * (ν + 3) * U * ((Fintype.card Jc : ℝ) * r ^ κ * ℓ ^ n) := by ring
        _ ≤ 2 * (ν + 3) * U * ((2 * 1 * dd) ^ κ * (3 * (1 + 3 * C * 1)) ^ (2 * n) * 40 ^ n *
              (D * U / 10) ^ n) := by gcongr
        _ = 2 * (ν + 3) * C₅ * U ^ (n + 1) := by
            rw [hC₅def, show D * U / 10 = D / 10 * U by ring, mul_pow]; ring
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
  have hgrid : ∀ v : Idx n → ℤ, (∀ c, |v c| ≤ A) →
      ‖∑ l, (p l : ℂ) * ψ l (gptL e K v)‖ ≤ 2 * Real.exp (-(3 * U)) := by
    intro v hv
    refine (grid_smallL e P I hd ψ p hK0 hr1 (by linarith) hS hArK hC0 hCdef hb0 hbU hQP Bn
      hBnZ (fun s hs => hpS ⟨s, hs⟩) v hv).trans (le_of_eq ?_)
    rw [hε, mul_left_comm, ← Real.exp_add, hν, ← hC₇def]; ring_nf
  -- interpolation (Lemma L)
  intro z hz
  have hΨd : Differentiable ℂ (fun z => ∑ l, (p l : ℂ) * ψ l z) :=
    Differentiable.fun_sum fun l _ => (hψd l).const_mul _
  have hint := hLI (fun z => ∑ l, (p l : ℂ) * ψ l z) A K r R (2 * Real.exp (-(3 * U)))
    (Real.exp (Δ + U)) hΨd hAA₀ hA1 hK0 hr0 hArK hrK2 hCLr (by positivity) (by positivity)
    hgrid (norm_combo_le ψ p hpB hBΔ hψR) z hz
  -- the final estimate
  have hpre : CL ^ (A ^ 2) ≤ Real.exp U := by
    rw [← Real.exp_log hCL0, ← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    have h4 : 4 * D * Real.log CL ≤ ℓ := hlogX.trans hℓX
    calc (A : ℝ) ^ 2 * Real.log CL ≤ 4 * (D * U / ℓ) * Real.log CL := by gcongr
      _ = (4 * D * Real.log CL) * U / ℓ := by ring
      _ ≤ ℓ * U / ℓ := by gcongr
      _ = U := by field_simp
  have hq : (CL * r / R) ^ (c * (A : ℝ) ^ 2) ≤ Real.exp (-(5 * U)) := by
    have hCLℓ : CL ≤ Real.exp (ℓ / 2) := by
      calc CL = Real.exp (Real.log CL) := (Real.exp_log hCL0).symm
        _ ≤ Real.exp (ℓ / 2) := by
            have h1 : Real.log CL ≤ D * Real.log CL := le_mul_of_one_le_left hlogCL hD1
            exact Real.exp_le_exp.mpr (by linarith)
    have hbase : CL * r / R ≤ Real.exp (-(ℓ / 2)) := by
      calc CL * r / R = CL * (R / r)⁻¹ := by field_simp
        _ = CL * Real.exp (-ℓ) := by rw [hRrℓ, Real.exp_neg]
        _ ≤ Real.exp (ℓ / 2) * Real.exp (-ℓ) := by gcongr
        _ = Real.exp (-(ℓ / 2)) := by rw [← Real.exp_add]; ring_nf
    have hexp : -(ℓ / 2) * (c * (A : ℝ) ^ 2) ≤ -(5 * U) := by
      have h1 : D * U ≤ (A : ℝ) ^ 2 * ℓ := by rwa [div_le_iff₀ hℓ0] at hA2lo
      have h2 : 10 * U ≤ c * D * U := mul_le_mul_of_nonneg_right hcD hU0.le
      have h3 : c * (D * U) ≤ c * ((A : ℝ) ^ 2 * ℓ) := by gcongr
      have e1 : -(ℓ / 2) * (c * (A : ℝ) ^ 2) = -(c * ((A : ℝ) ^ 2 * ℓ)) / 2 := by ring
      have e2 : c * (D * U) = c * D * U := by ring
      rw [e1]; linarith
    calc (CL * r / R) ^ (c * (A : ℝ) ^ 2) ≤ Real.exp (-(ℓ / 2)) ^ (c * (A : ℝ) ^ 2) :=
          Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = Real.exp (-(ℓ / 2) * (c * (A : ℝ) ^ 2)) := by rw [← Real.exp_mul]
      _ ≤ Real.exp (-(5 * U)) := Real.exp_le_exp.mpr hexp
  have hΔU' : Real.exp (Δ + U) ≤ Real.exp (U + U) := Real.exp_le_exp.mpr (by linarith)
  have hinner : 2 * Real.exp (-(3 * U)) + (CL * r / R) ^ (c * (A : ℝ) ^ 2) * Real.exp (Δ + U) ≤
      2 * Real.exp (-(3 * U)) + Real.exp (-(5 * U)) * Real.exp (U + U) := by
    gcongr
  have he3 : (3 : ℝ) ≤ Real.exp U := by have := Real.add_one_le_exp U; linarith
  calc ‖∑ l, (p l : ℂ) * ψ l z‖
      ≤ CL ^ (A ^ 2) * (2 * Real.exp (-(3 * U)) +
          (CL * r / R) ^ (c * (A : ℝ) ^ 2) * Real.exp (Δ + U)) := hint
    _ ≤ Real.exp U * (2 * Real.exp (-(3 * U)) + Real.exp (-(5 * U)) * Real.exp (U + U)) :=
        mul_le_mul hpre hinner (by positivity) (Real.exp_pos _).le
    _ = 3 * Real.exp (-(2 * U)) := by
        have e1 : Real.exp U * Real.exp (-(3 * U)) = Real.exp (-(2 * U)) := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp U * (Real.exp (-(5 * U)) * Real.exp (U + U)) =
            Real.exp (-(2 * U)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        rw [mul_add, ← mul_assoc, mul_comm (Real.exp U) 2, mul_assoc, e1, e2]; ring
    _ ≤ Real.exp U * Real.exp (-(2 * U)) := by gcongr
    _ = Real.exp (-U) := by rw [← Real.exp_add]; ring_nf

end LSG.Aux
