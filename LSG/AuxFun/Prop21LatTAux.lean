/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Prop21Lat

/-!
# Helpers for Prop. 2.1 with one polynomial direction (`Prop21LatT.lean`)

* `eval_eq_sum_lagBasis`: exact Lagrange interpolation of a polynomial of degree `< |Z|`;
* `y_bound`: integer combinations `Σ y_i P_i` of rank-`κ` period coordinates control `y`
  (adjugate of the nonzero minor);
* `tGrid`: the `t`-nodes `latNodes r (r i) A (2A)`, `A = ⌊√D⌋ + 1`: at most `10D + 15` nodes
  (more than `D`), all in the disc of radius `r`, Lagrange basis `≤ ((8 + 4c) e²)^N` on the disc of
  radius `(1 + c) r`;
* `grid_smallT`: the transfer of smallness from the condition points to the whole grid, through
  the periods (as `grid_small2`) and exact Lagrange interpolation in `t`;
* `final_arith2'`: the end of `final_arith2` with the bound `(2 + n) e^{-2U}`.
-/

open Complex Finset Polynomial

namespace LSG.Aux

/-- **Exact Lagrange interpolation** of a polynomial of degree `< |Z|`. -/
theorem eval_eq_sum_lagBasis (Z : Finset ℂ) (P : ℂ[X]) (hP : P.natDegree < Z.card) (w : ℂ) :
    P.eval w = ∑ ζ ∈ Z, P.eval ζ * lagBasis Z ζ w := by
  have hdeg : P.degree < Z.card := by
    rcases eq_or_ne P 0 with h | h
    · rw [h, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h]; exact_mod_cast hP
  have h := Lagrange.eq_interpolate (s := Z) (v := id) (f := P) (Set.injOn_id _) hdeg
  conv_lhs => rw [h]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun ζ hζ => ?_
  rw [eval_mul, eval_C, Lagrange.basis, eval_prod, lagBasis]
  congr 1
  refine prod_congr rfl fun ζ' hζ' => ?_
  rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C]
  simp only [id]
  field_simp

variable {n κ : ℕ}

/-- **The coefficients of an integer combination of the periods are controlled by its
coordinates** (adjugate of the nonzero minor). -/
lemma y_bound (P : Fin κ → Idx n → ℤ) (I : Fin κ → Idx n) (hd : (minorMat P I).det ≠ 0)
    (y : Fin κ → ℤ) {K B : ℤ} (hK : 0 ≤ K) (hx : ∀ c, K * |(∑ i, y i • P i) c| ≤ B)
    (i : Fin κ) : K * |y i| ≤ cAdj P I * B := by
  set Mm := minorMat P I with hMm
  set x : Idx n → ℤ := ∑ i, y i • P i with hxdef
  have hB : 0 ≤ B := le_trans (mul_nonneg hK (abs_nonneg _)) (hx (I i))
  have hMy : Mm.mulVec y = fun t => x (I t) := by
    funext t
    simp only [hMm, minorMat, Matrix.mulVec, dotProduct, Matrix.of_apply, hxdef,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hadj : Mm.det • y = Mm.adjugate.mulVec (fun t => x (I t)) := by
    rw [← hMy, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h1 := congrFun hadj i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h1
  have hdet : 1 ≤ |Mm.det| := Int.one_le_abs hd
  have h2 : K * (|Mm.det| * |y i|) ≤ cAdj P I * B := by
    rw [← abs_mul, h1]
    calc K * |∑ t, Mm.adjugate i t * x (I t)| ≤ K * ∑ t, |Mm.adjugate i t| * |x (I t)| := by
          gcongr
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact sum_congr rfl fun t _ => abs_mul _ _
      _ = ∑ t, |Mm.adjugate i t| * (K * |x (I t)|) := by
          rw [mul_sum]; exact sum_congr rfl fun t _ => by ring
      _ ≤ ∑ t, |Mm.adjugate i t| * B := by
          gcongr with t
          exact hx (I t)
      _ = (∑ t, |Mm.adjugate i t|) * B := by rw [sum_mul]
      _ ≤ cAdj P I * B := by
          gcongr
          exact single_le_sum (f := fun i => ∑ t, |Mm.adjugate i t|)
            (fun i _ => sum_nonneg fun t _ => abs_nonneg _) (mem_univ i)
  calc K * |y i| = K * (1 * |y i|) := by ring
    _ ≤ K * (|Mm.det| * |y i|) := by gcongr
    _ ≤ cAdj P I * B := h2

/-! ### The `t`-grid -/

/-- `A_t = ⌊√D⌋ + 1`. -/
def tA (D : ℕ) : ℕ := Nat.sqrt D + 1

/-- The `t`-nodes: `latNodes r (r i) A_t (2 A_t)`. -/
noncomputable def tGrid (r : ℝ) (D : ℕ) : Finset ℂ := latNodes (r : ℂ) (r * I) (tA D) (2 * tA D)

lemma tGrid_hD {r : ℝ} (hr : 0 < r) : ((starRingEnd ℂ) (r : ℂ) * (r * I)).im ≠ 0 := by
  simp only [Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.I_re, Complex.I_im]
  ring_nf; positivity

lemma card_tGrid {r : ℝ} (hr : 0 < r) (D : ℕ) : (tGrid r D).card = (2 * tA D + 1) ^ 2 :=
  card_latNodes (tGrid_hD hr) (by unfold tA; omega)

lemma lt_card_tGrid (D : ℕ) : D < (2 * tA D + 1) ^ 2 := by
  have h := Nat.lt_succ_sqrt D
  unfold tA
  nlinarith

lemma card_tGrid_le (D : ℕ) : (2 * tA D + 1) ^ 2 ≤ 10 * D + 15 := by
  have h := Nat.sqrt_le D
  unfold tA
  zify at h ⊢
  nlinarith [sq_nonneg ((Nat.sqrt D : ℤ) - 1)]

lemma norm_tGrid_le {r : ℝ} (hr : 0 < r) (D : ℕ) : ∀ ζ ∈ tGrid r D, ‖ζ‖ ≤ r := by
  intro ζ hζ
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hζ
  refine (norm_lnode_le _ _ hp).trans (le_of_eq ?_)
  have hA : (tA D : ℝ) ≠ 0 := by unfold tA; positivity
  simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Complex.norm_I, mul_one]
  push_cast
  field_simp
  ring

lemma lagBasis_tGrid_le {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (D : ℕ) :
    ∀ ζ ∈ tGrid r D, ∀ w : ℂ, ‖w‖ ≤ (1 + c) * r →
      ‖lagBasis (tGrid r D) ζ w‖ ≤ ((8 + 4 * c) * Real.exp 2) ^ ((2 * tA D + 1) ^ 2) := by
  intro ζ hζ w hw
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hζ
  have hA1 : 1 ≤ tA D := by unfold tA; omega
  refine (norm_lagBasis_lat_le (tGrid_hD hr) (by omega) hA1 hp (by positivity) hw).trans
    (le_of_eq ?_)
  have hAr : (tA D : ℝ) ≠ 0 := by positivity
  have him : |((starRingEnd ℂ) (r : ℂ) * (r * I)).im| = r ^ 2 := by
    simp only [Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im]
    ring_nf; exact abs_of_nonneg (by positivity)
  have hn : ‖(r : ℂ)‖ + ‖(r : ℂ) * I‖ = 2 * r := by
    simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_I, mul_one]
    ring
  rw [him, hn]
  congr 2
  have e : ((1 + c) * r * ((2 * tA D : ℕ) : ℝ) + 2 * r * (tA D : ℝ)) /
      (r ^ 2 / (2 * r) * (tA D : ℝ)) = 8 + 4 * c := by
    push_cast
    field_simp
    ring
  rw [e]
  exact max_eq_left (by linarith)

/-! ### Transfer through the periods and in `t` -/

/-- **Transfer by the multiplier and in `t`.** The grid point `(g, ζ)` is the condition point
`(gpt s, ζ − Σ y_i τ_i)` translated by the period `Σ y_i ω_i`; the value at `ζ − Σ y_i τ_i` is the
Lagrange combination of the values at the `t`-nodes. -/
lemma grid_smallT {L A K : ℕ} {a b r U ε S C Λ : ℝ} (α β : Fin n → ℂ)
    (P : Fin κ → Idx n → ℤ) (I : Fin κ → Idx n) (hd : (minorMat P I).det ≠ 0) (τ : Fin κ → ℂ)
    (ψ : Fin L → (Fin n → ℂ) → ℂ → ℂ) (p : Fin L → ℤ) (hK : K ≠ 0) (hr1 : 1 ≤ r)
    (hS0 : 0 ≤ S) (hS : ∀ j, ‖α j‖ + ‖β j‖ ≤ S) (hAK : (A : ℝ) / K ≤ r) (hC0 : 0 ≤ C)
    (hC : (C : ℝ) = ((cAdj P I * cP P : ℤ) : ℝ)) (hb0 : 0 ≤ b) (hbU : b * r ^ 2 ≤ a * U)
    (hQP : ∀ k : Fin κ → ℤ, ∀ x : Fin n → ℂ, ∀ t : ℂ, ∃ m : ℂ,
      ‖m‖ ≤ Real.exp (b * (‖x‖ + ‖∑ i, (k i : ℂ) • perVec α β (P i)‖) ^ 2) ∧
      ∀ l, ψ l (x + ∑ i, (k i : ℂ) • perVec α β (P i)) (t + ∑ i, (k i : ℂ) * τ i) =
        m * ψ l x t)
    (Zt : Finset ℂ) (hpoly : ∀ l x w, ψ l x w = ∑ ζ ∈ Zt, ψ l x ζ * lagBasis Zt ζ w)
    (hLag : ∀ ζ' ∈ Zt, ∀ w : ℂ,
      ‖w‖ ≤ (1 + 2 * ((cAdj P I : ℝ) * C) * ∑ i, ‖τ i‖) * r → ‖lagBasis Zt ζ' w‖ ≤ Λ)
    (Bn : ℕ) (hBn : (Bn : ℤ) = A + cAdj P I * cP P * (A + K))
    (hSc : ∀ s ∈ condIdx2 I ((K : ℤ) * (minorMat P I).det).natAbs Bn, ∀ ζ' ∈ Zt,
      ‖∑ l, (p l : ℂ) * ψ l (gpt α β K s) ζ'‖ ≤ 2 * ε)
    (g : Fin n → ℂ) (hg : ∀ j, g j ∈ latNodes (α j) (β j) A K) (ζ : ℂ) (hζ : ‖ζ‖ ≤ r) :
    ‖∑ l, (p l : ℂ) * ψ l g ζ‖ ≤
      Real.exp ((S * (1 + 4 * C)) ^ 2 * a * U) * (Zt.card * Λ * (2 * ε)) := by
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
  -- norm bounds (as `grid_small2`)
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
  have hAKr : C * (A + K) / K ≤ C * (r + 1) := by
    rw [div_le_iff₀ hKpos]
    nlinarith [mul_le_mul_of_nonneg_left hAK' hC0]
  have hper : ‖∑ i, (y i : ℂ) • perVec α β (P i)‖ ≤ 2 * S * C * r := by
    rw [← perVec_sum]
    refine (norm_perVec_le α β hS0 hS x (by positivity) hxB).trans ?_
    calc S * (C * (A + K) / K) ≤ S * (C * (r + 1)) := by gcongr
      _ ≤ 2 * S * C * r := by
          have hSC := mul_nonneg hS0 hC0
          nlinarith [mul_le_mul_of_nonneg_left hr1 hSC]
  -- the `t`-shift
  have hy : ∀ i, |(y i : ℝ)| ≤ (cAdj P I : ℝ) * C * (r + 1) := fun i => by
    have h := y_bound P I hd y (K := K) (B := cAdj P I * cP P * (A + K)) (by positivity) hxb i
    have h' : (((K : ℤ) * |y i| : ℤ) : ℝ) ≤ ((cAdj P I * (cAdj P I * cP P * (A + K)) : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    have hca : (0 : ℝ) ≤ cAdj P I := by
      have : (0 : ℤ) ≤ cAdj P I := sum_nonneg fun i _ => sum_nonneg fun t _ => abs_nonneg _
      exact_mod_cast this
    have e1 : (cAdj P I : ℝ) * ((cAdj P I : ℝ) * (cP P : ℝ) * (A + K)) =
        (cAdj P I : ℝ) * (C * (A + K)) := by rw [← hC']
    rw [e1] at h'
    have h3 : |(y i : ℝ)| ≤ (cAdj P I : ℝ) * (C * (A + K) / K) := by
      rw [mul_div_assoc', le_div_iff₀ hKpos]; linarith
    calc |(y i : ℝ)| ≤ (cAdj P I : ℝ) * (C * (A + K) / K) := h3
      _ ≤ (cAdj P I : ℝ) * (C * (r + 1)) := by gcongr
      _ = (cAdj P I : ℝ) * C * (r + 1) := by ring
  have hca0 : (0 : ℝ) ≤ (cAdj P I : ℝ) * C := by
    have : (0 : ℤ) ≤ cAdj P I := sum_nonneg fun i _ => sum_nonneg fun t _ => abs_nonneg _
    have : (0 : ℝ) ≤ cAdj P I := by exact_mod_cast this
    positivity
  have hshift : ‖∑ i, (y i : ℂ) * τ i‖ ≤ 2 * ((cAdj P I : ℝ) * C) * (∑ i, ‖τ i‖) * r := by
    calc ‖∑ i, (y i : ℂ) * τ i‖ ≤ ∑ i, ‖(y i : ℂ) * τ i‖ := norm_sum_le _ _
      _ = ∑ i, |(y i : ℝ)| * ‖τ i‖ := by
          refine sum_congr rfl fun i _ => ?_
          rw [norm_mul, Complex.norm_intCast]
      _ ≤ ∑ i, (cAdj P I : ℝ) * C * (r + 1) * ‖τ i‖ := by
          gcongr with i; exact hy i
      _ = (cAdj P I : ℝ) * C * (r + 1) * ∑ i, ‖τ i‖ := by rw [mul_sum]
      _ ≤ 2 * ((cAdj P I : ℝ) * C) * (∑ i, ‖τ i‖) * r := by
          have hT0 : 0 ≤ ∑ i, ‖τ i‖ := sum_nonneg fun i _ => norm_nonneg _
          have := mul_nonneg hca0 hT0
          nlinarith
  set w := ζ - ∑ i, (y i : ℂ) * τ i with hw
  have hwn : ‖w‖ ≤ (1 + 2 * ((cAdj P I : ℝ) * C) * ∑ i, ‖τ i‖) * r := by
    calc ‖w‖ ≤ ‖ζ‖ + ‖∑ i, (y i : ℂ) * τ i‖ := norm_sub_le _ _
      _ ≤ r + 2 * ((cAdj P I : ℝ) * C) * (∑ i, ‖τ i‖) * r := add_le_add hζ hshift
      _ = _ := by ring
  obtain ⟨m, hm, hmψ⟩ := hQP y (gpt α β K s) w
  have hζw : ζ = w + ∑ i, (y i : ℂ) * τ i := by rw [hw]; ring
  have hmul : ∑ l, (p l : ℂ) * ψ l g ζ =
      m * ∑ ζ' ∈ Zt, (∑ l, (p l : ℂ) * ψ l (gpt α β K s) ζ') * lagBasis Zt ζ' w := by
    rw [hg', hζw]
    simp only [hmψ]
    rw [mul_sum]
    simp only [hpoly _ (gpt α β K s) w, mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun ζ' _ => sum_congr rfl fun l _ => by ring
  have hm' : ‖m‖ ≤ Real.exp ((S * (1 + 4 * C)) ^ 2 * a * U) := by
    refine hm.trans (Real.exp_le_exp.mpr ?_)
    set u := ‖gpt α β K s‖ + ‖∑ i, (y i : ℂ) • perVec α β (P i)‖
    have hu : u ≤ S * (1 + 4 * C) * r := by simp only [u]; linarith
    have hu0 : 0 ≤ u := by positivity
    calc b * u ^ 2 ≤ b * (S * (1 + 4 * C) * r) ^ 2 := by gcongr
      _ = (S * (1 + 4 * C)) ^ 2 * (b * r ^ 2) := by ring
      _ ≤ (S * (1 + 4 * C)) ^ 2 * (a * U) := by gcongr
      _ = (S * (1 + 4 * C)) ^ 2 * a * U := by ring
  have hsum : ‖∑ ζ' ∈ Zt, (∑ l, (p l : ℂ) * ψ l (gpt α β K s) ζ') * lagBasis Zt ζ' w‖ ≤
      Zt.card * Λ * (2 * ε) := by
    calc _ ≤ ∑ ζ' ∈ Zt, ‖(∑ l, (p l : ℂ) * ψ l (gpt α β K s) ζ') * lagBasis Zt ζ' w‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ζ' ∈ Zt, (2 * ε) * Λ := by
          refine sum_le_sum fun ζ' hζ' => ?_
          rw [norm_mul]
          exact mul_le_mul (hSc s hs_mem ζ' hζ') (hLag ζ' hζ' w hwn) (norm_nonneg _)
            ((norm_nonneg _).trans (hSc s hs_mem ζ' hζ'))
      _ = Zt.card * Λ * (2 * ε) := by rw [sum_const, nsmul_eq_mul]; ring
  rw [hmul, norm_mul]
  exact mul_le_mul hm' hsum (norm_nonneg _) (Real.exp_pos _).le

/-- The final numerical inequality of `final_arith2`, stopped at `(2 + n) e^{-2U}`. -/
lemma final_arith2' {n Nn : ℕ} {U ℓ Δ q Bs : ℝ} (hBs : 1 ≤ Bs) (hU : (n : ℝ) + 2 ≤ U)
    (hℓ0 : 0 < ℓ) (hN1 : 10 * U / ℓ ≤ Nn) (hlog : n * Nn * Real.log Bs ≤ U)
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-(ℓ / 2))) (hΔ : Δ ≤ U) :
    (Bs ^ Nn) ^ n * (2 * Real.exp (-(3 * U)) + n * q ^ Nn * Real.exp (Δ + U)) ≤
      (2 + n) * Real.exp (-(2 * U)) := by
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

end LSG.Aux
