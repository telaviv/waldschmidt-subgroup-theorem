/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarSec7Data
import LSG.W88.AbVarSec7Rat
import LSG.W88.Sec7VCount

/-!
# A5.7: W88 §7 for `G_a^{d₀} × G_m^{d₁} × ∏ B_k` from `MultEstB` (`STAGE_A5.md` §6.4)

**`theorem41B_of (hME : MEB.MultEstB) An Tay : Theorem41B An`**, generic over block families with analytic packages
`An` and Taylor packages `Tay` over every number field. Copy of `theorem41Abelian_of` (`Sec7.lean`):

1. Generators `y_j` of `Y`, `κ = rk (Y ∩ PerL)` independent periods `ω_i`, `ℂ`-independent by toric injectivity
   (`linIndep_of_torInj`).
2. `exists_LUDataA` and `prop61A` with `b = 2`.
3. `MultEstB` for `PW μs p = PpolyA μs p · Π_k X_{k,i₀}` (block degree `D + 1`), points `exp_G(Σ h_j y_j)`,
   `h_j ≤ M = ⌊S/n⌋`, `n = d₀ + d₁ + G` (CR1), `T′ = ⌊Δ/(2n log S)⌋`, `D₀ = ⌊Δ/log²S⌋ + 1`, `D₁ = ⌊Δ/S⌋ + 1`.
4. `exists_inequiv_grid_gen` with `Z = T_{G′} + PerL` (`htil_perL`), `log_count`, `core_ineq`.
5. `exists_subgroupDataB`.
-/

open MvPolynomial Module Filter LSG.Aux LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.MEB (AbBlock ObstrDataB PerL perL_le IsHomB DfunB blk IGsem OrdGtB sigB)

set_option maxHeartbeats 4000000 in
-- the assembly of W88 §7 elaborates many real inequalities
/-- **W88 Theorem 4.1 (under (NR) and toric injectivity) for `G_a^{d₀} × G_m^{d₁} × ∏ B_k` from the multiplicity
estimate.** -/
theorem theorem41B_of (hME : LSG.MEB.MultEstB) {m : ℕ} {B : Fin m → AbBlock} (An : ∀ k, AbBlockAn (B k))
    (Tay : TayAll B) : Theorem41B An := by
  intro d0 d1 V W Y hn hWV hW hYfg hYVL hTor hNR
  set Λ := latF An with hΛdef
  have hΛ : ∀ k, IsNsmulIn (Λ k) (B k).per := fun k => (An k).lat_nsmul
  have hΛle : ∀ k, Λ k ≤ (B k).per := fun k => (An k).lat_le
  /- 1. Generators and periods. -/
  obtain ⟨μ, y, hYy⟩ := exists_gens Y hYfg
  have hYmem : ∀ j, y j ∈ Y := fun j => hYy ▸ AddSubgroup.subset_closure ⟨j, rfl⟩
  have hyV : ∀ j, y j ∈ V := fun j => (hYVL _ (hYmem j)).1
  have hyL : ∀ j, y j ∈ LamB d0 d1 An := fun j => (hYVL _ (hYmem j)).2
  have hYL : ∀ u ∈ Y, u ∈ LamB d0 d1 An := fun u hu => (hYVL u hu).2
  have hspanY : Submodule.span ℚ (Y : Set (MEB.Tan d0 d1 B)) = Submodule.span ℚ (Set.range y) := by
    rw [← hYy, span_closure_range]
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ
      ((Y ⊓ PerL d0 d1 B Λ : AddSubgroup (MEB.Tan d0 d1 B)) : Set (MEB.Tan d0 d1 B))) := by
    have hle : Submodule.span ℚ ((Y ⊓ PerL d0 d1 B Λ : AddSubgroup (MEB.Tan d0 d1 B)) :
        Set (MEB.Tan d0 d1 B)) ≤ Submodule.span ℚ (Set.range y) := by
      rw [← hspanY]; exact Submodule.span_mono fun x hx => hx.1
    have : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y)) :=
      FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
    exact Submodule.finiteDimensional_of_le hle
  obtain ⟨ω, hωZ, hω⟩ := exists_periods (Y ⊓ PerL d0 d1 B Λ)
  have hωV : ∀ i, ω i ∈ V := fun i => (hYVL _ (hωZ i).1).1
  have hωP : ∀ i, ω i ∈ PerL d0 d1 B Λ := fun i => (hωZ i).2
  have hωC : LinearIndependent ℂ ω :=
    linIndep_of_torInj hTor ω hωV (fun i => perL_le hΛle (hωP i)) hω
  obtain ⟨K, _, _, ι, τ₀, Dt, hDty, hDtw⟩ := exists_LUDataA An W hW y hyL
  have hyV' : ∀ j, Dt.y j ∈ V := by rw [hDty]; exact hyV
  obtain ⟨C, hC, S₀, hP61⟩ :=
    prop61A 2 (by norm_num) An (Tay K ι) V W hWV hn Dt hyV' hDtw ω hωV hωP hωC hNR
  obtain ⟨C', hME'⟩ := hME d0 d1 m B
  /- 2. Constants. -/
  set G := ∑ k, (B k).g with hG
  set N := finrank ℂ V with hN
  set κ := rk (Y ⊓ PerL d0 d1 B Λ) with hκ
  set nn := d0 + d1 + G with hnn
  set q := d0 + d1 + G - N with hq
  set e := d1 + 2 * G - κ with he
  have hq1 : 1 ≤ q := by omega
  have he2 : 2 * q ≤ e := by omega
  have hnn1 : 1 ≤ nn := by omega
  have hqz : ((nn : ℕ) : ℤ) - (N : ℤ) = (q : ℤ) := by omega
  have hez : ((d1 + 2 * G : ℕ) : ℤ) - (κ : ℤ) = (e : ℤ) := by omega
  have hrkY : rk Y ≤ μ := by
    rw [rk, hspanY]
    exact (finrank_range_le_card _).trans (by simp)
  set lC := Real.log C with hlC
  set cT := Real.log (4 * nn) with hcT
  set lnn := Real.log nn with hlnn
  set cX := lC / q with hcX
  set c4 := Real.log (1 + Real.exp (-cX)) with hc4
  set K0b := Real.log C' + nn * cT + μ * lnn + nn * c4 with hK0b
  set Kb := q * K0b + nn * |lC| with hKb
  set Bb : ℝ := 2 * d0 * nn + q * nn with hBb
  have hnnR : (1 : ℝ) ≤ nn := by exact_mod_cast hnn1
  have hcT0 : 0 ≤ cT := Real.log_nonneg (by linarith)
  have hlnn0 : 0 ≤ lnn := Real.log_nonneg hnnR
  have hc40 : 0 ≤ c4 := Real.log_nonneg (by linarith [Real.exp_pos (-cX)])
  /- 3. The scale `S`. -/
  obtain ⟨S, ⟨⟨hE3, -⟩, ⟨hE4a, hE4b⟩⟩, hS0, hS3⟩ :=
    (((eventually_log_big (|lC| + q * cT) q).and (eventually_log_big Kb Bb)).and
      ((eventually_ge_atTop S₀).and (eventually_ge_atTop 3))).exists
  obtain ⟨D, L, μs, p, hα, hβ, hD, hne, hvan⟩ := hP61 S hS0
  set Δ := delta61 C e (2 * d0) q S with hΔdef
  obtain ⟨hΔ0, hlogΔ⟩ := log_delta61 (e := e) (d := 2 * d0) hC hq1 hS3
  set LS := Real.log S with hLS
  set ℓℓ := Real.log LS with hℓℓ
  set LΔ := Real.log Δ with hLΔ
  have hLS1 : 1 ≤ LS := log_ge_one hS3
  have hℓ0 : 0 ≤ ℓℓ := Real.log_nonneg hLS1
  have hℓLS : ℓℓ ≤ LS := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogΔ' : (q : ℝ) * LΔ = lC + e * LS + 2 * d0 * ℓℓ := by rw [hlogΔ]; push_cast; ring
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have heR : (2 : ℝ) * q ≤ e := by exact_mod_cast he2
  have hp2 : 0 ≤ ((e : ℝ) - 2 * q) * LS := mul_nonneg (by linarith) (by linarith)
  have hd2 : 0 ≤ 2 * (d0 : ℝ) * ℓℓ := by positivity
  have hX2 : cX ≤ LΔ - 2 * LS := by
    rw [hcX, div_le_iff₀ (by linarith)]
    linarith only [hp2, hd2, hlogΔ']
  /- 4. `T′`. -/
  set XT := Δ / (2 * nn * LS) with hXT
  have hXT0 : 0 < XT := by positivity
  have hlogXT : Real.log XT = LΔ - Real.log (2 * nn) - ℓℓ := by
    rw [hXT, Real.log_div hΔ0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      hLΔ, hℓℓ]
    ring
  have hcT' : cT = Real.log 2 + Real.log (2 * nn) := by
    rw [hcT, ← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have hLΔT : cT + ℓℓ < LΔ := by
    have h1 : (q : ℝ) * (cT + ℓℓ) < q * LΔ := by
      rw [hlogΔ']
      have i1 := neg_abs_le lC
      have i2 : 0 ≤ ((e : ℝ) - 1) * LS := mul_nonneg (by linarith) (by linarith)
      linarith only [i1, i2, hd2, hE3]
    exact lt_of_mul_lt_mul_left h1 (by linarith)
  have hXT2 : 2 ≤ XT := by
    rw [← Real.log_le_log_iff (by norm_num) hXT0, hlogXT]; linarith
  obtain ⟨hT1, hlogT⟩ := floor_ge_half hXT2
  set T' := ⌊XT⌋₊ with hT'
  have bT : LΔ - cT - ℓℓ ≤ Real.log T' := by rw [hlogXT] at hlogT; linarith only [hlogT, hcT']
  have hmult : ((nn * T' : ℕ) : ℝ) < Δ / LS := by
    have h1 : (T' : ℝ) ≤ XT := Nat.floor_le hXT0.le
    have h2 : (nn : ℝ) * XT = Δ / (2 * LS) := by rw [hXT]; field_simp
    have h3 : Δ / (2 * LS) < Δ / LS := div_lt_div_of_pos_left hΔ0 (by linarith) (by linarith)
    push_cast
    calc (nn : ℝ) * T' ≤ nn * XT := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Δ / (2 * LS) := h2
      _ < Δ / LS := h3
  /- 5. The degrees. -/
  set X0 := Δ / LS ^ 2 with hX0
  set X1 := Δ / (S : ℝ) with hX1
  set X2 := Δ / (S : ℝ) ^ 2 with hX2d
  have hS0R : (0 : ℝ) < S := by have : (3 : ℝ) ≤ S := by exact_mod_cast hS3
                                linarith
  have hlX0 : Real.log X0 = LΔ - 2 * ℓℓ := by
    rw [hX0, Real.log_div hΔ0.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hlX1 : Real.log X1 = LΔ - LS := by rw [hX1, Real.log_div hΔ0.ne' (by positivity)]
  have hlX2 : Real.log X2 = LΔ - 2 * LS := by
    rw [hX2d, Real.log_div hΔ0.ne' (by positivity), Real.log_pow]; push_cast; ring
  set D0' := ⌊X0⌋₊ + 1 with hD0'
  set D1' := ⌊X1⌋₊ + 1 with hD1'
  have b0 : Real.log D0' ≤ LΔ - 2 * ℓℓ + c4 := by
    have := log_succ_le_of_le (Nat.floor_le (by positivity : 0 ≤ X0))
      (show cX ≤ Real.log X0 by rw [hlX0]; linarith) (by positivity)
    rw [hlX0] at this
    change Real.log ((⌊X0⌋₊ + 1 : ℕ) : ℝ) ≤ _
    push_cast; exact this
  have b1 : Real.log D1' ≤ LΔ - LS + c4 := by
    have := log_succ_le_of_le (Nat.floor_le (by positivity : 0 ≤ X1))
      (show cX ≤ Real.log X1 by rw [hlX1]; linarith) (by positivity)
    rw [hlX1] at this
    change Real.log ((⌊X1⌋₊ + 1 : ℕ) : ℝ) ≤ _
    push_cast; exact this
  have b2 : Real.log ((D + 1 : ℕ) : ℝ) ≤ LΔ - 2 * LS + c4 := by
    have := log_succ_le_of_le hD (show cX ≤ Real.log X2 by rw [hlX2]; linarith) (by positivity)
    rw [hlX2] at this; push_cast; exact this
  set M := S / nn with hM
  have bM : LS - lnn ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
    have h1 : S < (M + 1) * nn := by
      rw [hM, add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)
    have h2 : (S : ℝ) / nn ≤ ((M + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by linarith)]; exact_mod_cast h1.le
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_div (by positivity) (by positivity)] at h3
    exact h3
  /- 6. The polynomial and the multiplicity estimate. -/
  set S' := gridPtsB y M with hS'
  set P := PW μs p with hP
  have h0S' : (0 : MEB.GPt d0 d1 B) ∈ S' :=
    mem_gridPtsB.mpr ⟨0, fun _ => Nat.zero_le _, by simp⟩
  have hA : ∀ l, ∑ i, (μs l).α i ≤ D0' := fun l => by
    have := Nat.le_floor (hα l)
    rw [hD0']; omega
  have hB : ∀ l, ∑ j, (μs l).β j ≤ D1' := fun l => by
    have := Nat.le_floor (hβ l)
    rw [hD1']; omega
  obtain ⟨x, hx⟩ := hne
  have hvan' : ∀ σ ∈ sigB S' nn, OrdGtB W P (nn * T') σ := by
    intro σ hσ
    obtain ⟨h, hh, rfl⟩ := sig_gridPtsB hσ
    have hhS : ∀ j, h j ≤ S := fun j =>
      (hh j).trans (by rw [hM, mul_comm]; exact Nat.div_mul_le_self S nn)
    have hv := hvan h hhS
    rw [hDty] at hv
    refine ordGtB_PW μs p W _ fun w hw k hk => hv w hw k ?_
    have hk' : (k : ℝ) ≤ ((nn * T' : ℕ) : ℝ) := by exact_mod_cast hk
    linarith only [hk', hmult]
  obtain ⟨O, hOp, hcnt⟩ := hME' W S' P T' D0' D1' (D + 1) h0S' (isHomB_PW μs p)
    (PW_mem_FLE μs p hA hB) (PW_notMem_IGsem μs p hx) hT1
    (Nat.le_add_left _ _) (Nat.le_add_left _ _) (Nat.le_add_left _ _) hvan'
  /- 7. Counting and the inequality. -/
  set Z := O.tan.toAddSubgroup ⊔ PerL d0 d1 B Λ with hZ
  have hZmem : ∀ u, MEB.expG d0 d1 B u ∈ O.grp → u ∈ Submodule.span ℚ (Z : Set (MEB.Tan d0 d1 B)) := by
    intro u hu
    obtain ⟨Nu, hNu, hNuZ⟩ := O.htil_perL hΛ hu
    exact mem_span_rat_of_nsmul hNu (Submodule.subset_span hNuZ)
  obtain ⟨F, hFg, hFd, hFc⟩ :=
    exists_inequiv_grid_gen (MEB.expG d0 d1 B) O.grp O.grp_sub.zero_mem Z hZmem y M
  have hc := hcnt F (fun g hg => mem_gridPtsB.mpr (hFg g hg)) hFd
  rw [hFc, hYy] at hc
  set τ := finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan) with hτ
  set lam := rk Y - rk (Y ⊓ Z) with hlam
  have h1 := log_count (finrank_h0_leB O) (finrank_U_leB O) (finrank_t_leB O) hT1
    (Nat.le_add_left _ _) (Nat.le_add_left _ _) (Nat.le_add_left _ _) (Nat.le_add_left _ _) hc
    bT bM b0 b1 b2
  have hτnn : τ ≤ nn := by
    have := Submodule.finrank_mono hWV
    have := Submodule.finrank_mono (inf_le_left : W ⊓ O.tan ≤ W)
    omega
  have hlamμ : lam ≤ μ := by omega
  have hδnn : d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) ≤ nn := by
    have := finrank_U_leB O; omega
  have hcore := core_ineq (q := q) (e := e) (d0 := d0) (lam := lam) (τ := τ)
    (δ0 := d0 - finrank ℂ O.h0) (δ1 := finrank ℚ O.U) (δ2 := G - finrank ℂ O.t) hq1 (by omega)
    h1 hlogΔ' (Kb := Kb)
    (Bb := Bb) ?hK ?hB (by linarith) hℓ0 hE4a hE4b
  case hK =>
    have e1 : ((τ : ℕ) : ℝ) ≤ nn := by exact_mod_cast hτnn
    have e2 : ((lam : ℕ) : ℝ) ≤ μ := by exact_mod_cast hlamμ
    have e3 : ((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) : ℕ) : ℝ) ≤ nn := by
      exact_mod_cast hδnn
    have e4 : (((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) : ℕ) : ℝ) - τ) * lC ≤
        nn * |lC| := by
      have : |((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) : ℕ) : ℝ) - τ| ≤ nn := by
        rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) τ,
          Nat.cast_nonneg (α := ℝ) (d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t))]
      calc _ ≤ |((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) : ℕ) : ℝ) - τ| * |lC| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ nn * |lC| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have e5 : Real.log C' + τ * cT + lam * lnn +
        ((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) : ℕ) : ℝ) * c4 ≤ K0b := by
      rw [hK0b]
      have := mul_le_mul_of_nonneg_right e1 hcT0
      have := mul_le_mul_of_nonneg_right e2 hlnn0
      have := mul_le_mul_of_nonneg_right e3 hc40
      linarith
    rw [hKb]
    have m5 := mul_le_mul_of_nonneg_left e5 (by linarith only [hqR] : (0 : ℝ) ≤ q)
    linarith only [m5, e4]
  case hB =>
    have e3 : ((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) : ℕ) : ℝ) ≤ nn := by
      exact_mod_cast hδnn
    rw [hBb]
    have h01 : (0 : ℝ) ≤ 2 * d0 := by positivity
    have h02 : (0 : ℝ) ≤ q := by positivity
    have := mul_le_mul_of_nonneg_left (show ((d0 - finrank ℂ O.h0 + finrank ℚ O.U +
      (G - finrank ℂ O.t) : ℕ) : ℝ) - τ ≤ nn by linarith [Nat.cast_nonneg (α := ℝ) τ]) h01
    have := mul_le_mul_of_nonneg_left (show (τ : ℝ) - 2 * ((d0 - finrank ℂ O.h0 : ℕ) : ℝ) ≤ nn by
      have : ((τ : ℕ) : ℝ) ≤ nn := by exact_mod_cast hτnn
      linarith [Nat.cast_nonneg (α := ℝ) (d0 - finrank ℂ O.h0)]) h02
    linarith
  obtain ⟨hineq, hτδ⟩ := hcore
  have hτδ' := hτδ (obstr_delta_posB O hOp)
  /- 8. The `ℚ̄`-rational subgroup data. -/
  obtain ⟨H, hHlam, hH1, hH2, hHδ⟩ :=
    exists_subgroupDataB O W (PerL d0 d1 B Λ) (fun p hp => hp.1) Y (fun y hy => (hYL y hy).1)
  have hpos : (1 : ℤ) ≤ (H.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ) : ℤ) := by
    have : ((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) : ℕ) : ℤ) - (τ : ℤ) ≥ 1 := by
      omega
    linarith
  refine ⟨H, ?_, ?_, ?_⟩
  · change H.δ ≠ 0
    omega
  · omega
  · rw [hHlam, hH1, hH2]
    rw [hqz, hez]
    have hineq' : ((lam + finrank ℚ O.U + 2 * (G - finrank ℂ O.t) : ℕ) : ℤ) * (q : ℤ) ≤
        (e : ℤ) * (((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) : ℕ) : ℤ) - τ) := by
      have e1 : ((lam + finrank ℚ O.U + 2 * (G - finrank ℂ O.t) : ℕ) : ℤ) * (q : ℤ) =
          ((q * (lam + finrank ℚ O.U + 2 * (G - finrank ℂ O.t)) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, mul_comm]
      rw [e1]; exact hineq
    have he0 : (0 : ℤ) ≤ e := Int.natCast_nonneg e
    calc ((lam + finrank ℚ O.U + 2 * (G - finrank ℂ O.t) : ℕ) : ℤ) * (q : ℤ)
        ≤ (e : ℤ) * (((d0 - finrank ℂ O.h0 + finrank ℚ O.U + (G - finrank ℂ O.t) : ℕ) : ℤ) - τ) :=
          hineq'
      _ ≤ (e : ℤ) * ((H.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left hHδ he0
      _ = _ := by ring

end LSG.W88
