/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarVSec7Count
import LSG.MEBV.SubgroupMain

/-!
# M2.6.8: W88 §7 for `G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)` from `MultEstV`

**`theorem41AbVarVPer_of (hME : MEBV.MultEstV) An Tay M hM hMa hr : Theorem41AbVarVPer An M`**, generic over vector
block families with analytic packages `An` and Taylor packages `Tay` over every number field, for `M` onto with
algebraic entries and `r ≤ 1`. **`theorem41AbVarVPer`**: the unconditional form, from
`LSG.MEBV.multEstV_holds`.

Proof (copy of `Sec7V.theorem41VecLA_of_ME` and `AbVarSec7.theorem41B_of`):
1. Generators `y_j` of `Y`, `κ = rk (Y ∩ PerAV)` independent periods, `ℂ`-independent by toric injectivity
   (`linIndep_of_torInjAV`).
2. `exists_LUDataAV` and `prop61AV` with `b = 2`.
3. `MultEstV` on `G̃_r` (`hME d₀ r d₁ m B M hM`) for `P = PWV` (`K_M`-invariant, block degree `D₂ = D + F + 1`,
   trailing degree `≤ F`), points `exp(liftTA(Σ h_j y_j))`, `h_j ≤ ⌊S/n⌋`, `n = dim G̃_r`, `T′ = ⌊Δ/(2n log S)⌋`,
   `D₀ = ⌊2Δ/log²S⌋ + 1` (covers `Σα + Σφ`), `D₁ = ⌊Δ/S⌋ + 1`; order from `ordGtV_PWV`.
4. `exists_inequiv_grid_genAV` with `htilG_le_span`; `log_count` and `core_ineq` with `t₂ = t2G + m` against
   `D₂^{Σ(g_k+1)+r}`.
5. `exists_subgroupDataAV_rat` (`r ≤ 1`).
-/

open MvPolynomial Module Filter LSG.Aux LSG.AuxA LSG.AuxAV

noncomputable section

namespace LSG.W88

open LSG.W88.AVS

open LSG.MEBV (VBlock ObstrDataBV expG sigB OrdGtV TrailDeg dimG)
open LSG.W88.Vec (AlgMat)

set_option maxHeartbeats 4000000 in
-- the assembly of W88 §7 elaborates many real inequalities
/-- **W88 Theorem 4.1 (under (NR) and toric injectivity) for `G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)`
from the multiplicity estimate** (`M` onto with algebraic entries, `r ≤ 1`). -/
theorem theorem41AbVarVPer_of (hME : LSG.MEBV.MultEstV) {m r : ℕ} {B : Fin m → VBlock}
    (An : ∀ k, VBlockAn (B k)) (Tay : TayAllV B) (M : Matrix (Fin r) (Fin m) ℂ)
    (hM : Function.Surjective M.mulVec) (hMa : AlgMat M) (hr : r ≤ 1) : Theorem41AbVarVPer An M := by
  intro d0 d1 V W Y hn hWV hW hYfg hYVL hTor hNR
  /- 1. Generators and periods. -/
  obtain ⟨μ, y, hYy⟩ := exists_gens Y hYfg
  have hYmem : ∀ j, y j ∈ Y := fun j => hYy ▸ AddSubgroup.subset_closure ⟨j, rfl⟩
  have hyV : ∀ j, y j ∈ V := fun j => (hYVL _ (hYmem j)).1
  have hyL : ∀ j, y j ∈ LamAV d0 d1 An M := fun j => (hYVL _ (hYmem j)).2
  have hYL : ∀ u ∈ Y, u ∈ LamAV d0 d1 An M := fun u hu => (hYVL u hu).2
  have hspanY : Submodule.span ℚ (Y : Set (TanAV d0 d1 r B)) = Submodule.span ℚ (Set.range y) := by
    rw [← hYy, span_closure_range]
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ
      ((Y ⊓ PerAV d0 d1 An M : AddSubgroup (TanAV d0 d1 r B)) : Set (TanAV d0 d1 r B))) := by
    have hle : Submodule.span ℚ ((Y ⊓ PerAV d0 d1 An M : AddSubgroup (TanAV d0 d1 r B)) :
        Set (TanAV d0 d1 r B)) ≤ Submodule.span ℚ (Set.range y) := by
      rw [← hspanY]; exact Submodule.span_mono fun x hx => hx.1
    have : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y)) :=
      FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
    exact Submodule.finiteDimensional_of_le hle
  obtain ⟨ω, hωZ, hω⟩ := exists_periods (Y ⊓ PerAV d0 d1 An M)
  have hωV : ∀ i, ω i ∈ V := fun i => (hYVL _ (hωZ i).1).1
  have hωP : ∀ i, ω i ∈ PerAV d0 d1 An M := fun i => (hωZ i).2
  have hωC : LinearIndependent ℂ ω :=
    linIndep_of_torInjAV M hTor ω hωV (fun i => PerAV_le_PerAVf An M (hωP i)) hω
  obtain ⟨K, _, _, ι, τ₀, Dt, hDty, hDtw⟩ := exists_LUDataAV An M hMa W hW y hyL
  have hyV' : ∀ j, Dt.y j ∈ V := by rw [hDty]; exact hyV
  obtain ⟨C, hC, S₀, hP61⟩ :=
    prop61AV 2 (by norm_num) An (Tay K ι) M V W hWV (by omega) Dt hyV' hDtw ω hωV hωP hωC hNR
  obtain ⟨C', hME'⟩ := hME d0 r d1 m B M hM
  /- 2. Constants. -/
  set N := finrank ℂ V with hN
  set κ := rk (Y ⊓ PerAV d0 d1 An M) with hκ
  set nn := dimG (d0 + r) d1 B with hnn
  set q := d0 + d1 + (∑ k, (B k).g + r) - N with hq
  set e := d1 + 2 * (∑ k, (B k).g + r) - κ with he
  have hnnE : nn = d0 + r + d1 + ∑ k, ((B k).g + 1) := rfl
  have hsg := sum_g_succ (B := B)
  have hq1 : 1 ≤ q := by omega
  have he2 : 2 * q ≤ e := by omega
  have hnn1 : 1 ≤ nn := by omega
  have hqz : ((d0 + d1 + ∑ k, (B k).g + r : ℕ) : ℤ) - (N : ℤ) = (q : ℤ) := by omega
  have hez : ((d1 + 2 * (∑ k, (B k).g + r) : ℕ) : ℤ) - (κ : ℤ) = (e : ℤ) := by omega
  have hrkY : rk Y ≤ μ := by
    rw [rk, hspanY]
    exact (finrank_range_le_card _).trans (by simp)
  set lC := Real.log C with hlC
  set cT := Real.log (4 * nn) with hcT
  set lnn := Real.log nn with hlnn
  set cX := lC / q with hcX
  set c4 := Real.log 2 + Real.log (1 + Real.exp (-cX)) with hc4
  set K0b := Real.log C' + nn * cT + μ * lnn + nn * c4 with hK0b
  set Kb := q * K0b + nn * |lC| with hKb
  set Bb : ℝ := 2 * d0 * nn + q * nn with hBb
  have hnnR : (1 : ℝ) ≤ nn := by exact_mod_cast hnn1
  have hcT0 : 0 ≤ cT := Real.log_nonneg (by linarith)
  have hlnn0 : 0 ≤ lnn := Real.log_nonneg hnnR
  have hc40' : 0 ≤ Real.log (1 + Real.exp (-cX)) :=
    Real.log_nonneg (by linarith [Real.exp_pos (-cX)])
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc40 : 0 ≤ c4 := by linarith
  /- 3. The scale `S`. -/
  obtain ⟨S, ⟨⟨hE3, -⟩, ⟨hE4a, hE4b⟩⟩, hS0, hS3⟩ :=
    (((eventually_log_big (|lC| + q * cT) q).and (eventually_log_big Kb Bb)).and
      ((eventually_ge_atTop S₀).and (eventually_ge_atTop 3))).exists
  obtain ⟨D, F, L, μs, p, hα, hβ, hD, ⟨x, hx, hθ⟩, hvan⟩ := hP61 S hS0
  set Δ := delta61 C e (2 * d0) q S with hΔdef
  obtain ⟨hΔ0, hlogΔ⟩ := log_delta61 (e := e) (d := 2 * d0) hC hq1 hS3
  set LS := Real.log S with hLS
  set ℓℓ := Real.log LS with hℓℓ
  set LΔ := Real.log Δ with hLΔ
  have hLS1 : 1 ≤ LS := log_ge_one hS3
  have hℓ0 : 0 ≤ ℓℓ := Real.log_nonneg hLS1
  have hℓLS : ℓℓ ≤ LS := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogΔ' : (q : ℝ) * LΔ = lC + e * LS + 2 * d0 * ℓℓ := by rw [hlogΔ]; push_cast; ring
  have hSR : (3 : ℝ) ≤ S := by exact_mod_cast hS3
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
  set X0' := 2 * X0 with hX0'
  set X1 := Δ / (S : ℝ) with hX1
  set X2 := Δ / (S : ℝ) ^ 2 with hX2d
  have hS0R : (0 : ℝ) < S := by linarith
  have hlX0 : Real.log X0' = Real.log 2 + (LΔ - 2 * ℓℓ) := by
    rw [hX0', Real.log_mul (by norm_num) (by positivity), hX0,
      Real.log_div hΔ0.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hlX1 : Real.log X1 = LΔ - LS := by rw [hX1, Real.log_div hΔ0.ne' (by positivity)]
  have hlX2 : Real.log X2 = LΔ - 2 * LS := by
    rw [hX2d, Real.log_div hΔ0.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hLSS : LS ≤ S := by
    have := Real.log_le_sub_one_of_pos hS0R
    linarith
  have hX20 : X2 ≤ X0 := by
    rw [hX2d, hX0]
    exact div_le_div_of_nonneg_left hΔ0.le (by positivity)
      (pow_le_pow_left₀ (by linarith) hLSS 2)
  set D0' := ⌊X0'⌋₊ + 1 with hD0'
  set D1' := ⌊X1⌋₊ + 1 with hD1'
  have b0 : Real.log D0' ≤ LΔ - 2 * ℓℓ + c4 := by
    have := log_succ_le_of_le (Nat.floor_le (by positivity : 0 ≤ X0'))
      (show cX ≤ Real.log X0' by rw [hlX0]; linarith) (by positivity)
    rw [hlX0] at this
    change Real.log ((⌊X0'⌋₊ + 1 : ℕ) : ℝ) ≤ _
    push_cast; linarith
  have b1 : Real.log D1' ≤ LΔ - LS + c4 := by
    have := log_succ_le_of_le (Nat.floor_le (by positivity : 0 ≤ X1))
      (show cX ≤ Real.log X1 by rw [hlX1]; linarith) (by positivity)
    rw [hlX1] at this
    change Real.log ((⌊X1⌋₊ + 1 : ℕ) : ℝ) ≤ _
    push_cast; linarith
  have b2 : Real.log ((D + F + 1 : ℕ) : ℝ) ≤ LΔ - 2 * LS + c4 := by
    have := log_succ_le_of_le hD (show cX ≤ Real.log X2 by rw [hlX2]; linarith) (by positivity)
    rw [hlX2] at this; push_cast at this ⊢; linarith
  set Mg := S / nn with hMg
  have bM : LS - lnn ≤ Real.log ((Mg + 1 : ℕ) : ℝ) := by
    have h1 : S < (Mg + 1) * nn := by
      rw [hMg, add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)
    have h2 : (S : ℝ) / nn ≤ ((Mg + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by linarith)]; exact_mod_cast h1.le
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_div (by positivity) (by positivity)] at h3
    exact h3
  /- 6. The polynomial and the multiplicity estimate. -/
  set S' := gridPtsAV y Mg with hS'
  set P := PWV M μs p with hP
  set W' := W.map (liftTA (d₀ := d0) (d₁ := d1) (r := r) (B := B)) with hW'
  have h0S' : (0 : LSG.MEBV.GPt (d0 + r) d1 B) ∈ S' :=
    mem_gridPtsAV.mpr ⟨0, fun _ => Nat.zero_le _, by
      rw [show (∑ j, (0 : Fin μ → ℕ) j • y j) = 0 by simp, map_zero, map_zero]⟩
  have hA : ∀ l, ∑ i, (μs l).μ.α i + ∑ i, (μs l).φ i ≤ D0' := fun l => by
    have hsum : ((∑ i, (μs l).μ.α i + ∑ i, (μs l).φ i : ℕ) : ℝ) ≤ X0' := by
      have h1' : ((∑ i, (μs l).μ.α i : ℕ) : ℝ) ≤ X0 := hα l
      have h2' : ((∑ i, (μs l).φ i : ℕ) : ℝ) ≤ X0 := by
        have h3' : ((∑ i, (μs l).φ i : ℕ) : ℝ) ≤ ((D + F : ℕ) : ℝ) := by
          exact_mod_cast (μs l).hφ.trans (Nat.le_add_left F D)
        exact h3'.trans (hD.trans hX20)
      rw [Nat.cast_add, hX0']; linarith
    have := Nat.le_floor hsum
    rw [hD0']; omega
  have hB : ∀ l, ∑ j, (μs l).μ.β j ≤ D1' := fun l => by
    have := Nat.le_floor (hβ l)
    rw [hD1']; omega
  have hPtr : TrailDeg (d₀ := d0) (D + F + 1) P :=
    trailDegA_mono (by omega) (trailDeg_PWV M μs p)
  have hvan' : ∀ σ ∈ sigB S' nn, OrdGtV W' P (nn * T') σ := by
    intro σ hσ
    obtain ⟨h, hh, rfl⟩ := sig_gridPtsAV hσ
    have hhS : ∀ j, h j ≤ S := fun j =>
      (hh j).trans (by rw [hMg, mul_comm]; exact Nat.div_mul_le_self S nn)
    have hv := hvan h hhS
    rw [hDty] at hv
    refine ordGtV_PWV M μs p W _ fun w hw k hk => hv w hw k ?_
    have hk' : (k : ℝ) ≤ ((nn * T' : ℕ) : ℝ) := by exact_mod_cast hk
    linarith only [hk', hmult]
  obtain ⟨O, hOp, hcnt⟩ := hME' W' S' P T' D0' D1' (D + F + 1) h0S' (isHomV_PWV M μs p)
    (PWV_mem_FLE M μs p hA hB) hPtr (invarKV_PWV M μs p) (PWV_notMem_IGsem M μs p hx hθ) hT1
    (Nat.le_add_left _ _) (Nat.le_add_left _ _) (Nat.le_add_left _ _) hvan'
  /- 7. Counting and the inequality. -/
  obtain ⟨Fg, hFg, hFd, hFc⟩ := exists_inequiv_grid_genAV
    ((expG (d0 + r) d1 B).comp (liftTA (d₀ := d0) (d₁ := d1) (r := r) (B := B)).toAddMonoidHom) O.grp
    O.grp_sub.zero_mem ((tanG O).toAddSubgroup ⊔ PerAV d0 d1 An M) (fun u hu => htilG_le_span O An hu) y Mg
  have hc := hcnt Fg (fun g hg => by
    obtain ⟨h, hh, rfl⟩ := hFg g hg
    exact mem_gridPtsAV.mpr ⟨h, hh, rfl⟩) hFd
  rw [hFc, hYy, tau_eq O W] at hc
  set τ := finrank ℂ W - finrank ℂ ↥(W ⊓ tanG O) with hτ
  set lam := rk Y - rk (Y ⊓ ((tanG O).toAddSubgroup ⊔ PerAV d0 d1 An M)) with hlam
  set u := finrank ℚ O.U with hu
  have hu1 : u ≤ d1 := by simpa using Submodule.finrank_le O.U
  have ht2 : O.t2 ≤ ∑ k, ((B k).g + 1) + r := by have := t2G_le O; rw [t2_eq]; omega
  have h1 := log_count (t0_leAV O) hu1 ht2 hT1 (Nat.le_add_left _ _) (Nat.le_add_left _ _)
    (Nat.le_add_left _ _) (Nat.le_add_left _ _) hc bT bM b0 b1 b2
  have hτnn : τ ≤ nn := by
    have := Submodule.finrank_mono hWV
    have := Submodule.finrank_mono (inf_le_left : W ⊓ tanG O ≤ W)
    omega
  have hlamμ : lam ≤ μ := by omega
  have hδnn : d0 - O.t0 + u + (∑ k, ((B k).g + 1) + r - O.t2) ≤ nn := by omega
  have hcore := core_ineq (q := q) (e := e) (d0 := d0) (lam := lam) (τ := τ)
    (δ0 := d0 - O.t0) (δ1 := u) (δ2 := ∑ k, ((B k).g + 1) + r - O.t2) hq1 (by omega)
    h1 hlogΔ' (Kb := Kb) (Bb := Bb) ?hK ?hB (by linarith) hℓ0 hE4a hE4b
  case hK =>
    have e1 : ((τ : ℕ) : ℝ) ≤ nn := by exact_mod_cast hτnn
    have e2 : ((lam : ℕ) : ℝ) ≤ μ := by exact_mod_cast hlamμ
    have e3 : ((d0 - O.t0 + u + (∑ k, ((B k).g + 1) + r - O.t2) : ℕ) : ℝ) ≤ nn := by
      exact_mod_cast hδnn
    have e4 : (((d0 - O.t0 + u + (∑ k, ((B k).g + 1) + r - O.t2) : ℕ) : ℝ) - τ) * lC ≤ nn * |lC| := by
      have : |((d0 - O.t0 + u + (∑ k, ((B k).g + 1) + r - O.t2) : ℕ) : ℝ) - τ| ≤ nn := by
        rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) τ,
          Nat.cast_nonneg (α := ℝ) (d0 - O.t0 + u + (∑ k, ((B k).g + 1) + r - O.t2))]
      calc _ ≤ |((d0 - O.t0 + u + (∑ k, ((B k).g + 1) + r - O.t2) : ℕ) : ℝ) - τ| * |lC| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ nn * |lC| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have e5 : Real.log C' + τ * cT + lam * lnn +
        ((d0 - O.t0 + u + (∑ k, ((B k).g + 1) + r - O.t2) : ℕ) : ℝ) * c4 ≤ K0b := by
      rw [hK0b]
      have := mul_le_mul_of_nonneg_right e1 hcT0
      have := mul_le_mul_of_nonneg_right e2 hlnn0
      have := mul_le_mul_of_nonneg_right e3 hc40
      linarith
    rw [hKb]
    have m5 := mul_le_mul_of_nonneg_left e5 (by linarith only [hqR] : (0 : ℝ) ≤ q)
    linarith only [m5, e4]
  case hB =>
    have e3 : ((d0 - O.t0 + u + (∑ k, ((B k).g + 1) + r - O.t2) : ℕ) : ℝ) ≤ nn := by
      exact_mod_cast hδnn
    have e1 : ((τ : ℕ) : ℝ) ≤ nn := by exact_mod_cast hτnn
    rw [hBb]
    have h01 : (0 : ℝ) ≤ 2 * d0 := by positivity
    have h02 : (0 : ℝ) ≤ q := by positivity
    have := mul_le_mul_of_nonneg_left (show ((d0 - O.t0 + u + (∑ k, ((B k).g + 1) + r - O.t2) : ℕ) : ℝ) -
      τ ≤ nn by linarith [Nat.cast_nonneg (α := ℝ) τ]) h01
    have := mul_le_mul_of_nonneg_left (show (τ : ℝ) - 2 * ((d0 - O.t0 : ℕ) : ℝ) ≤ nn by
      linarith [Nat.cast_nonneg (α := ℝ) (d0 - O.t0)]) h02
    linarith
  obtain ⟨hineq, hτδ⟩ := hcore
  have hτδ' := hτδ (delta_posAV O hOp)
  /- 8. The `ℚ̄`-rational subgroup data. -/
  obtain ⟨H, hHlam, hH1, hH2, hHδ⟩ := exists_subgroupDataAV_rat O hr An W Y hYL
  have h2eq : ∑ k, ((B k).g + 1) + r - O.t2 = ∑ k, (B k).g + r - t2G O := by rw [t2_eq]; omega
  have ht0 := t0_eq O
  rw [h2eq, ht0] at hineq hτδ'
  have hpos : (1 : ℤ) ≤ (H.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ) : ℤ) := by
    have : ((d0 - finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) + u + (∑ k, (B k).g + r - t2G O) : ℕ) :
        ℤ) - (τ : ℤ) ≥ 1 := by omega
    linarith
  refine ⟨H, ?_, ?_, ?_⟩
  · change H.δ ≠ 0
    omega
  · omega
  · rw [hHlam, hH1, hH2, hqz, hez]
    have hineq' : ((lam + u + 2 * (∑ k, (B k).g + r - t2G O) : ℕ) : ℤ) * (q : ℤ) ≤
        (e : ℤ) * (((d0 - finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) + u +
          (∑ k, (B k).g + r - t2G O) : ℕ) : ℤ) - τ) := by
      have e1 : ((lam + u + 2 * (∑ k, (B k).g + r - t2G O) : ℕ) : ℤ) * (q : ℤ) =
          ((q * (lam + u + 2 * (∑ k, (B k).g + r - t2G O)) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, mul_comm]
      rw [e1]; exact hineq
    have he0 : (0 : ℤ) ≤ e := Int.natCast_nonneg e
    calc ((lam + u + 2 * (∑ k, (B k).g + r - t2G O) : ℕ) : ℤ) * (q : ℤ)
        ≤ (e : ℤ) * (((d0 - finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) + u +
            (∑ k, (B k).g + r - t2G O) : ℕ) : ℤ) - τ) := hineq'
      _ ≤ (e : ℤ) * ((H.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left hHδ he0
      _ = _ := by ring

/-- **W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)`, unconditionally** (`M` onto with
algebraic entries, `r ≤ 1`; the multiplicity estimate is `LSG.MEBV.multEstV_holds`). -/
theorem theorem41AbVarVPer {m r : ℕ} {B : Fin m → VBlock} (An : ∀ k, VBlockAn (B k)) (Tay : TayAllV B)
    (M : Matrix (Fin r) (Fin m) ℂ) (hM : Function.Surjective M.mulVec) (hMa : AlgMat M) (hr : r ≤ 1) :
    Theorem41AbVarVPer An M :=
  theorem41AbVarVPer_of LSG.MEBV.multEstV_holds An Tay M hM hMa hr

end LSG.W88
