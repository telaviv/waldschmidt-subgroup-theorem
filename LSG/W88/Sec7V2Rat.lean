/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7VRat
import LSG.W88.V5d2Frame

/-!
# W88 §7 for the class `𝒞` with `d₀ = 0`, `r ≤ 2`: the rationality repair (`STAGE6_MXP.md` §2.2)

For the complex obstruction `T′ = tanG O = Γ_full + U^⊥ + perTan t` (`d₀ = 0`, so
`Γ_full ⊆ ℂ^r` is the fibre part) two rational members are compared with `T′`:
* `T_S = (dataRat O).tan ⊆ T′` (`Γ″` = algebraic span of `Γ_full`): same `λ` (`LiftAlg`,
  `inf_tanPerV_eq`), `δ` and `δ₂` grow by `j = dim T′ − dim T_S`; it works when
  `dim (W ∩ T_S) ≥ dim (W ∩ T′)` (uses `2q ≤ e`);
* `T_E = (dataTop O).tan ⊇ T′` (`Γ = ℂ^r`): `λ` does not grow, `δ₂` does not grow, and
  `δ − τ` is unchanged as soon as `dim (W ∩ T_E) = dim (W ∩ T′) + dim T_E/T′`.
**One of them works** (`exists_subgroupDataV_rat2`): if `T_S` fails then `Γ_full ≠ 0` is not
rational, so `dim T_E/T′ ≤ 1` (`r ≤ 2`); if `T_E` fails too, `W ∩ T′ = W ∩ T_E` is rational (a
frame of the member `dataTop O`), and every algebraic vector of `T′` lies in `T_S`
(`alg_mem_dataRat`, `PerTanRat`), so `W ∩ T′ ⊆ T_S`: a contradiction.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module LSG.MEV
open LSG.W88.Vec (TanV PerV LamV AlgMat etaV zetaV vecIncl torIncl g2Incl perTanId perTan RatPair
  AlgPair SubgroupDataV LiftAlg PerTanRat RatSubV AlgVecV fibreV)

noncomputable section

namespace LSG.W88

variable {d0 r d1 m : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

section Rat2

variable (O : ObstrDataV d0 r d1 Ls M)

/-- **Every algebraic vector of `T′` lies in `T(dataRat O)`** (`PerTanRat`: algebraic lifts). -/
theorem alg_mem_dataRat (hPT : PerTanRat Ls) (hM : AlgMat M) {x : TanV d0 d1 m r}
    (hx : x ∈ tanG O) (hxa : AlgVecV x) : x ∈ (dataRat O).tan := by
  obtain ⟨w0, hw0⟩ := exists_perTanId O.S.t_ab (piZ_tanG O hx)
  obtain ⟨s, hs, hsa, hs1⟩ := LSG.W88.V5d.exists_alg_preimage (hPT _ O.S.t_ab)
    (LinearMap.fst ℂ (Fin m → ℂ) (Fin m → ℂ)) (fun v hv i => hv.1 i)
    (⟨(x.2.2.1, w0), hw0, rfl⟩ : x.2.2.1 ∈ (perTanId Ls O.S.t).map (LinearMap.fst ℂ _ _))
    (fun i => hxa.2.2.1 i)
  have hw : (x.2.2.1, s.2) ∈ perTanId Ls O.S.t := by
    have : s = (x.2.2.1, s.2) := Prod.ext hs1 rfl
    rw [← this]; exact hs
  have hvec : (x.1, x.2.2.2 - M.mulVec s.2) ∈ gamFull O := by
    change vecIncl (x.1, x.2.2.2 - M.mulVec s.2) ∈ tanG O
    have : vecIncl (x.1, x.2.2.2 - M.mulVec s.2) =
        x - torIncl x.2.1 - (g2Incl (x.2.2.1, M.mulVec s.2) : TanV d0 d1 m r) := by ext <;> simp
    rw [this]
    exact (tanG O).sub_mem ((tanG O).sub_mem hx (torIncl_mem_tanG O (prB_tanG O hx)))
      (g2Incl_mem_tanG O hw)
  have halg : AlgPair (x.1, x.2.2.2 - M.mulVec s.2) :=
    ⟨hxa.1, LSG.W88.V5d.algVec_sub hxa.2.2.2 (LSG.AuxV.algVec_mulVec hM hsa.2)⟩
  have e' : x = vecIncl (x.1, x.2.2.2 - M.mulVec s.2) + torIncl x.2.1 +
      g2Incl (x.2.2.1, M.mulVec s.2) := by ext <;> simp
  rw [e']
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left
      ⟨_, Submodule.subset_span ⟨hvec, halg⟩, rfl⟩)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, prB_tanG O hx, rfl⟩)
  · exact Submodule.mem_sup_right ⟨(x.2.2.1, M.mulVec s.2), ⟨(x.2.2.1, s.2), hw, rfl⟩, rfl⟩

theorem dataRat_tan_eq_of (h : gamRat O = gamFull O) : (dataRat O).tan = tanG O := by
  refine le_antisymm (dataRat_tan_le O) fun x hx => ?_
  obtain ⟨w, hw, hg, e⟩ := decomp_tanG O hx
  rw [e]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, by
      change _ ∈ gamRat O; rw [h]; exact hg, rfl⟩)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, prB_tanG O hx, rfl⟩)
  · exact Submodule.mem_sup_right ⟨(x.2.2.1, M.mulVec w), ⟨(x.2.2.1, w), hw, rfl⟩, rfl⟩

/-- The member `(U, t, ℂ^{d₀} × ℂ^r)`. -/
def dataTop : SubgroupDataV (d0 := d0) (d1 := d1) Ls M :=
  { U := O.S.U, t := O.S.t, gam := ⊤, gam_rat := LSG.W88.V5d.ratPair_top, t_ab := O.S.t_ab }

theorem tanG_le_dataTop : tanG O ≤ (dataTop O).tan := by
  intro x hx
  obtain ⟨w, hw, hg, e⟩ := decomp_tanG O hx
  rw [e]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, Submodule.mem_top, rfl⟩)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, prB_tanG O hx, rfl⟩)
  · exact Submodule.mem_sup_right ⟨(x.2.2.1, M.mulVec w), ⟨(x.2.2.1, w), hw, rfl⟩, rfl⟩

lemma vecIncl_mem_fibreV (hd0 : d0 = 0) (γ : (Fin d0 → ℂ) × (Fin r → ℂ)) :
    (vecIncl γ : TanV d0 d1 m r) ∈ fibreV := by
  subst hd0
  refine ⟨γ.2, ?_⟩
  simp only [LinearMap.comp_apply, LinearMap.inr_apply]
  congr 1
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem dataTop_le (hd0 : d0 = 0) : (dataTop O).tan ≤ tanG O ⊔ fibreV := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨γ, -, rfl⟩
    exact Submodule.mem_sup_right (vecIncl_mem_fibreV hd0 γ)
  · rintro _ ⟨b, hb, rfl⟩; exact Submodule.mem_sup_left (torIncl_mem_tanG O hb)
  · exact (perTan_le_tanG O).trans le_sup_left

/-- `dim T_E ≤ dim T′ + 1` when `Γ_full ≠ 0`, `d₀ = 0`, `r ≤ 2`. -/
theorem finrank_dataTop_le (hd0 : d0 = 0) (hr : r ≤ 2) (hΓ : gamFull O ≠ ⊥) :
    finrank ℂ (dataTop O).tan ≤ finrank ℂ (tanG O) + 1 := by
  have h1 := Submodule.finrank_mono (dataTop_le O hd0)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (tanG O) (fibreV : Submodule ℂ (TanV d0 d1 m r))
  have h3 : finrank ℂ (fibreV : Submodule ℂ (TanV d0 d1 m r)) ≤ 2 := by
    refine (LinearMap.finrank_range_le _).trans ?_
    simp; omega
  have h4 : 1 ≤ finrank ℂ ↥(tanG O ⊓ fibreV) := by
    obtain ⟨γ, hγ, hγ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hΓ
    have hmem : (vecIncl γ : TanV d0 d1 m r) ∈ tanG O ⊓ fibreV := ⟨hγ, vecIncl_mem_fibreV hd0 γ⟩
    have hne : (vecIncl γ : TanV d0 d1 m r) ≠ 0 := by
      intro h0
      apply hγ0
      have e1 := congrArg Prod.fst h0
      have e2 := congrArg (fun p : TanV d0 d1 m r => p.2.2.2) h0
      exact Prod.ext e1 e2
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    rw [h0] at hmem
    exact hne ((Submodule.mem_bot ℂ).mp hmem)
  omega

lemma rk_mono_of_le {E : Type*} [AddCommGroup E] [Module ℚ E] {Y A B : AddSubgroup E} (hY : Y.FG)
    (hAB : A ≤ B) (hB : B ≤ Y) : rk A ≤ rk B := by
  have : FiniteDimensional ℚ (Submodule.span ℚ (Y : Set E)) := K11.finiteDimensional_span_of_fg hY
  have : FiniteDimensional ℚ (Submodule.span ℚ (B : Set E)) :=
    Submodule.finiteDimensional_of_le (Submodule.span_mono hB)
  exact Submodule.finrank_mono (Submodule.span_mono hAB)

set_option maxHeartbeats 1000000 in -- many `finrank` atoms
/-- **The rationality repair for `d₀ = 0`, `r ≤ 2`.** -/
theorem exists_subgroupDataV_rat2 (hd0 : d0 = 0) (hr : r ≤ 2) (hLA : LiftAlg Ls)
    (hPT : PerTanRat Ls) (hM : AlgMat M) (W : Submodule ℂ (TanV d0 d1 m r)) (hW : RatSubV W)
    (Y : AddSubgroup (TanV d0 d1 m r)) (hYfg : Y.FG) (hY : ∀ y ∈ Y, y ∈ LamV Ls M) {q e : ℕ}
    (he2 : 2 * q ≤ e)
    (hδu : finrank ℚ O.S.U ≤ d0 + d1 + m + r - finrank ℂ (tanG O))
    (hT : ((rk Y - rk (Y ⊓ ((tanG O).toAddSubgroup ⊔ PerV Ls M)) + finrank ℚ O.S.U +
        2 * (d0 + d1 + m + r - finrank ℂ (tanG O) - finrank ℚ O.S.U) : ℕ) : ℤ) * q ≤
      e * (((d0 + d1 + m + r - finrank ℂ (tanG O) : ℕ) : ℤ) -
        ((finrank ℂ W - finrank ℂ ↥(W ⊓ tanG O) : ℕ) : ℤ)))
    (hpos : 1 ≤ ((d0 + d1 + m + r - finrank ℂ (tanG O) : ℕ) : ℤ) -
      ((finrank ℂ W - finrank ℂ ↥(W ⊓ tanG O) : ℕ) : ℤ)) :
    ∃ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.Proper ∧
      finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) < H.δ ∧
      ((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerV Ls M)) + H.δ1 + 2 * H.δ2 : ℕ) : ℤ) * q ≤
        e * ((H.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ) : ℤ)) := by
  classical
  set D := d0 + d1 + m + r with hD
  set u := finrank ℚ O.S.U with hu
  set T := tanG O with hTdef
  have hfTan : finrank ℂ (TanV d0 d1 m r) = D := by simp [hD, add_assoc]
  have htD : finrank ℂ T ≤ D := (Submodule.finrank_le T).trans hfTan.le
  have hwd : finrank ℂ ↥(W ⊓ T) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
  have hrkT : rk (Y ⊓ (T.toAddSubgroup ⊔ PerV Ls M)) ≤ rk Y :=
    rk_mono_of_le hYfg inf_le_left le_rfl
  have hδ0 : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.δ0 = 0 := fun H => by
    simp only [SubgroupDataV.δ0]; omega
  have he0 : (0 : ℤ) ≤ e := Int.natCast_nonneg e
  have hq0 : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have he2' : (2 : ℤ) * q ≤ e := by exact_mod_cast he2
  by_cases hS : finrank ℂ ↥(W ⊓ T) ≤ finrank ℂ ↥(W ⊓ (dataRat O).tan)
  · -- `T_S` works
    refine ⟨dataRat O, ?_⟩
    have hlam : Y ⊓ ((dataRat O).tan.toAddSubgroup ⊔ PerV Ls M) =
        Y ⊓ (T.toAddSubgroup ⊔ PerV Ls M) := inf_tanPerV_eq O hLA hM Y hY
    have hts : finrank ℂ (dataRat O).tan ≤ finrank ℂ T := Submodule.finrank_mono (dataRat_tan_le O)
    have hwS : finrank ℂ ↥(W ⊓ (dataRat O).tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
    have hδS : (dataRat O).δ = D - finrank ℂ (dataRat O).tan := rfl
    have hδ1S : (dataRat O).δ1 = u := rfl
    have hδ2S : (dataRat O).δ2 = D - finrank ℂ (dataRat O).tan - u := by
      simp only [SubgroupDataV.δ2, hδ0, hδ1S, hδS]; omega
    rw [hlam, hδ1S, hδ2S, hδS]
    set j : ℕ := finrank ℂ T - finrank ℂ (dataRat O).tan with hj
    have c1 : ((rk Y - rk (Y ⊓ (T.toAddSubgroup ⊔ PerV Ls M)) + u +
        2 * (D - finrank ℂ (dataRat O).tan - u) : ℕ) : ℤ) =
        ((rk Y - rk (Y ⊓ (T.toAddSubgroup ⊔ PerV Ls M)) + u +
        2 * (D - finrank ℂ T - u) : ℕ) : ℤ) + 2 * j := by
      simp only [hj]; push_cast; omega
    have c2 : ((D - finrank ℂ (dataRat O).tan : ℕ) : ℤ) -
        ((finrank ℂ W - finrank ℂ ↥(W ⊓ (dataRat O).tan) : ℕ) : ℤ) =
        (((D - finrank ℂ T : ℕ) : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ T) : ℕ) : ℤ)) + j +
          (finrank ℂ ↥(W ⊓ (dataRat O).tan) - finrank ℂ ↥(W ⊓ T) : ℤ) := by
      simp only [hj]; push_cast; omega
    have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have hS' : (0 : ℤ) ≤ (finrank ℂ ↥(W ⊓ (dataRat O).tan) - finrank ℂ ↥(W ⊓ T) : ℤ) := by
      have : (finrank ℂ ↥(W ⊓ T) : ℤ) ≤ finrank ℂ ↥(W ⊓ (dataRat O).tan) := by exact_mod_cast hS
      linarith
    have k1 : (2 * j : ℤ) * q ≤ e * j := by
      have := mul_le_mul_of_nonneg_right he2' hj0
      linarith
    have k2 : (0 : ℤ) ≤ e * (finrank ℂ ↥(W ⊓ (dataRat O).tan) - finrank ℂ ↥(W ⊓ T) : ℤ) :=
      mul_nonneg he0 hS'
    have hpos' : (1 : ℤ) ≤ ((D - finrank ℂ (dataRat O).tan : ℕ) : ℤ) -
        ((finrank ℂ W - finrank ℂ ↥(W ⊓ (dataRat O).tan) : ℕ) : ℤ) := by
      rw [c2]; linarith
    refine ⟨?_, ?_, ?_⟩
    · change D - finrank ℂ (dataRat O).tan ≠ 0
      omega
    · change _ < D - finrank ℂ (dataRat O).tan
      omega
    · rw [c1, c2, add_mul, mul_add, mul_add]
      linarith
  · -- `T_E` works
    push Not at hS
    have hne : gamRat O ≠ gamFull O := by
      intro h
      rw [dataRat_tan_eq_of O h] at hS
      exact lt_irrefl _ hS
    have hΓ : gamFull O ≠ ⊥ := by
      intro h
      apply hne
      exact le_antisymm (gamRat_le O) (h ▸ bot_le)
    refine ⟨dataTop O, ?_⟩
    have hTE := tanG_le_dataTop O
    have htE : finrank ℂ (dataTop O).tan ≤ finrank ℂ T + 1 := finrank_dataTop_le O hd0 hr hΓ
    have htE' : finrank ℂ T ≤ finrank ℂ (dataTop O).tan := Submodule.finrank_mono hTE
    have hwE : finrank ℂ ↥(W ⊓ T) ≤ finrank ℂ ↥(W ⊓ (dataTop O).tan) :=
      Submodule.finrank_mono (inf_le_inf_left _ hTE)
    have hadd := finrank_inf_add_le W (dataTop O).tan T hTE
    have hwEd : finrank ℂ ↥(W ⊓ (dataTop O).tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
    -- the key: `dim (W ∩ T_E) = dim (W ∩ T′) + dim T_E/T′`
    have hkey : finrank ℂ ↥(W ⊓ (dataTop O).tan) + finrank ℂ T =
        finrank ℂ ↥(W ⊓ T) + finrank ℂ (dataTop O).tan := by
      by_contra hcon
      have hj1 : finrank ℂ (dataTop O).tan = finrank ℂ T + 1 := by omega
      have hwEq : finrank ℂ ↥(W ⊓ (dataTop O).tan) = finrank ℂ ↥(W ⊓ T) := by omega
      have heq : W ⊓ T = W ⊓ (dataTop O).tan :=
        Submodule.eq_of_le_of_finrank_eq (inf_le_inf_left _ hTE) hwEq.symm
      have hrat : RatSubV (W ⊓ (dataTop O).tan) :=
        ((LSG.W88.V5d.exists_frame2 hM hPT (dataTop O)).some).ratV_inf_tan hM hW
      have hle : W ⊓ T ≤ W ⊓ (dataRat O).tan := by
        rw [heq, hrat, Submodule.span_le]
        rintro w ⟨hw, hwa⟩
        rw [← heq] at hw
        exact ⟨hw.1, alg_mem_dataRat O hPT hM hw.2 hwa⟩
      have := Submodule.finrank_mono hle
      omega
    have hlam : rk (Y ⊓ (T.toAddSubgroup ⊔ PerV Ls M)) ≤
        rk (Y ⊓ ((dataTop O).tan.toAddSubgroup ⊔ PerV Ls M)) :=
      rk_mono_of_le hYfg (inf_le_inf_left _ (sup_le_sup_right (fun x hx => hTE hx) _)) inf_le_left
    have hδE : (dataTop O).δ = D - finrank ℂ (dataTop O).tan := rfl
    have hδ1E : (dataTop O).δ1 = u := rfl
    have hδ2E : (dataTop O).δ2 = D - finrank ℂ (dataTop O).tan - u := by
      simp only [SubgroupDataV.δ2, hδ0, hδ1E, hδE]; omega
    rw [hδ1E, hδ2E, hδE]
    have c2 : ((D - finrank ℂ (dataTop O).tan : ℕ) : ℤ) -
        ((finrank ℂ W - finrank ℂ ↥(W ⊓ (dataTop O).tan) : ℕ) : ℤ) =
        ((D - finrank ℂ T : ℕ) : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ T) : ℕ) : ℤ) := by
      push_cast; omega
    have c1 : ((rk Y - rk (Y ⊓ ((dataTop O).tan.toAddSubgroup ⊔ PerV Ls M)) + u +
        2 * (D - finrank ℂ (dataTop O).tan - u) : ℕ) : ℤ) ≤
        ((rk Y - rk (Y ⊓ (T.toAddSubgroup ⊔ PerV Ls M)) + u +
        2 * (D - finrank ℂ T - u) : ℕ) : ℤ) := by
      have : rk Y - rk (Y ⊓ ((dataTop O).tan.toAddSubgroup ⊔ PerV Ls M)) + u +
          2 * (D - finrank ℂ (dataTop O).tan - u) ≤
          rk Y - rk (Y ⊓ (T.toAddSubgroup ⊔ PerV Ls M)) + u + 2 * (D - finrank ℂ T - u) := by
        omega
      exact_mod_cast this
    refine ⟨?_, ?_, ?_⟩
    · change D - finrank ℂ (dataTop O).tan ≠ 0
      omega
    · change _ < D - finrank ℂ (dataTop O).tan
      omega
    · rw [c2]
      exact (mul_le_mul_of_nonneg_right c1 hq0).trans hT

end Rat2

end LSG.W88
