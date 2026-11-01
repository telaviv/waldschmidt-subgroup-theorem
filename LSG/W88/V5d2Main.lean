/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dOntoSwap
import LSG.W88.V5d2Frame

/-!
# W88 §5d for the class with `d₀ = 0`, `r ≤ 2`, from `Theorem41Vec2`

`hyperplaneKappaVec2_of : Theorem41Vec2 → HyperplaneKappaVec2`. The proof is `coreV_onto`
(`V5dOntoMain.lean`) with these changes:
* frames for every `r` (`exists_frame2`), `topV_tan2`;
* `dim (V ∩ fibre) ≤ 1` (`finrank_inf_fibreV_le_one`, the fibre is a member) instead of
  `V ∩ fibre = 0`; it passes to the frame group (`Frame.finrank_comap_inf_fibreV`);
* Theorem 4.1 for the frame group `G_{H'}` (`d₀ = 0` since `d₀ = 0` for `G`, `f ≤ r ≤ 2`,
  `PerTanRat` by `perTanRat_comp`): `Theorem41Vec2` under (NR); otherwise `f = 0` and Roy or
  `corner_falseV'` as before. No swap presentation is needed.

`hyperplaneKappa_of_iso2`: `hyperplaneKappa_of_iso` (`V5dIso.lean`) at `d₀ = 0`, `r ≤ 2`.
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

variable {d0 d1 m r : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

set_option maxHeartbeats 1000000 in -- the maximiser argument elaborates many large `finrank` terms
/-- **The core of the §5d deduction** for the class with `d₀ = 0`, `r ≤ 2`, from `Theorem41Vec2`
(`coreV_onto` with frames for every `r` and `dim (V ∩ fibre) ≤ 1`). -/
theorem coreV2 (h41 : Theorem41Vec2)
    (hLs : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃)
    (hM : AlgMat M) (hd0 : d0 = 0) (hr : r ≤ 2) (hLA : LiftAlg Ls) (hPT : PerTanRat Ls)
    (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r)) (hYfg : Y.FG)
    (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M) (hV : finrank ℂ V + 1 = d0 + d1 + m + r) (hWV : W ≤ V)
    (hWrat : RatSubV W)
    (hno : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan ≤ V → H.tan = ⊥)
    (hineq : ((finrank ℚ (Submodule.span ℚ (Y : Set (TanV d0 d1 m r))) : ℤ) >
      ((d1 : ℤ) + 2 * (m + r) - finrank ℚ ↥(Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) ⊓
        OmV d0 d1 Ls M)) * (((d0 + d1 + m + r : ℕ) : ℤ) - 1 - finrank ℂ W))) : False := by
  classical
  have fr : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, Frame H :=
    fun H => (exists_frame2 hM hPT H).some
  have hVfib2 := finrank_inf_fibreV_le_one hr V hno
  set Yq := Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  set Ω := OmV d0 d1 Ls M with hΩ
  set κ := finrank ℚ ↥(Yq ⊓ Ω) with hκ
  have hΩd : finrank ℚ Ω ≤ d1 + 2 * m := finrank_OmV_le
  have hκle : κ ≤ d1 + 2 * m := (Submodule.finrank_mono inf_le_right).trans hΩd
  have hfTan : finrank ℂ (TanV d0 d1 m r) = d0 + d1 + m + r := by simp [add_assoc]
  let aF : SubgroupDataV (d0 := d0) (d1 := d1) Ls M → ℤ := fun H =>
    (finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPV H
  let eF : SubgroupDataV (d0 := d0) (d1 := d1) Ls M → ℤ := fun H =>
    (finrank ℂ H.tan : ℤ) - finrank ℂ ↥(W ⊓ H.tan)
  have he : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan ≠ ⊥ → 0 < eF H := by
    intro H hH
    have hle : W ⊓ H.tan ≤ H.tan := inf_le_right
    have h1 := Submodule.finrank_mono hle
    have h2 : finrank ℂ ↥(W ⊓ H.tan) ≠ finrank ℂ H.tan := by
      intro heq
      have := Submodule.eq_of_le_of_finrank_eq hle heq
      exact hH (hno H (this ▸ inf_le_left |>.trans hWV))
    simp only [eF]; omega
  have hzero : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan = ⊥ → aF H = 0 ∧ eF H = 0 := by
    intro H hH
    have hf := (fr H).finrank_tan
    have hn := (fr H).nPV_eq
    rw [hH, finrank_bot] at hf
    have hTq : H.tan.restrictScalars ℚ = ⊥ := by rw [hH]; rfl
    refine ⟨?_, ?_⟩
    · change (finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPV H = 0
      rw [hTq, bot_sup_eq, hn]; omega
    · change (finrank ℂ H.tan : ℤ) - finrank ℂ ↥(W ⊓ H.tan) = 0
      rw [hH, inf_bot_eq]; simp
  -- the value at `G`
  set G := topV (d0 := d0) (d1 := d1) Ls M with hG
  have hGtan : G.tan = ⊤ := topV_tan2 hM hPT
  have hGC : G.tan ≠ ⊥ := by
    rw [hGtan]; intro h
    have := congrArg (fun S : Submodule ℂ (TanV d0 d1 m r) => finrank ℂ S) h
    simp only [finrank_top, finrank_bot, hfTan] at this
    omega
  have hnPG : nPV G = d1 + 2 * (m + r) := by
    rw [nPV, hGtan, finrank_top, hfTan]
    have h1 : finrank ℂ (G.gam.map (LinearMap.fst ℂ (Fin d0 → ℂ) (Fin r → ℂ))) = d0 :=
      finrank_map_fst_top
    have h2 : finrank ℂ (torusLie G.U) = d1 := by
      change finrank ℂ (torusLie (⊥ : Submodule ℚ (Fin d1 → ℚ))) = d1
      rw [K5d.torusLie_bot, finrank_top, Module.finrank_fin_fun]
    rw [h1, h2]; push_cast; ring
  have haG : aF G = (finrank ℚ Yq : ℤ) - κ + (d1 + 2 * (m + r)) := by
    have : G.tan.restrictScalars ℚ = ⊤ := by rw [hGtan]; rfl
    change (finrank ℚ ↥(Yq ⊓ (G.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPV G = _
    rw [this, top_sup_eq, inf_top_eq, hnPG]
  have heG : eF G = ((d0 + d1 + m + r : ℕ) : ℤ) - finrank ℂ W := by
    change (finrank ℂ G.tan : ℤ) - finrank ℂ ↥(W ⊓ G.tan) = _
    rw [hGtan, inf_top_eq, finrank_top, hfTan]
  set D : ℤ := (d1 : ℤ) + 2 * (m + r) - κ with hD
  have hD0 : 0 ≤ D := by omega
  have hGineq : D * eF G < aF G := by
    rw [haG, heG]
    have : D * (((d0 + d1 + m + r : ℕ) : ℤ) - finrank ℂ W) =
        D * (((d0 + d1 + m + r : ℕ) : ℤ) - 1 - finrank ℂ W) + D := by ring
    rw [this]; simp only [hD] at hineq ⊢; linarith
  -- Lemma 5.1: a maximiser
  set S : Set (ℤ × ℤ) := (fun H => (aF H, eF H)) ''
    {H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M | H.tan ≠ ⊥} with hS
  have hSfin : S.Finite := by
    refine ((Set.finite_Icc (-(κ : ℤ)) (finrank ℚ Yq + d1 + 2 * (m + r))).prod
      (Set.finite_Icc (-((d0 + d1 + m + r : ℕ) : ℤ)) ((d0 + d1 + m + r : ℕ) : ℤ))).subset ?_
    rintro _ ⟨H, -, rfl⟩
    have h1 : finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) ≤ finrank ℚ Yq :=
      Submodule.finrank_mono inf_le_left
    have h2 := (fr H).nPV_bounds
    have h4 : finrank ℂ H.tan ≤ d0 + d1 + m + r := (Submodule.finrank_le _).trans hfTan.le
    have h5 : finrank ℂ ↥(W ⊓ H.tan) ≤ d0 + d1 + m + r := (Submodule.finrank_le _).trans hfTan.le
    simp only [Set.mem_prod, Set.mem_Icc, aF, eF]
    push_cast
    omega
  obtain ⟨_, ⟨H', hC', rfl⟩, hmax⟩ := Set.exists_max_image S (fun q : ℤ × ℤ =>
    (q.1 : ℚ) / q.2) hSfin ⟨_, ⟨G, hGC, rfl⟩⟩
  have hC : H'.tan ≠ ⊥ := hC'
  have he' : 0 < eF H' := he H' hC
  have hmaxAll : ∀ H, aF H * eF H' ≤ aF H' * eF H := by
    intro H
    by_cases hH : H.tan = ⊥
    · obtain ⟨h1, h2⟩ := hzero H hH; rw [h1, h2]; simp
    · have := hmax _ ⟨H, hH, rfl⟩
      simp only at this
      rw [div_le_div_iff₀ (by exact_mod_cast he H hH) (by exact_mod_cast he')] at this
      exact_mod_cast this
  have ha' : D * eF H' < aF H' := by
    have h1 := hmaxAll G
    have heG' := he G hGC
    by_contra hcon
    push Not at hcon
    nlinarith [mul_lt_mul_of_pos_right hGineq he', mul_le_mul_of_nonneg_right hcon heG'.le]
  -- the maximiser
  set F := fr H' with hF
  have hfg : fg H' = finrank ℂ H'.t := rfl
  have hT'V : ¬ H'.tan ≤ V := fun hle => hC (hno H' hle)
  set V' := V ⊓ H'.tan with hV'
  have hVdim : finrank ℂ V' + 1 = finrank ℂ H'.tan := by
    have hlt : V < V ⊔ H'.tan := lt_of_le_of_ne le_sup_left fun heq => hT'V (heq ▸ le_sup_right)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank ℂ ↥(V ⊔ H'.tan) ≤ d0 + d1 + m + r := (Submodule.finrank_le _).trans hfTan.le
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq V H'.tan
    rw [← hV'] at h3
    omega
  set Y' := Y ⊓ H'.tan.toAddSubgroup with hY'
  have hY'fg : Y'.FG := K5d.fg_of_le_addSubgroup' hYfg inf_le_left
  have hY'mem : ∀ y ∈ Y', y ∈ V' ∧ y ∈ LamV Ls M := fun y hy =>
    ⟨⟨(hY y hy.1).1, hy.2⟩, (hY y hy.1).2⟩
  have hspan' : Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) = Yq ⊓ H'.tan.restrictScalars ℚ := by
    rw [hY', K11.span_inf_addSubgroup, K11.span_submodule_coe]
  set W' := W ⊓ H'.tan with hW'
  have hW'rat : RatSubV W' := F.ratV_inf_tan hM hWrat
  have hW'V : W' ≤ V' := inf_le_inf_right _ hWV
  set κ' := finrank ℚ ↥(Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) ⊓ Ω) with hκ'
  set m' := finrank ℚ ↥(Submodule.span ℚ (Y' : Set (TanV d0 d1 m r))) with hm'
  have hΩT : finrank ℂ (torusLie H'.U) + 2 * finrank ℂ H'.t ≤
      finrank ℚ ↥(Ω ⊓ H'.tan.restrictScalars ℚ) := finrank_OmV_inf_ge (Ls := Ls) (M := M) H'
  have htl' := Frame.finrank_torusLie' (H := H')
  have hnP' := F.nPV_eq
  have hf' := Frame.ff_le (H := H')
  -- Lemma 5.2
  have hL52 : (finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) + nPV H' ≤
      m' + (d1 + 2 * (m + r)) := by
    have := K11.finrank_le_of_le_sup (Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω))
      (H'.tan.restrictScalars ℚ) Ω
      inf_le_right
    have e : Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω) ⊓ H'.tan.restrictScalars ℚ =
        Yq ⊓ H'.tan.restrictScalars ℚ := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_left : H'.tan.restrictScalars ℚ ≤ _ ⊔ Ω)]
    rw [e, ← hspan', ← hm'] at this
    rw [hnP']; omega
  have hLk : (κ : ℤ) + nPV H' ≤ κ' + (d1 + 2 * (m + r)) := by
    have := K11.finrank_le_of_le_sup (Yq ⊓ Ω) (H'.tan.restrictScalars ℚ) Ω
      (inf_le_right.trans le_sup_right)
    have e : Yq ⊓ Ω ⊓ H'.tan.restrictScalars ℚ =
        Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) ⊓ Ω := by
      rw [hspan', inf_right_comm]
    rw [e, ← hκ'] at this
    rw [hnP']; omega
  have he'v : eF H' = (finrank ℂ H'.tan : ℤ) - finrank ℂ ↥(W ⊓ H'.tan) := rfl
  have ha'v : aF H' = (finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPV H' := rfl
  obtain ⟨p1, p2, p3, p5, p6, p7, p8⟩ := trans_premises2 hM hLA F V' W' Y' inf_le_right hVdim
    hW'V hW'rat hY'fg hY'mem
  have p4 : finrank ℂ ↥(V'.comap F.Psi ⊓ fibreV) ≤ 1 :=
    (F.finrank_comap_inf_fibreV V').trans
      ((Submodule.finrank_mono (inf_le_inf_right _ inf_le_left)).trans hVfib2)
  have hk0 : fk0 H' = 0 := by
    have : fk0 H' ≤ d0 := by
      simpa using Submodule.finrank_le (H'.gam.map (LinearMap.fst ℂ (Fin d0 → ℂ) (Fin r → ℂ)))
    omega
  have hfT' := F.finrank_tan
  have hΩup : finrank ℚ ↥(Ω ⊓ H'.tan.restrictScalars ℚ) ≤ fk1 H' + 2 * fg H' :=
    F.finrank_OmV_inf_le
  have hle' : Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) ⊓ Ω ≤
      Ω ⊓ H'.tan.restrictScalars ℚ := by
    rw [hspan']; exact fun x hx => ⟨hx.2, hx.1.2⟩
  have hκ'le : κ' ≤ finrank ℚ ↥(Ω ⊓ H'.tan.restrictScalars ℚ) := by
    rw [hκ']; exact Submodule.finrank_mono hle'
  have hLsH : ∀ k, IsAlgebraic ℚ (F.LsH k).g₂ ∧ IsAlgebraic ℚ (F.LsH k).g₃ := fun k => hLs _
  have hLAH := liftAlg_comp (chart_ι_injective F.c) hLA
  have hPTH := perTanRat_comp (chart_ι_injective F.c) hPT
  -- the corner: `M_H = 0`, `g ≥ 1`, many periods in `V`
  have hcorner : (∀ y, F.MH.mulVec y = 0) → 1 ≤ fg H' → fk1 H' + 2 * fg H' ≤ κ' + 1 → False := by
    intro hMH hg1 hκc
    refine corner_falseV' F hMH hg1 V hno (Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) ⊓ Ω)
      ?_ ?_ ?_
    · rw [hspan']; exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · exact inf_le_left.trans (Submodule.span_le.mpr fun y hy => (hY'mem y hy).1.1)
    · change _ ≤ κ' + 1
      omega
  -- Theorem 4.1 for `G_{H'}`
  have hC41 : Concl41 F.LsH F.MH (V'.comap F.Psi) (W'.comap F.Psi)
      (Y'.map F.Phi.toAddMonoidHom) := by
    by_cases hNR : fk1 H' + 2 * fk0 H' + κ' ≤ 2 * finrank ℂ V'
    · -- (NR): `Theorem41Vec2`
      exact h41 (fk0 H') (fk1 H') (fg H') (ff H') F.LsH F.MH hLsH (F.algMat_MH hM) hk0
        (hf'.trans hr) hLAH hPTH _ _ _ p1 p2 p3 p4 p5 p6 (by rw [p7, p8]; exact hNR)
    · -- (NR) fails: then `f = 0`; linear (Roy) or the corner
      have hf0 : ff H' = 0 := by omega
      by_cases hg0 : fg H' = 0
      · exact concl41_lin hg0 hf0 F.LsH F.MH _ _ _ p1 p2 p3 p5 p6
      · exact (hcorner (fun _ => funext fun i => absurd i.2 (by omega)) (by omega)
          (by omega)).elim
  -- the comparison (Lemma 5.1 / 5.2), unchanged
  obtain ⟨H'', hT''T, hτ, hin⟩ := trans41V F V' W' Y' inf_le_right hVdim hW'V hY'fg hY'mem hC41
  have hlam : finrank ℚ ↥(Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) ⊓
      (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ ≤
      finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ' := by
    have hle : Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ≤
        Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) :=
      inf_le_inf_right _ (Submodule.span_mono inf_le_left)
    have : FiniteDimensional ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have := K11.finrank_le_of_le _ _ Ω hle
    have e1 : Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ⊓ Ω = Yq ⊓ Ω := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ H''.tan.restrictScalars ℚ ⊔ Ω)]
    have e2 : Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ⊓ Ω =
        Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) ⊓ Ω := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ H''.tan.restrictScalars ℚ ⊔ Ω)]
    rw [e1, e2] at this
    omega
  have hmx := hmaxAll H''
  have he''v : eF H'' = (finrank ℂ H''.tan : ℤ) - finrank ℂ ↥(W ⊓ H''.tan) := rfl
  have ha''v : aF H'' = (finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ +
      nPV H'' := rfl
  have hWr'' : W' ⊓ H''.tan = W ⊓ H''.tan := by
    rw [hW', inf_assoc, inf_eq_right.mpr hT''T]
  rw [hWr''] at hτ hin
  set s : ℤ := ((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
    ((finrank ℂ W' : ℤ) - finrank ℂ ↥(W ⊓ H''.tan)) with hs
  have hs1 : 1 ≤ s := by simp only [hs]; omega
  have hes : eF H'' ≤ eF H' - s := by rw [he''v, he'v, hs]; linarith
  set D' : ℤ := nPV H' - κ' with hD'
  have hDD : D' ≤ D := by simp only [hD, hD']; omega
  have hX : aF H' - aF H'' ≤ s * D' + (D - D') := by
    rw [ha'v, ha''v]
    have h2 : (finrank ℚ ↥(Submodule.span ℚ (Y' : Set (TanV d0 d1 m r)) ⊓
        (H''.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) + κ ≤
        finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ' := by exact_mod_cast hlam
    simp only [hD, hD']
    linarith [hin, hL52, h2]
  exact K5d.arith_final' hmx hes hX he' ha' hD0 hs1 hDD

/-- **W88 §5d for the class with `d₀ = 0`, `r ≤ 2`, from `Theorem41Vec2`.** -/
theorem hyperplaneKappaVec2_of (h41 : Theorem41Vec2) : HyperplaneKappaVec2 := by
  intro d0 d1 m r Ls M hLs hM hd0 hr hLA hPT V W Y hV hWV hWrat hYfg hY hineq
  by_contra hcon
  have hno : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan ≤ V → H.tan = ⊥ :=
    fun H hle => by_contra fun hne => hcon ⟨H, hne, hle⟩
  refine coreV2 h41 hLs hM hd0 hr hLA hPT V W Y hYfg hY (by simpa [add_assoc] using hV) hWV hWrat
    hno ?_
  have e : rk (Y ⊓ PerV Ls M) = finrank ℚ ↥(Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) ⊓
      OmV d0 d1 Ls M) := by
    rw [rk, K11.span_inf_addSubgroup]
  rw [rk, e] at hineq
  push_cast
  exact hineq

end LSG.W88.V5d
