/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.K5dTrans
import LSG.W88.K5dRat
import LSG.CM.Transport
import LSG.Subgroups.Torus

/-!
# W88 §5d for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`: `lean_mstar`'s `HypStd`, unconditionally

`hyperplaneKappaStd`: `MStarCopy.HyperplaneKappa (gmStd d₀ d₁ Ls)` for all `d₀, d₁, m` and curves `Ls`
with algebraic invariants; `hypStd : MStarCopy.HypStd`, `hypStdCM`, `hypStdCMAt_zero`.

## The model (for review)

`gmStd d₀ d₁ Ls` (verbatim copy of `lean_mstar`'s, `MStarCopyStd.lean`) is `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`
in the coordinates `Tan d₀ d₁ m`: `d₁ = d₁`, `d₂ = m` (the `G_a` factor does not enter (5.4)),
algebraic vectors `algStd`, logarithms `Lam Ls`, periods `span_ℚ Per Ls`, and as subgroup family
all `SubgroupData` (`H₀ × T_U × B`, `H₀` `ℚ̄`-rational, `B` given by an abelian tangent space).

## The proof (W88 §5: Lemma 5.1, Lemma 5.2, §5d)

Assume `V` (a hyperplane) contains no nonzero `H.tan`. For a subgroup `H` put
`a(H) = rk(Γ ∩ H) + d₁' + 2d₂'` and `e(H) = dim H − dim W_H`, where `W_H` is the `ℚ̄`-rational part of
`W ∩ T_H` (`aF`, `eF`, `Wr`). Every `H ≠ 0` has `e(H) > 0`; (5.4) says `a(G) > D e(G)`, `D = d₁ + 2m − κ`.
Take `H'` maximising `a/e` (Lemma 5.1). Then `T_{H'} ⊄ V`, `V' = V ∩ T_{H'}` is a hyperplane of
`T_{H'}`, and Theorem 4.1 for `H'` (`trans41`) gives `H'' ⊂ H'` whose inequality, together with
Lemma 5.2 and the maximality of `H'`, yields `(s − 1)(D − D') < 0` with `s ≥ 1`, `D ≥ D'`.
Theorem 4.1 for `H'` comes from:
* `LSG.CM.thm41SubAt_of LSG.W88.theorem41Abelian` (Theorem 4.1 for `G_a^{k₀} × G_m^{k₁} × B`) when
  the (NR) inequality holds for `H'`;
* Roy's Theorem 1 (`StrongSix.M2.waldschmidtTheorem1`, no (NR)) when `B = 0` (`sub41Concl_bot`);
* when `B ≠ 0` and (NR) fails, i.e. `κ' ≥ d₁' + 2d₂' − 1`, the periods in `V` force `0 × 0 × B ⊂ V`
  (`corner_false`), contradicting the assumption.
-/

open Complex Module

namespace LSG.W88.K5d

variable {d0 d1 m : ℕ}

/-- The final inequality chase of §5d. -/
lemma arith_final' {a a'' e e'' s D D' : ℤ} (hmx : a'' * e ≤ a * e'') (hes : e'' ≤ e - s)
    (hX : a - a'' ≤ s * D' + (D - D')) (he : 0 < e) (ha : D * e < a) (hD : 0 ≤ D) (hs1 : 1 ≤ s)
    (hDD : D' ≤ D) : False := by
  have ha0 : 0 ≤ a := le_trans (mul_nonneg hD he.le) ha.le
  have hmx' : a'' * e ≤ a * (e - s) := hmx.trans (mul_le_mul_of_nonneg_left hes ha0)
  have hstep : a * s ≤ (s * D' + (D - D')) * e := by
    nlinarith [mul_le_mul_of_nonneg_right hX he.le]
  have hstep2 : D * e * s < a * s := mul_lt_mul_of_pos_right ha (by linarith)
  have h3 : (s - 1) * (D - D') * e < 0 := by nlinarith
  have h4 : 0 ≤ (s - 1) * (D - D') * e :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) he.le
  linarith

variable (Ls : Fin m → PeriodPair)

/-- The `ℚ̄`-rational part of `W ∩ T_H`. -/
noncomputable def Wr (W : Submodule ℂ (Tan d0 d1 m)) (H : SubgroupData (d0 := d0) (d1 := d1) Ls) :
    Submodule ℂ (Tan d0 d1 m) :=
  Submodule.span ℂ {w | w ∈ W ⊓ H.tan ∧ AlgVec w.1 ∧ AlgVec w.2.1 ∧ AlgVec w.2.2}

lemma Wr_le (W : Submodule ℂ (Tan d0 d1 m)) (H : SubgroupData (d0 := d0) (d1 := d1) Ls) :
    Wr Ls W H ≤ W ⊓ H.tan := Submodule.span_le.mpr fun _ hw => hw.1

lemma Wr_rat (W : Submodule ℂ (Tan d0 d1 m)) (H : SubgroupData (d0 := d0) (d1 := d1) Ls) :
    RationalOverQbarTan (Wr Ls W H) := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    intro w hw
    exact ⟨Submodule.subset_span hw, hw.2⟩
  · exact Submodule.span_le.mpr fun _ hw => hw.1

/-- The whole group as a `SubgroupData`. -/
noncomputable def topSub : SubgroupData (d0 := d0) (d1 := d1) Ls where
  h0 := ⊤
  U := ⊥
  t := ⊤
  h0_rat := by
    apply le_antisymm _ le_top
    intro v _
    have : v = ∑ i, v i • (Pi.single i 1 : Fin d0 → ℂ) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨Submodule.mem_top, fun j => ?_⟩)
    by_cases h : j = i
    · subst h; simpa using isAlgebraic_one
    · simpa [h] using isAlgebraic_zero
  t_ab := by
    unfold IsAbelianTangent
    rw [Submodule.restrictScalars_top]
    have : {z : Fin m → ℂ | z ∈ (⊤ : Submodule ℂ (Fin m → ℂ)) ∧ ∀ j, z j ∈ (Ls j).lattice} =
        (LSG.Subgroups.periodLattice Ls : Set (Fin m → ℂ)) := by
      ext z; simp [LSG.Subgroups.mem_periodLattice]
    rw [this, LSG.Subgroups.span_periodLattice]

lemma torusLie_bot : torusLie (⊥ : Submodule ℚ (Fin d1 → ℚ)) = ⊤ := by
  rw [eq_top_iff]; intro v _ φ hφ
  rw [Submodule.mem_bot] at hφ; subst hφ; simp

lemma topSub_tan : (topSub (d0 := d0) (d1 := d1) Ls).tan = ⊤ := by
  simp only [topSub, SubgroupData.tan, torusLie_bot, Submodule.prod_top]

omit Ls in
lemma fg_of_le_addSubgroup' {E : Type*} [AddCommGroup E] {P Q : AddSubgroup E} (hP : P.FG)
    (h : Q ≤ P) : Q.FG := by
  have : Module.Finite ℤ P := Module.Finite.iff_addGroup_fg.mpr hP
  have : Module.Finite ℤ Q :=
    Module.Finite.of_injective (AddSubgroup.inclusion h).toIntLinearMap
      (AddSubgroup.inclusion_injective h)
  exact Module.Finite.iff_addGroup_fg.mp this

/-- **The core of the §5d deduction** for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`. -/
theorem core (hLs : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃)
    (V W : Submodule ℂ (Tan d0 d1 m)) (Y : AddSubgroup (Tan d0 d1 m)) (hYfg : Y.FG)
    (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ Lam Ls) (hV : finrank ℂ V + 1 = d0 + d1 + m) (hWV : W ≤ V)
    (hWrat : RationalOverQbarTan W)
    (hrat : ∀ t, IsAbelianTangent Ls t → RationalOverQbar t)
    (hno : ∀ H : SubgroupData (d0 := d0) (d1 := d1) Ls, H.tan ≤ V → H.tan = ⊥)
    (hineq : ((finrank ℚ (Submodule.span ℚ (Y : Set (Tan d0 d1 m))) : ℤ) >
      ((d1 : ℤ) + 2 * m - finrank ℚ ↥(Submodule.span ℚ (Y : Set (Tan d0 d1 m)) ⊓ Ωs Ls d0 d1)) *
        (((d0 + d1 + m : ℕ) : ℤ) - 1 - finrank ℂ W))) : False := by
  classical
  have hWrEq : ∀ H : SubgroupData (d0 := d0) (d1 := d1) Ls, Wr Ls W H = W ⊓ H.tan :=
    fun H => (ratT_inf_tan Ls hrat hWrat H).symm
  set Yq := Submodule.span ℚ (Y : Set (Tan d0 d1 m)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  set Ω := Ωs Ls d0 d1 with hΩ
  set κ := finrank ℚ ↥(Yq ⊓ Ω) with hκ
  have hΩd : finrank ℚ Ω ≤ d1 + 2 * m := finrank_Ωs_le Ls
  have hκle : κ ≤ d1 + 2 * m := (Submodule.finrank_mono inf_le_right).trans hΩd
  have hfTan : finrank ℂ (Tan d0 d1 m) = d0 + d1 + m := by simp [add_assoc]
  let aF : SubgroupData (d0 := d0) (d1 := d1) Ls → ℤ := fun H =>
    (finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nP Ls H
  let eF : SubgroupData (d0 := d0) (d1 := d1) Ls → ℤ := fun H =>
    (finrank ℂ H.tan : ℤ) - finrank ℂ (Wr Ls W H)
  have he : ∀ H : SubgroupData (d0 := d0) (d1 := d1) Ls, H.tan ≠ ⊥ → 0 < eF H := by
    intro H hH
    have hle : Wr Ls W H ≤ H.tan := (Wr_le Ls W H).trans inf_le_right
    have h1 := Submodule.finrank_mono hle
    have h2 : finrank ℂ (Wr Ls W H) ≠ finrank ℂ H.tan := by
      intro heq
      have := Submodule.eq_of_le_of_finrank_eq hle heq
      exact hH (hno H (this ▸ (Wr_le Ls W H).trans inf_le_left |>.trans hWV))
    simp only [eF]; omega
  have hzero : ∀ H : SubgroupData (d0 := d0) (d1 := d1) Ls, H.tan = ⊥ → aF H = 0 ∧ eF H = 0 := by
    intro H hH
    have hf := finrank_tan Ls H
    rw [hH, finrank_bot] at hf
    have hTq : H.tan.restrictScalars ℚ = ⊥ := by rw [hH]; rfl
    have hW0 : finrank ℂ (Wr Ls W H) = 0 := by
      have := Submodule.finrank_mono ((Wr_le Ls W H).trans inf_le_right)
      rw [hH, finrank_bot] at this; omega
    refine ⟨?_, ?_⟩
    · change (finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nP Ls H = 0
      rw [hTq, bot_sup_eq]; simp only [nP]; omega
    · change (finrank ℂ H.tan : ℤ) - finrank ℂ (Wr Ls W H) = 0
      rw [hH, finrank_bot, hW0]; simp
  -- the value at `G`
  set G := topSub (d0 := d0) (d1 := d1) Ls with hG
  have hGtan : G.tan = ⊤ := topSub_tan Ls
  have hGC : G.tan ≠ ⊥ := by
    rw [hGtan]; intro h
    have := congrArg (fun S : Submodule ℂ (Tan d0 d1 m) => finrank ℂ S) h
    simp only [finrank_top, finrank_bot, hfTan] at this
    omega
  have hnPG : nP Ls G = d1 + 2 * m := by
    have h := finrank_torusLie (⊥ : Submodule ℚ (Fin d1 → ℚ))
    simp only [finrank_bot, add_zero] at h
    change finrank ℂ (torusLie (⊥ : Submodule ℚ (Fin d1 → ℚ))) +
      2 * finrank ℂ (⊤ : Submodule ℂ (Fin m → ℂ)) = _
    rw [h, finrank_top, finrank_fin_fun]
  have haG : aF G = (finrank ℚ Yq : ℤ) - κ + (d1 + 2 * m) := by
    have : G.tan.restrictScalars ℚ = ⊤ := by rw [hGtan]; rfl
    change (finrank ℚ ↥(Yq ⊓ (G.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nP Ls G = _
    rw [this, top_sup_eq, inf_top_eq, hnPG]
    push_cast; ring
  have hWrG : Wr Ls W G = W := by
    apply le_antisymm ((Wr_le Ls W G).trans inf_le_left)
    conv_lhs => rw [hWrat]
    refine Submodule.span_mono ?_
    intro w hw; exact ⟨⟨hw.1, by rw [hGtan]; exact Submodule.mem_top⟩, hw.2⟩
  have heG : eF G = ((d0 + d1 + m : ℕ) : ℤ) - finrank ℂ W := by
    change (finrank ℂ G.tan : ℤ) - finrank ℂ (Wr Ls W G) = _
    rw [hWrG, hGtan, finrank_top, hfTan]
  set D : ℤ := (d1 : ℤ) + 2 * m - κ with hD
  have hD0 : 0 ≤ D := by omega
  have hGineq : D * eF G < aF G := by
    rw [haG, heG]
    have : D * (((d0 + d1 + m : ℕ) : ℤ) - finrank ℂ W) =
        D * (((d0 + d1 + m : ℕ) : ℤ) - 1 - finrank ℂ W) + D := by ring
    rw [this]; simp only [hD] at hineq ⊢; linarith
  -- Lemma 5.1: a maximiser
  set S : Set (ℤ × ℤ) := (fun H => (aF H, eF H)) ''
    {H : SubgroupData (d0 := d0) (d1 := d1) Ls | H.tan ≠ ⊥} with hS
  have hSfin : S.Finite := by
    refine ((Set.finite_Icc (-(κ : ℤ)) (finrank ℚ Yq + d1 + 2 * m)).prod
      (Set.finite_Icc (-((d0 + d1 + m : ℕ) : ℤ)) ((d0 + d1 + m : ℕ) : ℤ))).subset ?_
    rintro _ ⟨H, -, rfl⟩
    have h1 : finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) ≤ finrank ℚ Yq :=
      Submodule.finrank_mono inf_le_left
    have h2 := finrank_torusLie H.U
    have h3 : finrank ℂ H.t ≤ m := (Submodule.finrank_le _).trans (by simp)
    have h4 : finrank ℂ H.tan ≤ d0 + d1 + m := (Submodule.finrank_le _).trans hfTan.le
    have h5 : finrank ℂ (Wr Ls W H) ≤ d0 + d1 + m := (Submodule.finrank_le _).trans hfTan.le
    simp only [Set.mem_prod, Set.mem_Icc, aF, eF, nP]
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
  have hT'V : ¬ H'.tan ≤ V := fun hle => hC (hno H' hle)
  set V' := V ⊓ H'.tan with hV'
  have hVdim : finrank ℂ V' + 1 = finrank ℂ H'.tan := by
    have hlt : V < V ⊔ H'.tan := lt_of_le_of_ne le_sup_left fun heq => hT'V (heq ▸ le_sup_right)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank ℂ ↥(V ⊔ H'.tan) ≤ d0 + d1 + m := (Submodule.finrank_le _).trans hfTan.le
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq V H'.tan
    rw [← hV'] at h3
    omega
  set Y' := Y ⊓ H'.tan.toAddSubgroup with hY'
  have hY'fg : Y'.FG := fg_of_le_addSubgroup' hYfg inf_le_left
  have hY'mem : ∀ y ∈ Y', y ∈ V' ∧ y ∈ Lam Ls := fun y hy =>
    ⟨⟨(hY y hy.1).1, hy.2⟩, (hY y hy.1).2⟩
  have hspan' : Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) = Yq ⊓ H'.tan.restrictScalars ℚ := by
    rw [hY', K11.span_inf_addSubgroup, K11.span_submodule_coe]
  set κ' := finrank ℚ ↥(Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) ⊓ Ω) with hκ'
  set m' := finrank ℚ ↥(Submodule.span ℚ (Y' : Set (Tan d0 d1 m))) with hm'
  have hΩT := finrank_Ωs_inf_ge Ls H'
  rw [← hΩ] at hΩT
  -- Lemma 5.2
  have hL52 : finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) + nP Ls H' ≤ m' + (d1 + 2 * m) := by
    have := K11.finrank_le_of_le_sup (Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) (H'.tan.restrictScalars ℚ) Ω
      inf_le_right
    have e : Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω) ⊓ H'.tan.restrictScalars ℚ =
        Yq ⊓ H'.tan.restrictScalars ℚ := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_left : H'.tan.restrictScalars ℚ ≤ _ ⊔ Ω)]
    rw [e, ← hspan', ← hm'] at this
    simp only [nP]; omega
  have hLk : κ + nP Ls H' ≤ κ' + (d1 + 2 * m) := by
    have := K11.finrank_le_of_le_sup (Yq ⊓ Ω) (H'.tan.restrictScalars ℚ) Ω
      (inf_le_right.trans le_sup_right)
    have e : Yq ⊓ Ω ⊓ H'.tan.restrictScalars ℚ = Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) ⊓ Ω := by
      rw [hspan', inf_right_comm]
    rw [e, ← hκ'] at this
    simp only [nP]; omega
  have he'v : eF H' = (finrank ℂ H'.tan : ℤ) - finrank ℂ (Wr Ls W H') := rfl
  have ha'v : aF H' = (finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nP Ls H' := rfl
  have hWr'V : Wr Ls W H' ≤ V' := fun w hw =>
    ⟨hWV ((Wr_le Ls W H' hw).1), (Wr_le Ls W H' hw).2⟩
  by_cases hNR : finrank ℂ (torusLie H'.U) + 2 * finrank ℂ H'.h0 + κ' ≤ 2 * finrank ℂ V' ∨
      H'.t = ⊥
  · -- Theorem 4.1 for `G'`
    obtain ⟨H'', hT''T, hτ, hin⟩ := trans41 Ls hLs H'
      (LSG.CM.thm41SubAt_of LSG.W88.theorem41Abelian hLs H'.t_ab) V' (Wr Ls W H') Y'
      inf_le_right hVdim hWr'V (Wr_rat Ls W H') hY'fg hY'mem hNR
    have hlam : finrank ℚ ↥(Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) ⊓
        (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ ≤
        finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ' := by
      have hle : Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ≤
          Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) :=
        inf_le_inf_right _ (Submodule.span_mono inf_le_left)
      have : FiniteDimensional ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) :=
        Submodule.finiteDimensional_of_le inf_le_left
      have := K11.finrank_le_of_le _ _ Ω hle
      have e1 : Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ⊓ Ω = Yq ⊓ Ω := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ H''.tan.restrictScalars ℚ ⊔ Ω)]
      have e2 : Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ⊓ Ω =
          Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) ⊓ Ω := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ H''.tan.restrictScalars ℚ ⊔ Ω)]
      rw [e1, e2] at this
      omega
    have hmx := hmaxAll H''
    have he''v : eF H'' = (finrank ℂ H''.tan : ℤ) - finrank ℂ (Wr Ls W H'') := rfl
    have ha''v : aF H'' = (finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ +
        nP Ls H'' := rfl
    have hWr'' : finrank ℂ ↥(Wr Ls W H' ⊓ H''.tan) ≤ finrank ℂ (Wr Ls W H'') := by
      rw [hWrEq H', hWrEq H'', inf_assoc, inf_eq_right.mpr hT''T]
    set s : ℤ := ((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
      ((finrank ℂ (Wr Ls W H') : ℤ) - finrank ℂ ↥(Wr Ls W H' ⊓ H''.tan)) with hs
    have hs1 : 1 ≤ s := by simp only [hs]; omega
    have hes : eF H'' ≤ eF H' - s := by rw [he''v, he'v, hs]; push_cast; omega
    set D' : ℤ := (nP Ls H' : ℤ) - κ' with hD'
    have hDD : D' ≤ D := by simp only [hD, hD']; omega
    have hX : aF H' - aF H'' ≤ s * D' + (D - D') := by
      rw [ha'v, ha''v]
      have h1 : (finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) + nP Ls H' ≤
          m' + (d1 + 2 * m) := by exact_mod_cast hL52
      have h2 : (finrank ℚ ↥(Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) ⊓
          (H''.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) + κ ≤
          finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ' := by exact_mod_cast hlam
      simp only [hD, hD']
      linarith
    exact arith_final' hmx hes hX he' ha' hD0 hs1 hDD
  · -- the corner: `B ≠ 0` and (NR) fails
    push Not at hNR
    obtain ⟨hNR1, hNR2⟩ := hNR
    have hspanV : Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) ≤ V.restrictScalars ℚ :=
      Submodule.span_le.mpr fun y hy => (hY'mem y hy).1.1
    have hb : 1 ≤ finrank ℂ H'.t := by
      by_contra h0; push Not at h0
      exact hNR2 (Submodule.finrank_eq_zero.mp (by omega))
    have hfT := finrank_tan Ls H'
    refine corner_false Ls V hno H' hb (Submodule.span ℚ (Y' : Set (Tan d0 d1 m)) ⊓ Ω) ?_
      (inf_le_left.trans hspanV) ?_
    · rw [hspan']; exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · change _ ≤ κ' + 1
      omega

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`**, provided the abelian tangent spaces of
`E₁ × ⋯ × E_m` are `ℚ̄`-rational (`hrat`; true for a power of one curve, `abTan_rat_const`). -/
theorem hyperplaneKappaStd_of_rat (hLs : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃)
    (hrat : ∀ t, IsAbelianTangent Ls t → RationalOverQbar t) :
    MStarCopy.HyperplaneKappa (MStarCopy.gmStd d0 d1 Ls) := by
  intro V W n y hV hWV hWrat hy hineq
  by_contra hcon
  have hno : ∀ H : SubgroupData (d0 := d0) (d1 := d1) Ls, H.tan ≤ V → H.tan = ⊥ := fun H hle =>
    by_contra fun hne => hcon ⟨_, ⟨H, rfl⟩, hne, hle⟩
  set Y := AddSubgroup.closure (Set.range y) with hY
  have hYle : Y ≤ V.toAddSubgroup ⊓ lamSub Ls hLs := by
    rw [hY, AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(hy i).1, (hy i).2⟩
  have hfTan : finrank ℂ (Tan d0 d1 m) = d0 + d1 + m := by simp [add_assoc]
  have hVd : finrank ℂ V + 1 = d0 + d1 + m := by rw [← hfTan]; exact hV
  have hspanY : Submodule.span ℚ (Y : Set (Tan d0 d1 m)) = Submodule.span ℚ (Set.range y) :=
    K11.span_closure_eq _
  refine core Ls hLs V W Y ((AddSubgroup.fg_iff _).mpr ⟨_, rfl, Set.finite_range y⟩)
    (fun z hz => ⟨(hYle hz).1, (hYle hz).2⟩) hVd hWV ((ratT_iff W).mp hWrat) hrat hno ?_
  rw [hspanY]
  have := hineq
  simp only [MStarCopy.gmStd, hfTan] at this
  push_cast at this ⊢
  convert this using 2
  all_goals first | rfl | ring

/-- **`HypStd` for a power of one curve** (no CM hypothesis), every `d₀`, `d₁`. -/
theorem hyperplaneKappaStd_const (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (d0 d1 r : ℕ) :
    MStarCopy.HyperplaneKappa (MStarCopy.gmStd d0 d1 (fun _ : Fin r => L)) :=
  hyperplaneKappaStd_of_rat (fun _ : Fin r => L) (fun _ => ⟨hg₂, hg₃⟩)
    (fun t ht => abTan_rat_const L t ht)

end LSG.W88.K5d

namespace LSG.W88

/-- **`lean_mstar`'s `HypStdCM L`** (W88 §5d for `G_a^{d₀} × G_m^{d₁} × E^r`), unconditionally. -/
theorem hypStdCM (L : PeriodPair) : MStarCopy.HypStdCM L :=
  fun d0 d1 r hg₂ hg₃ => K5d.hyperplaneKappaStd_const L hg₂ hg₃ d0 d1 r

/-- **`lean_mstar`'s `HypStdCMAt L 0`**, unconditionally. -/
theorem hypStdCMAt_zero (L : PeriodPair) : MStarCopy.HypStdCMAt L 0 :=
  fun d1 r hg₂ hg₃ => hypStdCM L 0 d1 r hg₂ hg₃

/-- **`lean_mstar`'s `HypStdCMAt L d`** for every `d`, unconditionally. -/
theorem hypStdCMAt (L : PeriodPair) (d : ℕ) : MStarCopy.HypStdCMAt L d :=
  fun d1 r hg₂ hg₃ => hypStdCM L d d1 r hg₂ hg₃

/-- **`lean_mstar`'s `HypStd`**, assuming only that abelian subvarieties of products of elliptic
curves with algebraic invariants have `ℚ̄`-rational tangent spaces. -/
theorem hypStd_of_rat
    (hrat : ∀ (m : ℕ) (Ls : Fin m → PeriodPair),
      (∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) →
      ∀ t, IsAbelianTangent Ls t → RationalOverQbar t) : MStarCopy.HypStd :=
  fun d0 d1 m Ls hLs => K5d.hyperplaneKappaStd_of_rat Ls hLs (hrat m Ls hLs)

end LSG.W88
