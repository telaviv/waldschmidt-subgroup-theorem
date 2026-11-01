/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVar5dRank

/-!
# A5.9b: the §5d engine on `G_a^{d₀} × G_m^{d₁} × ∏ B_k` (`STAGE_A5.md` §6.5)

**`hyperplaneKappaB_of`**: `HyperplaneKappaOnLsg (gmB d₀ d₁ An) TorInjB` (the W88 §5d hypothesis for toric-injective
hyperplanes), from
* `Trans41B An H′` for every subgroup `H′` (Theorem 4.1 for `H′` in the coordinates of `G`, the conclusion of the
  elliptic `trans41`; to be supplied by the pivot transport and Roy's theorem), and
* `hrat`: `W ∩ T_H` is `ℚ̄`-rational for `ℚ̄`-rational `W` (for the `A`-block: CM rationality of abelian
  subvarieties).

Proof: `K5d.core` verbatim (Lemma 5.1, Lemma 5.2, `arith_final'`), with `Ω = span_ℚ Per`, `W ∩ T_H` in place of its
rational part, and **no corner case**: under `TorInjB`, `κ′ ≤ d₁′` (`kappa_le_of_torInj`), so (NR) holds for `H′`
unless `t′ = 0`.
-/

open Complex Module Submodule LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.MEB (AbBlock PerL perAb IsRatSub tanOf)

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-- `Ω = span_ℚ Ω(G)`. -/
abbrev OmB (d₀ d₁ : ℕ) (B : Fin m → AbBlock) : Submodule ℚ (MEB.Tan d₀ d₁ B) :=
  span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B))

/-- `d₁′ + 2d₂′` of a subgroup. -/
abbrev nPB (H : SubgroupDataB d₀ d₁ B) : ℕ := finrank ℂ (torusLie H.U) + 2 * finrank ℂ H.t

/-- **Theorem 4.1 for the subgroup `H′`, in the coordinates of `G`** (the conclusion of the elliptic `trans41`):
`V ⊂ T_{H′}` a hyperplane of `T_{H′}`, toric-injective, (NR) for `H′` unless `t′ = 0`. -/
def Trans41B (An : ∀ k, AbBlockAn (B k)) (H' : SubgroupDataB d₀ d₁ B) : Prop :=
  ∀ (V W : Submodule ℂ (MEB.Tan d₀ d₁ B)) (Y : AddSubgroup (MEB.Tan d₀ d₁ B)),
    V ≤ H'.tan → finrank ℂ V + 1 = finrank ℂ H'.tan → W ≤ V → RationalOverQbarB W → Y.FG →
    (∀ y ∈ Y, y ∈ V ∧ y ∈ LamB d₀ d₁ An) → TorInjB V →
    (finrank ℂ (torusLie H'.U) + 2 * finrank ℂ H'.h0 +
        finrank ℚ ↥(span ℚ (Y : Set (MEB.Tan d₀ d₁ B)) ⊓ OmB d₀ d₁ B) ≤ 2 * finrank ℂ V ∨ H'.t = ⊥) →
    ∃ H'' : SubgroupDataB d₀ d₁ B, H''.tan ≤ H'.tan ∧
      (finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan) < (finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan ∧
      ((finrank ℚ (span ℚ (Y : Set (MEB.Tan d₀ d₁ B))) : ℤ) -
          finrank ℚ ↥(span ℚ (Y : Set (MEB.Tan d₀ d₁ B)) ⊓ (H''.tan.restrictScalars ℚ ⊔ OmB d₀ d₁ B)) +
          ((nPB H' : ℤ) - nPB H'')) ≤
        (((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
            ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan))) *
          ((nPB H' : ℤ) - finrank ℚ ↥(span ℚ (Y : Set (MEB.Tan d₀ d₁ B)) ⊓ OmB d₀ d₁ B))

/-- The final inequality chase of §5d (copy of `K5d.arith_final'`). -/
lemma arith_finalB {a a'' e e'' s D D' : ℤ} (hmx : a'' * e ≤ a * e'') (hes : e'' ≤ e - s)
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

lemma fg_of_le_addSubgroupB {E : Type*} [AddCommGroup E] {P Q : AddSubgroup E} (hP : P.FG)
    (h : Q ≤ P) : Q.FG := by
  have : Module.Finite ℤ P := Module.Finite.iff_addGroup_fg.mpr hP
  have : Module.Finite ℤ Q :=
    Module.Finite.of_injective (AddSubgroup.inclusion h).toIntLinearMap
      (AddSubgroup.inclusion_injective h)
  exact Module.Finite.iff_addGroup_fg.mp this

lemma finrank_TanB : finrank ℂ (MEB.Tan d₀ d₁ B) = d₀ + d₁ + ∑ k, (B k).g := by
  rw [Module.finrank_prod, Module.finrank_prod]
  simp [Module.finrank_pi_fintype, add_assoc]

lemma torInjB_mono {V V' : Submodule ℂ (MEB.Tan d₀ d₁ B)} (h : V' ≤ V) (hV : TorInjB V) : TorInjB V' :=
  fun v hv => hV v (h hv)

set_option maxHeartbeats 1600000 in
-- the §5d chase
/-- **The core of the §5d deduction** for `G_a^{d₀} × G_m^{d₁} × ∏ B_k`. -/
theorem coreB (An : ∀ k, AbBlockAn (B k)) (htr : ∀ H' : SubgroupDataB d₀ d₁ B, Trans41B An H')
    (V W : Submodule ℂ (MEB.Tan d₀ d₁ B)) (Y : AddSubgroup (MEB.Tan d₀ d₁ B)) (hYfg : Y.FG)
    (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamB d₀ d₁ An) (hV : finrank ℂ V + 1 = d₀ + d₁ + ∑ k, (B k).g)
    (hWV : W ≤ V) (hWr : ∀ H : SubgroupDataB d₀ d₁ B, RationalOverQbarB (W ⊓ H.tan))
    (hTor : TorInjB V)
    (hno : ∀ H : SubgroupDataB d₀ d₁ B, H.tan ≤ V → H.tan = ⊥)
    (hineq : ((finrank ℚ (span ℚ (Y : Set (MEB.Tan d₀ d₁ B))) : ℤ) >
      ((d₁ : ℤ) + 2 * (∑ k, (B k).g : ℕ) -
          finrank ℚ ↥(span ℚ (Y : Set (MEB.Tan d₀ d₁ B)) ⊓ OmB d₀ d₁ B)) *
        (((d₀ + d₁ + ∑ k, (B k).g : ℕ) : ℤ) - 1 - finrank ℂ W))) : False := by
  classical
  set Gd := ∑ k, (B k).g with hGd
  set Yq := span ℚ (Y : Set (MEB.Tan d₀ d₁ B)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  set Ω := OmB d₀ d₁ B with hΩ
  set κ := finrank ℚ ↥(Yq ⊓ Ω) with hκ
  have hΩd : finrank ℚ Ω ≤ d₁ + 2 * Gd := (finrank_span_Per_le (d₀ := d₀) (d₁ := d₁) (B := B)).2
  have hκle : κ ≤ d₁ + 2 * Gd := (Submodule.finrank_mono inf_le_right).trans hΩd
  have hfTan : finrank ℂ (MEB.Tan d₀ d₁ B) = d₀ + d₁ + Gd := finrank_TanB
  have hfT : ∀ H : SubgroupDataB d₀ d₁ B, finrank ℂ H.t ≤ Gd := fun H =>
    (Submodule.finrank_le _).trans (by simp [Module.finrank_pi_fintype, hGd])
  let aF : SubgroupDataB d₀ d₁ B → ℤ := fun H =>
    (finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPB H
  let eF : SubgroupDataB d₀ d₁ B → ℤ := fun H =>
    (finrank ℂ H.tan : ℤ) - finrank ℂ ↥(W ⊓ H.tan)
  have he : ∀ H : SubgroupDataB d₀ d₁ B, H.tan ≠ ⊥ → 0 < eF H := by
    intro H hH
    have hle : W ⊓ H.tan ≤ H.tan := inf_le_right
    have h1 := Submodule.finrank_mono hle
    have h2 : finrank ℂ ↥(W ⊓ H.tan) ≠ finrank ℂ H.tan := by
      intro heq
      have := Submodule.eq_of_le_of_finrank_eq hle heq
      exact hH (hno H (this ▸ inf_le_left |>.trans hWV))
    simp only [eF]; omega
  have hzero : ∀ H : SubgroupDataB d₀ d₁ B, H.tan = ⊥ → aF H = 0 ∧ eF H = 0 := by
    intro H hH
    have hf := finrank_tanB H
    rw [hH, finrank_bot] at hf
    have hTq : H.tan.restrictScalars ℚ = ⊥ := by rw [hH]; rfl
    have hW0 : finrank ℂ ↥(W ⊓ H.tan) = 0 := by
      have := Submodule.finrank_mono (inf_le_right : W ⊓ H.tan ≤ H.tan)
      have h0 : finrank ℂ H.tan = 0 := by rw [hH, finrank_bot]
      omega
    refine ⟨?_, ?_⟩
    · change (finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPB H = 0
      rw [hTq, bot_sup_eq, ← hκ]; simp only [nPB]; omega
    · change (finrank ℂ H.tan : ℤ) - finrank ℂ ↥(W ⊓ H.tan) = 0
      rw [hW0, hH, finrank_bot]; simp
  -- the value at `G`
  set G := topSubB d₀ d₁ B with hG
  have hGtan : G.tan = ⊤ := topSubB_tan
  have hGC : G.tan ≠ ⊥ := by
    rw [hGtan]; intro h
    have := congrArg (fun S : Submodule ℂ (MEB.Tan d₀ d₁ B) => finrank ℂ S) h
    simp only [finrank_top, finrank_bot, hfTan] at this
    omega
  have hnPG : nPB G = d₁ + 2 * Gd := by
    have h := K5d.finrank_torusLie (⊥ : Submodule ℚ (Fin d₁ → ℚ))
    simp only [finrank_bot, add_zero] at h
    change finrank ℂ (torusLie (⊥ : Submodule ℚ (Fin d₁ → ℚ))) +
      2 * finrank ℂ (⊤ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) = _
    rw [h, finrank_top]
    simp [Module.finrank_pi_fintype, hGd]
  have haG : aF G = (finrank ℚ Yq : ℤ) - κ + (d₁ + 2 * Gd) := by
    have : G.tan.restrictScalars ℚ = ⊤ := by rw [hGtan]; rfl
    change (finrank ℚ ↥(Yq ⊓ (G.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPB G = _
    rw [this, top_sup_eq, inf_top_eq, hnPG]
    push_cast; ring
  have heG : eF G = ((d₀ + d₁ + Gd : ℕ) : ℤ) - finrank ℂ W := by
    change (finrank ℂ G.tan : ℤ) - finrank ℂ ↥(W ⊓ G.tan) = _
    rw [hGtan, inf_top_eq, finrank_top, hfTan]
  set D : ℤ := (d₁ : ℤ) + 2 * Gd - κ with hD
  have hD0 : 0 ≤ D := by omega
  have hGineq : D * eF G < aF G := by
    rw [haG, heG]
    have : D * (((d₀ + d₁ + Gd : ℕ) : ℤ) - finrank ℂ W) =
        D * (((d₀ + d₁ + Gd : ℕ) : ℤ) - 1 - finrank ℂ W) + D := by ring
    rw [this]; simp only [hD] at hineq ⊢; push_cast at hineq ⊢; linarith
  -- Lemma 5.1: a maximiser
  set S : Set (ℤ × ℤ) := (fun H => (aF H, eF H)) ''
    {H : SubgroupDataB d₀ d₁ B | H.tan ≠ ⊥} with hS
  have hSfin : S.Finite := by
    refine ((Set.finite_Icc (-(κ : ℤ)) (finrank ℚ Yq + d₁ + 2 * Gd)).prod
      (Set.finite_Icc (-((d₀ + d₁ + Gd : ℕ) : ℤ)) ((d₀ + d₁ + Gd : ℕ) : ℤ))).subset ?_
    rintro _ ⟨H, -, rfl⟩
    have h1 : finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) ≤ finrank ℚ Yq :=
      Submodule.finrank_mono inf_le_left
    have h2 := K5d.finrank_torusLie H.U
    have h3 := hfT H
    have h4 : finrank ℂ H.tan ≤ d₀ + d₁ + Gd := (Submodule.finrank_le _).trans hfTan.le
    have h5 : finrank ℂ ↥(W ⊓ H.tan) ≤ d₀ + d₁ + Gd := (Submodule.finrank_le _).trans hfTan.le
    simp only [Set.mem_prod, Set.mem_Icc, aF, eF, nPB]
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
    have h2 : finrank ℂ ↥(V ⊔ H'.tan) ≤ d₀ + d₁ + Gd := (Submodule.finrank_le _).trans hfTan.le
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq V H'.tan
    rw [← hV'] at h3
    omega
  set Y' := Y ⊓ H'.tan.toAddSubgroup with hY'
  have hY'fg : Y'.FG := fg_of_le_addSubgroupB hYfg inf_le_left
  have hY'mem : ∀ y ∈ Y', y ∈ V' ∧ y ∈ LamB d₀ d₁ An := fun y hy =>
    ⟨⟨(hY y hy.1).1, hy.2⟩, (hY y hy.1).2⟩
  have hspan' : span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) = Yq ⊓ H'.tan.restrictScalars ℚ := by
    rw [hY', K11.span_inf_addSubgroup, K11.span_submodule_coe]
  set κ' := finrank ℚ ↥(span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) ⊓ Ω) with hκ'
  set m' := finrank ℚ ↥(span ℚ (Y' : Set (MEB.Tan d₀ d₁ B))) with hm'
  have hΩT := finrank_Per_inf_tan_ge (d₀ := d₀) H'.h0 H'.U H'.t H'.t_rat
  have hΩT' : nPB H' ≤ finrank ℚ ↥(Ω ⊓ H'.tan.restrictScalars ℚ) := hΩT
  -- Lemma 5.2
  have hL52 : finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) + nPB H' ≤ m' + (d₁ + 2 * Gd) := by
    have := K11.finrank_le_of_le_sup (Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) (H'.tan.restrictScalars ℚ)
      Ω inf_le_right
    have e : Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω) ⊓ H'.tan.restrictScalars ℚ =
        Yq ⊓ H'.tan.restrictScalars ℚ := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_left : H'.tan.restrictScalars ℚ ≤ _ ⊔ Ω)]
    rw [e, ← hspan', ← hm'] at this
    have : finrank ℚ ↥(Ω ⊓ H'.tan.restrictScalars ℚ) ≤ finrank ℚ Ω := Submodule.finrank_mono inf_le_left
    omega
  have hLk : κ + nPB H' ≤ κ' + (d₁ + 2 * Gd) := by
    have := K11.finrank_le_of_le_sup (Yq ⊓ Ω) (H'.tan.restrictScalars ℚ) Ω
      (inf_le_right.trans le_sup_right)
    have e : Yq ⊓ Ω ⊓ H'.tan.restrictScalars ℚ =
        span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) ⊓ Ω := by
      rw [hspan', inf_right_comm]
    rw [e, ← hκ'] at this
    omega
  have he'v : eF H' = (finrank ℂ H'.tan : ℤ) - finrank ℂ ↥(W ⊓ H'.tan) := rfl
  have ha'v : aF H' = (finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPB H' := rfl
  have hWr'V : W ⊓ H'.tan ≤ V' := fun w hw => ⟨hWV hw.1, hw.2⟩
  -- (NR) for `H′` unless `t′ = 0`: toric injectivity
  have hNR : finrank ℂ (torusLie H'.U) + 2 * finrank ℂ H'.h0 + κ' ≤ 2 * finrank ℂ V' ∨
      H'.t = ⊥ := by
    by_cases ht : H'.t = ⊥
    · exact Or.inr ht
    left
    have : FiniteDimensional ℚ ↥(span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) ⊓ Ω) :=
      Submodule.finiteDimensional_of_le inf_le_right
    have hk := kappa_le_of_torInj hTor H'.U (span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) ⊓ Ω)
      (fun v hv => (span_le.mpr fun y hy => (hY'mem y hy).1.1 : span ℚ (Y' : Set _) ≤
        V.restrictScalars ℚ) hv.1)
      inf_le_right
      (fun v hv => by
        have h1 : v ∈ H'.tan := (span_le.mpr fun y hy => (hY'mem y hy).1.2 :
          span ℚ (Y' : Set _) ≤ H'.tan.restrictScalars ℚ) hv.1
        exact h1.2.1)
    have ht1 : 1 ≤ finrank ℂ H'.t := by
      by_contra h0; push Not at h0
      exact ht (Submodule.finrank_eq_zero.mp (by omega))
    have hfT' := finrank_tanB H'
    omega
  obtain ⟨H'', hT''T, hτ, hin⟩ := htr H' V' (W ⊓ H'.tan) Y' inf_le_right hVdim hWr'V (hWr H') hY'fg
    hY'mem (torInjB_mono inf_le_left hTor) hNR
  have hlam : finrank ℚ ↥(span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) ⊓
      (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ ≤
      finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ' := by
    have hle : span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ≤
        Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) :=
      inf_le_inf_right _ (span_mono inf_le_left)
    have : FiniteDimensional ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have := K11.finrank_le_of_le _ _ Ω hle
    have e1 : Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ⊓ Ω = Yq ⊓ Ω := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ H''.tan.restrictScalars ℚ ⊔ Ω)]
    have e2 : span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ⊓ Ω =
        span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) ⊓ Ω := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ H''.tan.restrictScalars ℚ ⊔ Ω)]
    rw [e1, e2] at this
    omega
  have hmx := hmaxAll H''
  have he''v : eF H'' = (finrank ℂ H''.tan : ℤ) - finrank ℂ ↥(W ⊓ H''.tan) := rfl
  have ha''v : aF H'' = (finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ +
      nPB H'' := rfl
  have hWr'' : finrank ℂ ↥(W ⊓ H'.tan ⊓ H''.tan) ≤ finrank ℂ ↥(W ⊓ H''.tan) := by
    rw [inf_assoc, inf_eq_right.mpr hT''T]
  set s : ℤ := ((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
    ((finrank ℂ ↥(W ⊓ H'.tan) : ℤ) - finrank ℂ ↥(W ⊓ H'.tan ⊓ H''.tan)) with hs
  have hs1 : 1 ≤ s := by simp only [hs]; omega
  have hes : eF H'' ≤ eF H' - s := by rw [he''v, he'v, hs]; push_cast; omega
  set D' : ℤ := (nPB H' : ℤ) - κ' with hD'
  have hDD : D' ≤ D := by simp only [hD, hD']; omega
  have hX : aF H' - aF H'' ≤ s * D' + (D - D') := by
    rw [ha'v, ha''v]
    have h1 : (finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) + nPB H' ≤
        m' + (d₁ + 2 * Gd) := by exact_mod_cast hL52
    have h2 : (finrank ℚ ↥(span ℚ (Y' : Set (MEB.Tan d₀ d₁ B)) ⊓
        (H''.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) + κ ≤
        finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ' := by exact_mod_cast hlam
    simp only [hD, hD']
    linarith
  exact arith_finalB hmx hes hX he' ha' hD0 hs1 hDD

/-! ### The group model and the §5d statement -/

variable (d₀ d₁) in
/-- **The group model of `G_a^{d₀} × G_m^{d₁} × ∏ B_k`** with `lam = LamB An`, `per = span_ℚ PerL`. -/
def gmB (An : ∀ k, AbBlockAn (B k)) : MStarCopy.GroupModel (MEB.Tan d₀ d₁ B) where
  d₁ := d₁
  d₂ := ∑ k, (B k).g
  alg := AlgTanB
  lam := ((LamB d₀ d₁ An : AddSubgroup (MEB.Tan d₀ d₁ B)) : Set (MEB.Tan d₀ d₁ B))
  per := span ℚ (PerL d₀ d₁ B (latF An) : Set (MEB.Tan d₀ d₁ B))
  sub := fun S => ∃ H : SubgroupDataB d₀ d₁ B, S = H.tan

lemma rationalB_of_gm (An : ∀ k, AbBlockAn (B k)) {W : Submodule ℂ (MEB.Tan d₀ d₁ B)}
    (hW : (gmB d₀ d₁ An).Rational W) : RationalOverQbarB W := by
  obtain ⟨S, hS, rfl⟩ := hW
  apply le_antisymm
  · exact span_mono fun v hv => ⟨subset_span hv, hS v hv⟩
  · exact span_le.mpr fun _ hv => hv.1

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × ∏ B_k` on toric-injective hyperplanes**, from Theorem 4.1 for every
subgroup (`htr`) and the rationality of `W ∩ T_H` (`hrat`). -/
theorem hyperplaneKappaB_of (An : ∀ k, AbBlockAn (B k))
    (htr : ∀ H' : SubgroupDataB d₀ d₁ B, Trans41B An H')
    (hrat : ∀ (W : Submodule ℂ (MEB.Tan d₀ d₁ B)) (H : SubgroupDataB d₀ d₁ B),
      RationalOverQbarB W → RationalOverQbarB (W ⊓ H.tan)) :
    HyperplaneKappaOnLsg (gmB d₀ d₁ An) TorInjB := by
  intro V W n y hV hWV hWrat hgood hy hineq
  by_contra hcon
  have hno : ∀ H : SubgroupDataB d₀ d₁ B, H.tan ≤ V → H.tan = ⊥ := fun H hle =>
    by_contra fun hne => hcon ⟨_, ⟨H, rfl⟩, hne, hle⟩
  set Y := AddSubgroup.closure (Set.range y) with hY
  have hYle : Y ≤ V.toAddSubgroup ⊓ LamB d₀ d₁ An := by
    rw [hY, AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(hy i).1, (hy i).2⟩
  have hVd : finrank ℂ V + 1 = d₀ + d₁ + ∑ k, (B k).g := by rw [← finrank_TanB]; exact hV
  have hspanY : span ℚ (Y : Set (MEB.Tan d₀ d₁ B)) = span ℚ (Set.range y) := K11.span_closure_eq _
  have hWr := rationalB_of_gm An hWrat
  refine coreB An htr V W Y ((AddSubgroup.fg_iff _).mpr ⟨_, rfl, Set.finite_range y⟩)
    (fun z hz => ⟨(hYle hz).1, (hYle hz).2⟩) hVd hWV (fun H => hrat W H hWr) hgood hno ?_
  rw [hspanY]
  have hper : span ℚ (PerL d₀ d₁ B (latF An) : Set (MEB.Tan d₀ d₁ B)) = OmB d₀ d₁ B :=
    LSG.MEB.span_perL (fun k => (An k).lat_le) (fun k => (An k).lat_nsmul)
  have := hineq
  simp only [gmB, finrank_TanB] at this
  push_cast at this ⊢
  rw [← hper]
  exact this

end LSG.W88
