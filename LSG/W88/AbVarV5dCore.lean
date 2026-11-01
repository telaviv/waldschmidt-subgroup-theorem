/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarV5dRank
import LSG.W88.AbVar5dCore

/-!
# M2.7b: the §5d core on the vector-extension class

**`coreAV`**: the W88 §5d chase (Lemma 5.1, Lemma 5.2, `arith_finalB`) on
`G = G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)`, copied from `coreB` (`AbVar5dCore.lean`) with
`Ω = span_ℚ PerAVf`, `d₂ = Σ g_k + r`, `nPAV H = dim U^⊥ + 2 d₂(H)` (`d₂(H) ≤ dim t + r`,
`rk (Ω ∩ T_H) ≥ dim U^⊥ + 2 dim t`), from `Trans41AV An H′` (Theorem 4.1 for every member, in the coordinates of
`G`). As in the abelian case there is no corner: under `TorInjAV`, `κ′ ≤ dim U^⊥` (`kappa_le_of_torInjAV`), so (NR)
holds for `H′` unless `t′ = 0` (here `d₂(H′) = dim t′ + r ≥ 1` by `PerTanFib`).

**`hyperplaneKappaAbVarV_of_trans`**: `HyperplaneKappaAbVarV An M` from `Trans41AV` for every member, `PerTanFib`
and the rationality of `W ∩ T_H`.
-/

open Complex Module Submodule LSG.AuxAV LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.W88.AVS

open LSG.MEB (IsRatSub)
open LSG.MEBV (VBlock perTanId perBase)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {M : Matrix (Fin r) (Fin m) ℂ}

lemma mem_tan_tor {H : SubgroupDataAV d₀ d₁ B M} {x : TanAV d₀ d₁ r B} (hx : x ∈ H.tan) :
    x.2.1 ∈ torusLie H.U := by
  have hle : H.tan ≤ (torusLie H.U).comap prBA := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨γ, -, rfl⟩; exact (torusLie H.U).zero_mem
    · rintro _ ⟨b, hb, rfl⟩; exact hb
    · rintro _ ⟨_, -, rfl⟩; exact (torusLie H.U).zero_mem
  exact hle hx

/-- **`d₂(H) = dim t + r` for `t ≠ 0`** (under `PerTanFib`). -/
lemma d2H_eq_of_ne (hF : PerTanFib B M) (H : SubgroupDataAV d₀ d₁ B M) (hne : H.t ≠ ⊥) :
    d2H H = finrank ℂ H.t + r := by
  set S := H.tan ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓ LinearMap.ker prBA)
  let f : TanAV d₀ d₁ r B →ₗ[ℂ] (∀ k, Fin (B k).g → ℂ) × (Fin r → ℂ) :=
    (LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)
  have hinj' : Function.Injective (f.domRestrict S) := by
    intro x y h
    have h' : f ((x : TanAV d₀ d₁ r B) - (y : TanAV d₀ d₁ r B)) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h
    have hm := S.sub_mem x.2 y.2
    exact Subtype.ext (sub_eq_zero.mp (Prod.ext hm.2.1 (Prod.ext hm.2.2 h')))
  have hmap : S.map f = H.t.prod ⊤ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact ⟨mem_tan_z hx.1, mem_top⟩
    · rintro ⟨z, s⟩ ⟨hz, -⟩
      refine ⟨(0, 0, z, s), ⟨(mem_tan_iff_of_ne hF H hne).mpr
        ⟨(H.gam.map (LinearMap.fst ℂ _ _)).zero_mem, (torusLie H.U).zero_mem, hz⟩, rfl, rfl⟩, rfl⟩
  have h2 : finrank ℂ ↥(S.map f) = d2H H := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj']; rfl
  rw [← h2, hmap, K5d.finrank_prodSub, finrank_top, Module.finrank_fin_fun]

lemma torInjAV_mono {V V' : Submodule ℂ (TanAV d₀ d₁ r B)} (h : V' ≤ V) (hV : TorInjAV M V) :
    TorInjAV M V' :=
  fun v hv => hV v (h hv)

/-- **Theorem 4.1 for the member `H′`, in the coordinates of `G`**: `V ⊂ T_{H′}` a hyperplane of `T_{H′}`,
toric-injective, (NR) for `H′` unless `t′ = 0`. -/
def Trans41AV (An : ∀ k, VBlockAn (B k)) (H' : SubgroupDataAV d₀ d₁ B M) : Prop :=
  ∀ (V W : Submodule ℂ (TanAV d₀ d₁ r B)) (Y : AddSubgroup (TanAV d₀ d₁ r B)),
    V ≤ H'.tan → finrank ℂ V + 1 = finrank ℂ H'.tan → W ≤ V → RationalOverQbarAV W → Y.FG →
    (∀ y ∈ Y, y ∈ V ∧ y ∈ LamAV d₀ d₁ An M) → TorInjAV M V →
    (finrank ℂ (torusLie H'.U) + 2 * finrank ℂ (H'.gam.map (LinearMap.fst ℂ _ _)) +
        finrank ℚ ↥(span ℚ (Y : Set (TanAV d₀ d₁ r B)) ⊓ OmAV d₀ d₁ B M) ≤ 2 * finrank ℂ V ∨
      H'.t = ⊥) →
    ∃ H'' : SubgroupDataAV d₀ d₁ B M, H''.tan ≤ H'.tan ∧
      (finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan) < (finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan ∧
      ((finrank ℚ (span ℚ (Y : Set (TanAV d₀ d₁ r B))) : ℤ) -
          finrank ℚ ↥(span ℚ (Y : Set (TanAV d₀ d₁ r B)) ⊓
            (H''.tan.restrictScalars ℚ ⊔ OmAV d₀ d₁ B M)) +
          ((nPAV H' : ℤ) - nPAV H'')) ≤
        (((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
            ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan))) *
          ((nPAV H' : ℤ) - finrank ℚ ↥(span ℚ (Y : Set (TanAV d₀ d₁ r B)) ⊓ OmAV d₀ d₁ B M))

set_option maxHeartbeats 1600000 in
-- the §5d chase
/-- **The core of the §5d deduction** for `G_a^{d₀} × G_m^{d₁} × ∏ B_k`. -/
theorem coreAV (An : ∀ k, VBlockAn (B k)) (hF : PerTanFib B M)
    (htr : ∀ H' : SubgroupDataAV d₀ d₁ B M, Trans41AV An H')
    (V W : Submodule ℂ (TanAV d₀ d₁ r B)) (Y : AddSubgroup (TanAV d₀ d₁ r B)) (hYfg : Y.FG)
    (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamAV d₀ d₁ An M) (hV : finrank ℂ V + 1 = d₀ + d₁ + (∑ k, (B k).g + r))
    (hWV : W ≤ V) (hWr : ∀ H : SubgroupDataAV d₀ d₁ B M, RationalOverQbarAV (W ⊓ H.tan))
    (hTor : TorInjAV M V)
    (hno : ∀ H : SubgroupDataAV d₀ d₁ B M, H.tan ≤ V → H.tan = ⊥)
    (hineq : ((finrank ℚ (span ℚ (Y : Set (TanAV d₀ d₁ r B))) : ℤ) >
      ((d₁ : ℤ) + 2 * ((∑ k, (B k).g + r : ℕ) : ℤ) -
          finrank ℚ ↥(span ℚ (Y : Set (TanAV d₀ d₁ r B)) ⊓ OmAV d₀ d₁ B M)) *
        (((d₀ + d₁ + (∑ k, (B k).g + r) : ℕ) : ℤ) - 1 - finrank ℂ W))) : False := by
  classical
  set Gd := ∑ k, (B k).g + r with hGd
  set Yq := span ℚ (Y : Set (TanAV d₀ d₁ r B)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  set Ω := OmAV d₀ d₁ B M with hΩ
  set κ := finrank ℚ ↥(Yq ⊓ Ω) with hκ
  have hΩd : finrank ℚ Ω + 2 * r ≤ d₁ + 2 * Gd := by
    have : finrank ℚ Ω ≤ d₁ + 2 * ∑ k, (B k).g := finrank_OmAV_le
    omega
  have hκle : κ ≤ d₁ + 2 * Gd := (Submodule.finrank_mono inf_le_right).trans (by omega)
  have hfTan : finrank ℂ (TanAV d₀ d₁ r B) = d₀ + d₁ + Gd := by
    have := finrank_TanAV (d₀ := d₀) (d₁ := d₁) (r := r) (B := B); omega
  have hfT : ∀ H : SubgroupDataAV d₀ d₁ B M, nPAV H ≤ d₁ + 2 * Gd := fun H => by
    have h1 := nPAV_le H
    have h2 : finrank ℂ H.t ≤ ∑ k, (B k).g :=
      (Submodule.finrank_le _).trans (by simp [Module.finrank_pi_fintype])
    have h3 := K5d.finrank_torusLie H.U
    omega
  let aF : SubgroupDataAV d₀ d₁ B M → ℤ := fun H =>
    (finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPAV H
  let eF : SubgroupDataAV d₀ d₁ B M → ℤ := fun H =>
    (finrank ℂ H.tan : ℤ) - finrank ℂ ↥(W ⊓ H.tan)
  have he : ∀ H : SubgroupDataAV d₀ d₁ B M, H.tan ≠ ⊥ → 0 < eF H := by
    intro H hH
    have hle : W ⊓ H.tan ≤ H.tan := inf_le_right
    have h1 := Submodule.finrank_mono hle
    have h2 : finrank ℂ ↥(W ⊓ H.tan) ≠ finrank ℂ H.tan := by
      intro heq
      have := Submodule.eq_of_le_of_finrank_eq hle heq
      exact hH (hno H (this ▸ inf_le_left |>.trans hWV))
    simp only [eF]; omega
  have hzero : ∀ H : SubgroupDataAV d₀ d₁ B M, H.tan = ⊥ → aF H = 0 ∧ eF H = 0 := by
    intro H hH
    have hf := finrank_tan_eq H
    rw [hH, finrank_bot] at hf
    have hTq : H.tan.restrictScalars ℚ = ⊥ := by rw [hH]; rfl
    have hW0 : finrank ℂ ↥(W ⊓ H.tan) = 0 := by
      have := Submodule.finrank_mono (inf_le_right : W ⊓ H.tan ≤ H.tan)
      have h0 : finrank ℂ H.tan = 0 := by rw [hH, finrank_bot]
      omega
    refine ⟨?_, ?_⟩
    · change (finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPAV H = 0
      rw [hTq, bot_sup_eq, ← hκ]; simp only [nPAV]; omega
    · change (finrank ℂ H.tan : ℤ) - finrank ℂ ↥(W ⊓ H.tan) = 0
      rw [hW0, hH, finrank_bot]; simp
  -- the value at `G`
  set G := topSubAV d₀ d₁ B M with hG
  have hGtan : G.tan = ⊤ := topSubAV_tan
  have hGC : G.tan ≠ ⊥ := by
    rw [hGtan]; intro h
    have := congrArg (fun S : Submodule ℂ (TanAV d₀ d₁ r B) => finrank ℂ S) h
    simp only [finrank_top, finrank_bot, hfTan] at this
    omega
  have hnPG : nPAV G = d₁ + 2 * Gd := by
    have := nPAV_top (d₀ := d₀) (d₁ := d₁) (B := B) (M := M); omega
  have haG : aF G = (finrank ℚ Yq : ℤ) - κ + (d₁ + 2 * Gd) := by
    have : G.tan.restrictScalars ℚ = ⊤ := by rw [hGtan]; rfl
    change (finrank ℚ ↥(Yq ⊓ (G.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPAV G = _
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
    {H : SubgroupDataAV d₀ d₁ B M | H.tan ≠ ⊥} with hS
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
  have hY'mem : ∀ y ∈ Y', y ∈ V' ∧ y ∈ LamAV d₀ d₁ An M := fun y hy =>
    ⟨⟨(hY y hy.1).1, hy.2⟩, (hY y hy.1).2⟩
  have hspan' : span ℚ (Y' : Set (TanAV d₀ d₁ r B)) = Yq ⊓ H'.tan.restrictScalars ℚ := by
    rw [hY', K11.span_inf_addSubgroup, K11.span_submodule_coe]
  set κ' := finrank ℚ ↥(span ℚ (Y' : Set (TanAV d₀ d₁ r B)) ⊓ Ω) with hκ'
  set m' := finrank ℚ ↥(span ℚ (Y' : Set (TanAV d₀ d₁ r B))) with hm'
  have hΩT : finrank ℂ (torusLie H'.U) + 2 * finrank ℂ H'.t ≤
      finrank ℚ ↥(Ω ⊓ H'.tan.restrictScalars ℚ) := finrank_OmAV_inf_ge H'
  have hΩT' : nPAV H' ≤ finrank ℚ ↥(Ω ⊓ H'.tan.restrictScalars ℚ) + 2 * r := by
    have := nPAV_le H'; omega
  -- Lemma 5.2
  have hL52 : finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) + nPAV H' ≤ m' + (d₁ + 2 * Gd) := by
    have := K11.finrank_le_of_le_sup (Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) (H'.tan.restrictScalars ℚ)
      Ω inf_le_right
    have e : Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω) ⊓ H'.tan.restrictScalars ℚ =
        Yq ⊓ H'.tan.restrictScalars ℚ := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_left : H'.tan.restrictScalars ℚ ≤ _ ⊔ Ω)]
    rw [e, ← hspan', ← hm'] at this
    have : finrank ℚ ↥(Ω ⊓ H'.tan.restrictScalars ℚ) ≤ finrank ℚ Ω := Submodule.finrank_mono inf_le_left
    omega
  have hLk : κ + nPAV H' ≤ κ' + (d₁ + 2 * Gd) := by
    have := K11.finrank_le_of_le_sup (Yq ⊓ Ω) (H'.tan.restrictScalars ℚ) Ω
      (inf_le_right.trans le_sup_right)
    have e : Yq ⊓ Ω ⊓ H'.tan.restrictScalars ℚ =
        span ℚ (Y' : Set (TanAV d₀ d₁ r B)) ⊓ Ω := by
      rw [hspan', inf_right_comm]
    rw [e, ← hκ'] at this
    omega
  have he'v : eF H' = (finrank ℂ H'.tan : ℤ) - finrank ℂ ↥(W ⊓ H'.tan) := rfl
  have ha'v : aF H' = (finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ + nPAV H' := rfl
  have hWr'V : W ⊓ H'.tan ≤ V' := fun w hw => ⟨hWV hw.1, hw.2⟩
  -- (NR) for `H′` unless `t′ = 0`: toric injectivity
  have hNR : finrank ℂ (torusLie H'.U) + 2 * finrank ℂ (H'.gam.map (LinearMap.fst ℂ _ _)) + κ' ≤ 2 * finrank ℂ V' ∨
      H'.t = ⊥ := by
    by_cases ht : H'.t = ⊥
    · exact Or.inr ht
    left
    have : FiniteDimensional ℚ ↥(span ℚ (Y' : Set (TanAV d₀ d₁ r B)) ⊓ Ω) :=
      Submodule.finiteDimensional_of_le inf_le_right
    have hk := kappa_le_of_torInjAV hTor H'.U (span ℚ (Y' : Set (TanAV d₀ d₁ r B)) ⊓ Ω)
      (fun v hv => (span_le.mpr fun y hy => (hY'mem y hy).1.1 : span ℚ (Y' : Set _) ≤
        V.restrictScalars ℚ) hv.1)
      inf_le_right
      (fun v hv => by
        have h1 : v ∈ H'.tan := (span_le.mpr fun y hy => (hY'mem y hy).1.2 :
          span ℚ (Y' : Set _) ≤ H'.tan.restrictScalars ℚ) hv.1
        exact mem_tan_tor h1)
    have ht1 : 1 ≤ finrank ℂ H'.t := by
      by_contra h0; push Not at h0
      exact ht (Submodule.finrank_eq_zero.mp (by omega))
    have hfT' := finrank_tan_eq H'
    have hd2 := d2H_eq_of_ne hF H' ht
    omega
  obtain ⟨H'', hT''T, hτ, hin⟩ := htr H' V' (W ⊓ H'.tan) Y' inf_le_right hVdim hWr'V (hWr H') hY'fg
    hY'mem (torInjAV_mono inf_le_left hTor) hNR
  have hlam : finrank ℚ ↥(span ℚ (Y' : Set (TanAV d₀ d₁ r B)) ⊓
      (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ ≤
      finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ' := by
    have hle : span ℚ (Y' : Set (TanAV d₀ d₁ r B)) ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ≤
        Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) :=
      inf_le_inf_right _ (span_mono inf_le_left)
    have : FiniteDimensional ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have := K11.finrank_le_of_le _ _ Ω hle
    have e1 : Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ⊓ Ω = Yq ⊓ Ω := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ H''.tan.restrictScalars ℚ ⊔ Ω)]
    have e2 : span ℚ (Y' : Set (TanAV d₀ d₁ r B)) ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) ⊓ Ω =
        span ℚ (Y' : Set (TanAV d₀ d₁ r B)) ⊓ Ω := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ H''.tan.restrictScalars ℚ ⊔ Ω)]
    rw [e1, e2] at this
    omega
  have hmx := hmaxAll H''
  have he''v : eF H'' = (finrank ℂ H''.tan : ℤ) - finrank ℂ ↥(W ⊓ H''.tan) := rfl
  have ha''v : aF H'' = (finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) - κ +
      nPAV H'' := rfl
  have hWr'' : finrank ℂ ↥(W ⊓ H'.tan ⊓ H''.tan) ≤ finrank ℂ ↥(W ⊓ H''.tan) := by
    rw [inf_assoc, inf_eq_right.mpr hT''T]
  set s : ℤ := ((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
    ((finrank ℂ ↥(W ⊓ H'.tan) : ℤ) - finrank ℂ ↥(W ⊓ H'.tan ⊓ H''.tan)) with hs
  have hs1 : 1 ≤ s := by simp only [hs]; omega
  have hes : eF H'' ≤ eF H' - s := by rw [he''v, he'v, hs]; push_cast; omega
  set D' : ℤ := (nPAV H' : ℤ) - κ' with hD'
  have hDD : D' ≤ D := by simp only [hD, hD']; omega
  have hX : aF H' - aF H'' ≤ s * D' + (D - D') := by
    rw [ha'v, ha''v]
    have h1 : (finrank ℚ ↥(Yq ⊓ (H'.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) + nPAV H' ≤
        m' + (d₁ + 2 * Gd) := by exact_mod_cast hL52
    have h2 : (finrank ℚ ↥(span ℚ (Y' : Set (TanAV d₀ d₁ r B)) ⊓
        (H''.tan.restrictScalars ℚ ⊔ Ω)) : ℤ) + κ ≤
        finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) + κ' := by exact_mod_cast hlam
    simp only [hD, hD']
    linarith
  exact arith_finalB hmx hes hX he' ha' hD0 hs1 hDD


lemma rationalAV_of_gm (An : ∀ k, VBlockAn (B k)) {W : Submodule ℂ (TanAV d₀ d₁ r B)}
    (hW : (gmLsgAV d₀ d₁ An M).Rational W) : RationalOverQbarAV W := by
  obtain ⟨S, hS, rfl⟩ := hW
  apply le_antisymm
  · exact span_mono fun v hv => ⟨subset_span hv, hS v hv⟩
  · exact span_le.mpr fun _ hv => hv.1

/-- **W88 §5d for the vector-extension class on toric-injective hyperplanes**, from Theorem 4.1 for every member
(`htr`), `PerTanFib` and the rationality of `W ∩ T_H` (`hrat`). -/
theorem hyperplaneKappaAbVarV_of_trans (An : ∀ k, VBlockAn (B k)) (hF : PerTanFib B M)
    (htr : ∀ d₀ d₁ (H' : SubgroupDataAV d₀ d₁ B M), Trans41AV An H')
    (hrat : ∀ d₀ d₁ (W : Submodule ℂ (TanAV d₀ d₁ r B)) (H : SubgroupDataAV d₀ d₁ B M),
      RationalOverQbarAV W → RationalOverQbarAV (W ⊓ H.tan)) :
    HyperplaneKappaAbVarV An M := by
  intro d₀ d₁ V W n y hV hWV hWrat hgood hy hineq
  by_contra hcon
  have hno : ∀ H : SubgroupDataAV d₀ d₁ B M, H.tan ≤ V → H.tan = ⊥ := fun H hle =>
    by_contra fun hne => hcon ⟨_, ⟨H, rfl, fibOK_of_perTanFib hF H⟩, hne, hle⟩
  set Y := AddSubgroup.closure (Set.range y) with hY
  have hYle : Y ≤ V.toAddSubgroup ⊓ LamAV d₀ d₁ An M := by
    rw [hY, AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(hy i).1, (hy i).2⟩
  have hVd : finrank ℂ V + 1 = d₀ + d₁ + (∑ k, (B k).g + r) := by
    rw [hV, finrank_TanAV]; ring
  have hspanY : span ℚ (Y : Set (TanAV d₀ d₁ r B)) = span ℚ (Set.range y) := K11.span_closure_eq _
  have hWr := rationalAV_of_gm An hWrat
  refine coreAV An hF (htr d₀ d₁) V W Y ((AddSubgroup.fg_iff _).mpr ⟨_, rfl, Set.finite_range y⟩)
    (fun z hz => ⟨(hYle hz).1, (hYle hz).2⟩) hVd hWV (fun H => hrat d₀ d₁ W H hWr) hgood hno ?_
  rw [hspanY]
  have hper := span_perAV_eq (d₀ := d₀) (d₁ := d₁) (M := M) An
  have e1 : finrank ℚ ↥(span ℚ (Set.range y) ⊓ (gmLsgAV d₀ d₁ An M).per) =
      finrank ℚ ↥(span ℚ (Set.range y) ⊓ OmAV d₀ d₁ B M) := by
    rw [← hper]; rfl
  have e2 : (gmLsgAV d₀ d₁ An M).d₂ = ∑ k, (B k).g + r := rfl
  have e3 : (gmLsgAV d₀ d₁ An M).d₁ = d₁ := rfl
  rw [e1, e2, e3, finrank_TanAV] at hineq
  convert hineq using 3
  push_cast; ring

end LSG.W88
