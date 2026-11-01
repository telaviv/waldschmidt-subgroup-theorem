/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVar5dCore
import LSG.W88.K5dTrans

/-!
# A5.9c: Theorem 4.1 for a subgroup `H′ = H₀ × T_U × B′`, in the coordinates of `G` (`STAGE_A5.md` §6.6 (a)1)

**`trans41B`**: `Trans41B An H′` from `Thm41SubAtB An k₀ k₁ H′.t` (Theorem 4.1 for `G_a^{k₀} × G_m^{k₁} × B′` in the
coordinates `MEB.Tan k₀ k₁ B`, `T_{B′} = t`), `k₀ = dim h₀′`, `k₁ = dim annQ U′`. Copy of `K5d.trans41`: transport
along `ι : (a, c, z) ↦ (A a, C c, z)`, `A` a `ℚ̄`-frame of `h₀′`, `C` a `ℚ`-frame of `annQ U′`; the block part is the
identity. `ι` preserves `LamB`, `Ω = span_ℚ Per` (`map_OmB`) and toric injectivity.
-/

open Complex Module LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.MEB (AbBlock perAb IsRatSub tanOf)
open K5d (cmK algVec_cmK_mulVec algVec_cm_mulVec exp_cm_mulVec mulVec_left_invK exists_algFrame
  finrank_map_inj finrank_prodSub torusLie_eq_annC castL_mem_torusLie_iff finrank_torusLie)

variable {m : ℕ} {B : Fin m → AbBlock}

/-- The tangent space `ℂ^{k₀} × ℂ^{k₁} × t` of `G_a^{k₀} × G_m^{k₁} × B′`. -/
def tanBB (k0 k1 : ℕ) (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : Submodule ℂ (MEB.Tan k0 k1 B) :=
  (⊤ : Submodule ℂ (Fin k0 → ℂ)).prod ((⊤ : Submodule ℂ (Fin k1 → ℂ)).prod t)

/-- `δ = codim` of `H` inside `G_a^{k₀} × G_m^{k₁} × B′`. -/
def SubgroupDataB.δBt {k0 k1 : ℕ} (H : SubgroupDataB k0 k1 B) (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) :
    ℕ := H.δ0 + H.δ1 + (finrank ℂ t - finrank ℂ H.t)

/-- **W88 Theorem 4.1 for `G_a^{k₀} × G_m^{k₁} × B′`** (`T_{B′} = t`), under (NR) unless `t = 0`, and toric
injectivity. -/
def Thm41SubAtB (An : ∀ k, AbBlockAn (B k)) (k0 k1 : ℕ) (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : Prop :=
  ∀ (V W : Submodule ℂ (MEB.Tan k0 k1 B)) (Y : AddSubgroup (MEB.Tan k0 k1 B)),
    V ≤ tanBB k0 k1 t → finrank ℂ V < k0 + k1 + finrank ℂ t → W ≤ V → RationalOverQbarB W →
    Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamB k0 k1 An) → TorInjB V →
    (k1 + 2 * k0 + rk (Y ⊓ MEB.Per k0 k1 B) ≤ 2 * finrank ℂ V ∨ t = ⊥) →
    ∃ H : SubgroupDataB k0 k1 B, H.t ≤ t ∧ H.δBt t ≠ 0 ∧
      finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) < H.δBt t ∧
      (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ MEB.Per k0 k1 B)) + H.δ1 +
          2 * (finrank ℂ t - finrank ℂ H.t) : ℕ) : ℤ) *
          ((k0 + k1 + finrank ℂ t : ℕ) - finrank ℂ V : ℤ) ≤
        ((H.δBt t : ℤ) - (finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ)) *
          ((k1 + 2 * finrank ℂ t : ℕ) - rk (Y ⊓ MEB.Per k0 k1 B) : ℤ))

/-! ### Periods in toric/abelian form -/

variable {d₀ d₁ : ℕ}

lemma inAb_mem_OmB {z : ∀ k, Fin (B k).g → ℂ} (hz : z ∈ Submodule.span ℚ (perAb B : Set _)) :
    inAb d₀ d₁ B z ∈ OmB d₀ d₁ B := by
  have hmap : (Submodule.span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ))).map (inAb d₀ d₁ B) ≤
      OmB d₀ d₁ B := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨rfl, fun j => ⟨0, by simp [inAb_apply]⟩, fun k => hy k (Set.mem_univ k)⟩
  exact hmap ⟨z, hz, rfl⟩

lemma mem_OmB {x : MEB.Tan d₀ d₁ B} (hx : x ∈ OmB d₀ d₁ B) :
    ∃ (c : Fin d₁ → ℚ) (z : ∀ k, Fin (B k).g → ℂ), z ∈ Submodule.span ℚ (perAb B : Set _) ∧
      x = inTB d₀ d₁ B c + inAb d₀ d₁ B z := by
  induction hx using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨hp1, hp2, hp3⟩ := hp
    choose n hn using hp2
    refine ⟨fun i => (n i : ℚ), p.2.2, Submodule.subset_span fun k _ => hp3 k, ?_⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [inTB_apply, inAb_apply, hp1]
    · funext j
      simp [inTB_apply, inAb_apply, K11.castL, hn j]
    · simp [inTB_apply, inAb_apply]
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, z, hz, rfl⟩ := hx
    obtain ⟨b, w, hw, rfl⟩ := hy
    exact ⟨a + b, z + w, Submodule.add_mem _ hz hw, by rw [map_add, map_add]; abel⟩
  | smul r x _ hx =>
    obtain ⟨a, z, hz, rfl⟩ := hx
    exact ⟨r • a, r • z, Submodule.smul_mem _ _ hz, by rw [map_smul, map_smul, smul_add]⟩

/-! ### The transport maps -/

variable {k0 k1 : ℕ}

/-- `ι : (a, c, z) ↦ (A a, C c, z)`. -/
def iotaB (A : Matrix (Fin d₀) (Fin k0) K11.Kq) (C : Matrix (Fin d₁) (Fin k1) ℚ) :
    MEB.Tan k0 k1 B →ₗ[ℂ] MEB.Tan d₀ d₁ B :=
  ((cmK K11.Kq A).mulVecLin.comp (LinearMap.fst ℂ _ _)).prod
    (((K11.cm C).mulVecLin.comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))).prod
      ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)))

/-- `π : (u, v, z) ↦ (B u, D v, z)`. -/
def piB (Bm : Matrix (Fin k0) (Fin d₀) K11.Kq) (D : Matrix (Fin k1) (Fin d₁) ℚ) :
    MEB.Tan d₀ d₁ B →ₗ[ℂ] MEB.Tan k0 k1 B :=
  ((cmK K11.Kq Bm).mulVecLin.comp (LinearMap.fst ℂ _ _)).prod
    (((K11.cm D).mulVecLin.comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))).prod
      ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)))

lemma iotaB_apply (A : Matrix (Fin d₀) (Fin k0) K11.Kq) (C : Matrix (Fin d₁) (Fin k1) ℚ)
    (x : MEB.Tan k0 k1 B) :
    iotaB A C x = ((cmK K11.Kq A).mulVec x.1, (K11.cm C).mulVec x.2.1, x.2.2) := rfl

lemma piB_apply (Bm : Matrix (Fin k0) (Fin d₀) K11.Kq) (D : Matrix (Fin k1) (Fin d₁) ℚ)
    (x : MEB.Tan d₀ d₁ B) :
    piB Bm D x = ((cmK K11.Kq Bm).mulVec x.1, (K11.cm D).mulVec x.2.1, x.2.2) := rfl

lemma iotaB_inT_add_inAb (A : Matrix (Fin d₀) (Fin k0) K11.Kq) (C : Matrix (Fin d₁) (Fin k1) ℚ)
    (c : Fin k1 → ℚ) (z : ∀ k, Fin (B k).g → ℂ) :
    iotaB A C (inTB k0 k1 B c + inAb k0 k1 B z) = inTB d₀ d₁ B (C.mulVec c) + inAb d₀ d₁ B z := by
  rw [iotaB_apply, inTB_apply, inTB_apply, inAb_apply, inAb_apply]
  refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
  simp only [Prod.snd_add, Prod.fst_add, add_zero, Matrix.mulVec_smul, K11.cm_mulVec_castL]

set_option maxHeartbeats 1600000 in
-- the transport of all the data
/-- **Theorem 4.1 for `G′ = H′` in the coordinates of `G`.** -/
theorem trans41B (An : ∀ k, AbBlockAn (B k)) (H' : SubgroupDataB d₀ d₁ B)
    (h41 : Thm41SubAtB An (finrank ℂ H'.h0) (finrank ℚ (K11.annQ H'.U)) H'.t) : Trans41B An H' := by
  classical
  intro V W Y hVT hVdim hWV hWrat hYfg hY hTor hNR
  set k0 := finrank ℂ H'.h0 with hk0
  set k1 := finrank ℚ (K11.annQ H'.U) with hk1
  obtain ⟨A, Bm, hBA, hA⟩ := exists_algFrame H'.h0 H'.h0_rat
  obtain ⟨C, D, hDC, hC⟩ := K11.exists_frame (K11.annQ H'.U)
  set ι : MEB.Tan k0 k1 B →ₗ[ℂ] MEB.Tan d₀ d₁ B := iotaB A C with hι
  set π : MEB.Tan d₀ d₁ B →ₗ[ℂ] MEB.Tan k0 k1 B := piB Bm D with hπ
  have htl' : torusLie H'.U = LinearMap.range (K11.cm C).mulVecLin := by
    rw [torusLie_eq_annC, K11.annC_eq_cspan, K11.cspan_eq_range hC]
  have hπι : ∀ x, π (ι x) = x := by
    intro x
    rw [hπ, hι, iotaB_apply, piB_apply, mulVec_left_invK hBA, K11.mulVec_left_inv hDC]
  have hinj : Function.Injective ι := fun x y h => by rw [← hπι x, ← hπι y, h]
  set R : Submodule ℂ (MEB.Tan d₀ d₁ B) := H'.h0.prod ((torusLie H'.U).prod ⊤) with hR
  have hιπ : ∀ v ∈ R, ι (π v) = v := by
    intro v hv
    rw [hR, Submodule.mem_prod, Submodule.mem_prod] at hv
    obtain ⟨h1, h2, -⟩ := hv
    rw [← hA] at h1; rw [htl'] at h2
    obtain ⟨a, ha⟩ := h1; obtain ⟨c, hc⟩ := h2
    rw [hι, hπ, piB_apply, iotaB_apply]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · change (cmK K11.Kq A).mulVec ((cmK K11.Kq Bm).mulVec v.1) = v.1
      rw [← ha]; simp only [Matrix.mulVecLin_apply]; rw [mulVec_left_invK hBA]
    · change (K11.cm C).mulVec ((K11.cm D).mulVec v.2.1) = v.2.1
      rw [← hc]; simp only [Matrix.mulVecLin_apply]; rw [K11.mulVec_left_inv hDC]
  have hrange : LinearMap.range ι = R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hR, Submodule.mem_prod, Submodule.mem_prod, hι, iotaB_apply, ← hA, htl']
      exact ⟨⟨x.1, rfl⟩, ⟨x.2.1, rfl⟩, Submodule.mem_top⟩
    · intro v hv; exact ⟨π v, hιπ v hv⟩
  have hTR : H'.tan ≤ R := by
    intro x hx
    rw [SubgroupDataB.tan, tanOf, Submodule.mem_prod, Submodule.mem_prod] at hx
    rw [hR, Submodule.mem_prod, Submodule.mem_prod]
    exact ⟨hx.1, hx.2.1, Submodule.mem_top⟩
  have hTmap : (tanBB k0 k1 H'.t).map ι = H'.tan := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      simp only [tanBB, SetLike.mem_coe, Submodule.mem_prod] at hx
      have := (hrange ▸ LinearMap.mem_range_self ι x : ι x ∈ R)
      rw [hR, Submodule.mem_prod, Submodule.mem_prod] at this
      rw [SubgroupDataB.tan, tanOf, Submodule.mem_prod, Submodule.mem_prod]
      exact ⟨this.1, this.2.1, hx.2.2⟩
    · intro v hv
      refine ⟨π v, ?_, hιπ v (hTR hv)⟩
      rw [SubgroupDataB.tan, tanOf, Submodule.mem_prod, Submodule.mem_prod] at hv
      change π v ∈ tanBB k0 k1 H'.t
      rw [tanBB, Submodule.mem_prod, Submodule.mem_prod, hπ, piB_apply]
      exact ⟨Submodule.mem_top, Submodule.mem_top, hv.2.2⟩
  have hfT : finrank ℂ H'.tan = k0 + k1 + finrank ℂ H'.t := by
    rw [← hTmap, finrank_map_inj hinj, tanBB, finrank_prodSub, finrank_prodSub]
    simp [add_assoc]
  have htor' : finrank ℂ (torusLie H'.U) = k1 := by
    have h1 := K11.finrank_annQ H'.U
    have h2 := finrank_torusLie H'.U
    omega
  have hmap : ∀ S : Submodule ℂ (MEB.Tan d₀ d₁ B), S ≤ R → (S.comap ι).map ι = S := by
    intro S hS; rw [Submodule.map_comap_eq, hrange, inf_eq_right.mpr hS]
  set Vs := V.comap ι with hVs_def
  set Ws := W.comap ι with hWs_def
  set Ys := Y.map π.toAddMonoidHom with hYs_def
  have hVR : V ≤ R := hVT.trans hTR
  have hWR : W ≤ R := hWV.trans hVR
  have hVs : finrank ℂ Vs = finrank ℂ V := by rw [← finrank_map_inj hinj, hmap V hVR]
  have hWs : finrank ℂ Ws = finrank ℂ W := by rw [← finrank_map_inj hinj, hmap W hWR]
  have hVsT : Vs ≤ tanBB k0 k1 H'.t := by
    intro x hx
    have h := hVT (show ι x ∈ V from hx)
    rw [SubgroupDataB.tan, tanOf, Submodule.mem_prod, Submodule.mem_prod] at h
    rw [tanBB, Submodule.mem_prod, Submodule.mem_prod]
    exact ⟨Submodule.mem_top, Submodule.mem_top, h.2.2⟩
  have hWsrat : RationalOverQbarB Ws := by
    set S := {w | w ∈ W ∧ AlgTanB w} with hS
    have hWs_eq : Ws = W.map π := by
      ext x; constructor
      · intro hx; exact ⟨ι x, hx, hπι x⟩
      · rintro ⟨w, hw, rfl⟩
        change ι (π w) ∈ W
        rw [hιπ w (hWR hw)]; exact hw
    have hWs_span : Ws = Submodule.span ℂ (π '' S) := by
      rw [hWs_eq]; conv_lhs => rw [hWrat]
      rw [Submodule.map_span]
    refine le_antisymm (hWs_span.le.trans (Submodule.span_mono ?_)) ?_
    · rintro _ ⟨s, hs, rfl⟩
      refine ⟨by rw [hWs_eq]; exact ⟨s, hs.1, rfl⟩, ?_, ?_, ?_⟩
      · rw [hπ, piB_apply]; exact algVec_cmK_mulVec Bm hs.2.1
      · rw [hπ, piB_apply]; exact algVec_cm_mulVec D hs.2.2.1
      · rw [hπ, piB_apply]; exact hs.2.2.2
    · rw [Submodule.span_le]; exact fun x hx => hx.1
  have hYsfg : Ys.FG := K11.fg_map_addSubgroup hYfg _
  have hYsmem : ∀ x ∈ Ys, x ∈ Vs ∧ x ∈ LamB k0 k1 An := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyV, hyL⟩ := hY y hy
    refine ⟨?_, ?_⟩
    · change ι (π y) ∈ V
      rw [hιπ y (hVR hyV)]; exact hyV
    · change π y ∈ LamB k0 k1 An
      rw [hπ, piB_apply]
      exact ⟨algVec_cmK_mulVec Bm hyL.1, exp_cm_mulVec D hyL.2.1, hyL.2.2⟩
  -- the `ℚ`-structures
  set ιq := ι.restrictScalars ℚ with hιq
  have hinjq : Function.Injective ιq := hinj
  set Yq := Submodule.span ℚ (Y : Set (MEB.Tan d₀ d₁ B)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  have hYR : Yq ≤ R.restrictScalars ℚ := Submodule.span_le.mpr fun y hy => hVR (hY y hy).1
  have hYmap : (Submodule.span ℚ (Ys : Set (MEB.Tan k0 k1 B))).map ιq = Yq := by
    rw [Submodule.map_span]; congr 1
    ext v; constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      change ι (π y) ∈ Y
      rw [hιπ y (hVR (hY y hy).1)]; exact hy
    · intro hv; exact ⟨π v, ⟨v, hv, rfl⟩, hιπ v (hVR (hY v hv).1)⟩
  have hPmap : (OmB k0 k1 B).map ιq = OmB d₀ d₁ B ⊓ R.restrictScalars ℚ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨c, z, hz, rfl⟩ := mem_OmB hx
        change ι _ ∈ _
        rw [hι, iotaB_inT_add_inAb]
        exact Submodule.add_mem _ (inTB_mem_span_Per _) (inAb_mem_OmB hz)
      · change ι x ∈ R; rw [← hrange]; exact LinearMap.mem_range_self ι x
    · rintro x ⟨hxΩ, hxR⟩
      obtain ⟨q, z, hz, rfl⟩ := mem_OmB hxΩ
      have hq : q ∈ K11.annQ H'.U := by
        have h := hxR
        change inTB d₀ d₁ B q + inAb d₀ d₁ B z ∈ R at h
        rw [hR, Submodule.mem_prod, Submodule.mem_prod] at h
        have h2 := h.2.1
        simp only [inTB_apply, inAb_apply, Prod.snd_add, Prod.fst_add, add_zero] at h2
        exact castL_mem_torusLie_iff.mp h2
      rw [← hC] at hq
      obtain ⟨c, rfl⟩ := hq
      refine ⟨inTB k0 k1 B c + inAb k0 k1 B z, Submodule.add_mem _ (inTB_mem_span_Per c)
        (inAb_mem_OmB hz), ?_⟩
      change ι _ = _
      rw [hι, iotaB_inT_add_inAb]
      rfl
  have rk1 : rk Ys = finrank ℚ Yq := by rw [rk, ← finrank_map_inj hinjq, hYmap]
  have rk2 : rk (Ys ⊓ MEB.Per k0 k1 B) = finrank ℚ ↥(Yq ⊓ OmB d₀ d₁ B) := by
    rw [rk, K11.span_inf_addSubgroup, ← finrank_map_inj hinjq, Submodule.map_inf _ hinjq,
      hYmap, hPmap, inf_comm (OmB d₀ d₁ B), ← inf_assoc, inf_eq_left.mpr hYR]
  -- toric injectivity of `Vs`
  have hTors : TorInjB Vs := by
    intro v hv hvP hv1
    have h1 : ι v ∈ OmB d₀ d₁ B := (hPmap.le ⟨v, hvP, rfl⟩).1
    have h2 : (ι v).2.1 = 0 := by rw [hι, iotaB_apply]; simp [hv1]
    exact hinj (by rw [hTor (ι v) hv h1 h2, map_zero])
  -- the small theorem
  obtain ⟨Hs, hHst, -, hτs, hineqs⟩ := h41 Vs Ws Ys hVsT (by rw [hVs]; omega)
    (Submodule.comap_mono hWV) hWsrat hYsfg hYsmem hTors (by
      rcases hNR with h | h
      · left; rw [rk2, hVs]; rw [htor'] at h; omega
      · exact Or.inr h)
  -- the subgroup `G''`
  have hh0rat : RationalOverQbar (Hs.h0.map (cmK K11.Kq A).mulVecLin) := by
    set S := {w | w ∈ Hs.h0 ∧ AlgVec w} with hS
    refine le_antisymm ?_ (Submodule.span_le.mpr fun x hx => hx.1)
    conv_lhs => rw [Hs.h0_rat]
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw.1, rfl⟩, algVec_cmK_mulVec A hw.2⟩
  let H'' : SubgroupDataB d₀ d₁ B :=
    { h0 := Hs.h0.map (cmK K11.Kq A).mulVecLin
      U := K11.annQ ((K11.annQ Hs.U).map C.mulVecLin)
      t := Hs.t
      h0_rat := hh0rat
      t_rat := Hs.t_rat }
  have htl'' : (torusLie Hs.U).map (K11.cm C).mulVecLin = torusLie H''.U := by
    rw [torusLie_eq_annC, K11.annC_eq_cspan, K11.map_cspan, torusLie_eq_annC,
      ← K11.cspan_eq_annC]
  have hTan : Hs.tan.map ι = H''.tan := by
    ext ⟨u, v, z⟩
    rw [Submodule.mem_map]
    simp only [H'', SubgroupDataB.tan, tanOf, Submodule.mem_prod]
    rw [← htl'']
    constructor
    · rintro ⟨⟨a, c, w⟩, ⟨ha, hc, hw⟩, hx⟩
      rw [hι, iotaB_apply] at hx
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := ⟨congrArg Prod.fst hx,
        congrArg (fun p => p.2.1) hx, congrArg (fun p => p.2.2) hx⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨c, hc, rfl⟩, hw⟩
    · rintro ⟨⟨a, ha, rfl⟩, ⟨c, hc, rfl⟩, hz⟩
      exact ⟨(a, c, z), ⟨ha, hc, hz⟩, rfl⟩
  have hT''T : H''.tan ≤ H'.tan := by
    rw [← hTan, ← hTmap]
    refine Submodule.map_mono ?_
    intro x hx
    rw [SubgroupDataB.tan, tanOf, Submodule.mem_prod, Submodule.mem_prod] at hx
    rw [tanBB, Submodule.mem_prod, Submodule.mem_prod]
    exact ⟨Submodule.mem_top, Submodule.mem_top, hHst hx.2.2⟩
  have hWinf : finrank ℂ ↥(Ws ⊓ Hs.tan) = finrank ℂ ↥(W ⊓ H''.tan) := by
    rw [← finrank_map_inj hinj, Submodule.map_inf _ hinj, hmap W hWR, hTan]
  have hfT'' : finrank ℂ H''.tan = finrank ℂ Hs.tan := by rw [← hTan, finrank_map_inj hinj]
  have htorS : finrank ℂ (torusLie H''.U) = finrank ℂ (torusLie Hs.U) := by
    rw [← htl'', finrank_map_inj (K11.cm_injective hDC)]
  have hTq : (Submodule.span ℚ ((Hs.tan.toAddSubgroup : AddSubgroup (MEB.Tan k0 k1 B)) :
      Set (MEB.Tan k0 k1 B))).map ιq = H''.tan.restrictScalars ℚ := by
    rw [K11.span_submodule_coe, ← hTan]; rfl
  have rk3 : rk (Ys ⊓ (Hs.tan.toAddSubgroup ⊔ MEB.Per k0 k1 B)) =
      finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmB d₀ d₁ B)) := by
    rw [rk, K11.span_inf_addSubgroup, K11.span_sup_addSubgroup, ← finrank_map_inj hinjq,
      Submodule.map_inf _ hinjq, Submodule.map_sup, hYmap, hTq, hPmap]
    have hT''q : H''.tan.restrictScalars ℚ ≤ R.restrictScalars ℚ := fun x hx => hTR (hT''T hx)
    have : Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmB d₀ d₁ B ⊓ R.restrictScalars ℚ) =
        Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmB d₀ d₁ B) := by
      rw [← sup_inf_assoc_of_le _ hT''q, inf_comm _ (R.restrictScalars ℚ), ← inf_assoc,
        inf_eq_left.mpr hYR]
    rw [this]
  -- numerics
  have hle1 : finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmB d₀ d₁ B)) ≤ finrank ℚ Yq :=
    Submodule.finrank_mono inf_le_left
  have hle2 : finrank ℂ ↥(W ⊓ H''.tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
  have hfTs := finrank_tanB Hs
  have hftorS := finrank_torusLie Hs.U
  have hHst' : finrank ℂ Hs.t ≤ finrank ℂ H'.t := Submodule.finrank_mono hHst
  have hh0s : finrank ℂ Hs.h0 ≤ k0 := (Submodule.finrank_le _).trans (by simp)
  have hδ : (Hs.δBt H'.t : ℤ) = (finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan := by
    simp only [SubgroupDataB.δBt, SubgroupDataB.δ0, SubgroupDataB.δ1]
    rw [hfT'', hfTs, hfT]
    push_cast [Nat.cast_sub hHst', Nat.cast_sub hh0s]
    have : (finrank ℚ Hs.U : ℤ) = k1 - finrank ℂ (torusLie Hs.U) := by omega
    linarith
  have hδ12 : ((Hs.δ1 + 2 * (finrank ℂ H'.t - finrank ℂ Hs.t) : ℕ) : ℤ) =
      (nPB H' : ℤ) - nPB H'' := by
    simp only [SubgroupDataB.δ1, nPB, htorS, htor']
    push_cast [Nat.cast_sub hHst']
    have : (finrank ℚ Hs.U : ℤ) = k1 - finrank ℂ (torusLie Hs.U) := by omega
    simp only [H'']
    linarith
  refine ⟨H'', hT''T, ?_, ?_⟩
  · rw [hWs, hWinf] at hτs
    have := (Nat.cast_lt (α := ℤ)).mpr hτs
    rw [Nat.cast_sub hle2, hδ] at this
    exact this
  · rw [rk1, rk3, rk2, hVs, hWs, hWinf] at hineqs
    have e1 : ((finrank ℚ Yq - finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmB d₀ d₁ B)) +
        Hs.δ1 + 2 * (finrank ℂ H'.t - finrank ℂ Hs.t) : ℕ) : ℤ) = (finrank ℚ Yq : ℤ) -
          finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmB d₀ d₁ B)) +
          ((nPB H' : ℤ) - nPB H'') := by
      rw [← hδ12]; push_cast [Nat.cast_sub hle1]; ring
    have e2 : (((k0 + k1 + finrank ℂ H'.t : ℕ) : ℤ) - finrank ℂ V) = 1 := by
      rw [hfT] at hVdim; omega
    have e3 : ((Hs.δBt H'.t : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H''.tan) : ℕ) : ℤ)) =
        ((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
          ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan)) := by
      rw [hδ, Nat.cast_sub hle2]
    have e4 : (((k1 + 2 * finrank ℂ H'.t : ℕ) : ℤ) - finrank ℚ ↥(Yq ⊓ OmB d₀ d₁ B)) =
        (nPB H' : ℤ) - finrank ℚ ↥(Yq ⊓ OmB d₀ d₁ B) := by
      simp only [nPB, htor']
    rw [e1, e2, e3, e4, mul_one] at hineqs
    exact hineqs

end LSG.W88
