/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarV5dPiv
import LSG.W88.AbVar5dRoy

/-!
# M2.7d: Theorem 4.1 for a member with `t = 0` (Roy), through the abelian engine

A member `H′` with `t′ = 0` is linear: `T_{H′} = Γ ⊕ U^⊥` with `Γ ⊂ ℂ^{d₀} × ℂ^r`. It lies in the image of the linear
embedding

  `j : MEB.Tan (d₀ + r) d₁ B₀ → TanAV d₀ d₁ r B`, `(a′, b, ·) ↦ (a′|_{d₀}, b, 0, a′|_r)`

(`B₀` the empty `AbBlock` family), which matches logarithms (`z = 0` makes `sPart = s`), periods (toric only) and
toric injectivity. **`trans41AV_bot`**: `Trans41AV An H′` from the abelian `trans41B` for the member
`H₀ = (Γ flattened) × T_U` of `G_a^{d₀+r} × G_m^{d₁}` with `thm41SubAtB_bot` (Roy's Theorem 1, no (NR)). Bookkeeping:
`nPAV − nPB = 2 d₂(H)` (`d₂(H) = dim (Γ ∩ fibre)`), and `2 (d₂(H′) − d₂(H″)) ≤ 2 (δ − τ) d₂(H′)` since `δ − τ ≥ 1`.
-/

open Complex Module Submodule LSG.AuxAV LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.W88.AVS

open LSG.MEB (IsRatSub perAb AbBlock tanOf)
open LSG.MEBV (VBlock perTanId perBase)
open LSG.W88.Vec (RatPair AlgPair AlgMat)
open K5d (finrank_map_inj)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {M : Matrix (Fin r) (Fin m) ℂ}

/-- The empty abelian family. -/
def B₀ : Fin 0 → AbBlock := fun k => k.elim0

/-- Its (empty) analytic packages. -/
def An₀ : ∀ k, AbBlockAn (B₀ k) := fun k => k.elim0

/-! ### Flattening `ℂ^{d₀} × ℂ^r ≅ ℂ^{d₀+r}` -/

/-- `(a, s) ↦ a ++ s`. -/
def flatL (d₀ r : ℕ) : ((Fin d₀ → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] (Fin (d₀ + r) → ℂ) where
  toFun x := Fin.append x.1 x.2
  map_add' x y := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' c x := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- `v ↦ (v|_{d₀}, v|_r)`. -/
def unflatL (d₀ r : ℕ) : (Fin (d₀ + r) → ℂ) →ₗ[ℂ] ((Fin d₀ → ℂ) × (Fin r → ℂ)) where
  toFun v := (fun i => v (Fin.castAdd r i), fun i => v (Fin.natAdd d₀ i))
  map_add' x y := rfl
  map_smul' c x := rfl

lemma unflat_flat (x : (Fin d₀ → ℂ) × (Fin r → ℂ)) : unflatL d₀ r (flatL d₀ r x) = x := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [flatL, unflatL]

lemma flat_unflat (v : Fin (d₀ + r) → ℂ) : flatL d₀ r (unflatL d₀ r v) = v := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [flatL, unflatL]

lemma algVec_flat {x : (Fin d₀ → ℂ) × (Fin r → ℂ)} (hx : AlgPair x) : AlgVec (flatL d₀ r x) := by
  intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [flatL] using hx.1 j
  · simpa [flatL] using hx.2 j

lemma algPair_unflat {v : Fin (d₀ + r) → ℂ} (hv : AlgVec v) : AlgPair (unflatL d₀ r v) :=
  ⟨fun i => hv _, fun i => hv _⟩

/-! ### The embedding `j` and its left inverse `q` -/

variable (d₀ d₁ r B) in
/-- `j (a′, b, ·) = (a′|_{d₀}, b, 0, a′|_r)`. -/
def jEmb : MEB.Tan (d₀ + r) d₁ B₀ →ₗ[ℂ] TanAV d₀ d₁ r B where
  toFun x := ((unflatL d₀ r x.1).1, x.2.1, 0, (unflatL d₀ r x.1).2)
  map_add' x y := by ext <;> simp [unflatL]
  map_smul' c x := by ext <;> simp [unflatL]

variable (d₀ d₁ r B) in
/-- `q (a, b, z, s) = (a ++ s, b, ·)`. -/
def qEmb : TanAV d₀ d₁ r B →ₗ[ℂ] MEB.Tan (d₀ + r) d₁ B₀ where
  toFun x := (flatL d₀ r (x.1, x.2.2.2), x.2.1, 0)
  map_add' x y := by
    refine Prod.ext ?_ (Prod.ext rfl (Subsingleton.elim _ _))
    change flatL d₀ r ((x.1, x.2.2.2) + (y.1, y.2.2.2)) = _
    rw [map_add]; rfl
  map_smul' c x := by
    refine Prod.ext ?_ (Prod.ext rfl (Subsingleton.elim _ _))
    change flatL d₀ r (c • (x.1, x.2.2.2)) = _
    rw [map_smul]; rfl

lemma qj (x : MEB.Tan (d₀ + r) d₁ B₀) : qEmb d₀ d₁ r B (jEmb d₀ d₁ r B x) = x := by
  refine Prod.ext ?_ (Prod.ext rfl (Subsingleton.elim _ _))
  change flatL d₀ r ((unflatL d₀ r x.1).1, (unflatL d₀ r x.1).2) = x.1
  exact flat_unflat x.1

lemma jq {x : TanAV d₀ d₁ r B} (hx : x.2.2.1 = 0) : jEmb d₀ d₁ r B (qEmb d₀ d₁ r B x) = x := by
  have h := unflat_flat (d₀ := d₀) (r := r) (x.1, x.2.2.2)
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext hx.symm ?_))
  · change (unflatL d₀ r (flatL d₀ r (x.1, x.2.2.2))).1 = x.1
    rw [h]
  · change (unflatL d₀ r (flatL d₀ r (x.1, x.2.2.2))).2 = x.2.2.2
    rw [h]

lemma jEmb_injective : Function.Injective (jEmb d₀ d₁ r B) := fun x y h => by
  rw [← qj x, ← qj y, h]

/-! ### Members with `t = 0` -/

lemma tan_eq_of_bot (H : SubgroupDataAV d₀ d₁ B M) (ht : H.t = ⊥) :
    H.tan = H.gam.map vecInclA ⊔ (torusLie H.U).map torInclA := by
  simp only [SubgroupDataAV.tan, ht, perTanA_bot', Submodule.map_bot, sup_bot_eq]

lemma map_jEmb_tanOf (h0 : Submodule ℂ (Fin (d₀ + r) → ℂ)) (U : Submodule ℚ (Fin d₁ → ℚ)) :
    (tanOf h0 U ⊥).map (jEmb d₀ d₁ r B) =
      (h0.map (unflatL d₀ r)).map vecInclA ⊔ (torusLie U).map torInclA := by
  apply le_antisymm
  · rintro _ ⟨y, ⟨hy0, hyU, -⟩, rfl⟩
    have e : jEmb d₀ d₁ r B y = vecInclA (unflatL d₀ r y.1) + torInclA y.2.1 := by
      ext <;> simp [jEmb, vecInclA, torInclA]
    rw [e]
    exact add_mem (mem_sup_left ⟨_, ⟨y.1, hy0, rfl⟩, rfl⟩) (mem_sup_right ⟨y.2.1, hyU, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨(v, 0, 0), ⟨hv, (torusLie U).zero_mem, (mem_bot ℂ).mpr (Subsingleton.elim _ _)⟩, ?_⟩
      ext <;> simp [jEmb, vecInclA]
    · rintro _ ⟨b, hb, rfl⟩
      refine ⟨(0, b, 0), ⟨zero_mem _, hb, (mem_bot ℂ).mpr (Subsingleton.elim _ _)⟩, ?_⟩
      ext <;> simp [jEmb, torInclA, unflatL]

lemma ratPair_map_unflat {h0 : Submodule ℂ (Fin (d₀ + r) → ℂ)} (h : RationalOverQbar h0) :
    RatPair (h0.map (unflatL d₀ r)) := by
  refine le_antisymm ?_ (span_le.mpr fun x hx => hx.1)
  conv_lhs => rw [h]
  rw [map_span]
  refine span_mono ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw.1, rfl⟩, algPair_unflat hw.2⟩

lemma rational_map_flat {Γ : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ))} (h : RatPair Γ) :
    RationalOverQbar (Γ.map (flatL d₀ r)) := by
  refine le_antisymm ?_ (span_le.mpr fun x hx => hx.1)
  conv_lhs => rw [h]
  rw [map_span]
  refine span_mono ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw.1, rfl⟩, algVec_flat hw.2⟩

lemma map_unflat_map_flat (Γ : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ))) :
    (Γ.map (flatL d₀ r)).map (unflatL d₀ r) = Γ := by
  rw [← Submodule.map_comp]
  have : (unflatL d₀ r).comp (flatL d₀ r) = LinearMap.id := LinearMap.ext fun x => unflat_flat x
  rw [this, Submodule.map_id]

set_option maxHeartbeats 3200000 in
-- the transport along `j`
/-- **Theorem 4.1 for a member with `t = 0`** (Roy), in the coordinates of `G`. -/
theorem trans41AV_bot (An : ∀ k, VBlockAn (B k)) (H' : SubgroupDataAV d₀ d₁ B M) (ht : H'.t = ⊥) :
    Trans41AV An H' := by
  classical
  intro V W Y hVT hVdim hWV hWrat hYfg hY hTor _
  set j := jEmb d₀ d₁ r B with hj
  set q := qEmb d₀ d₁ r B with hq
  let H₀ : SubgroupDataB (d₀ + r) d₁ B₀ :=
    { h0 := H'.gam.map (flatL d₀ r), U := H'.U, t := ⊥, h0_rat := rational_map_flat H'.gam_rat,
      t_rat := isRatSub_botB }
  have hT0 : H₀.tan.map j = H'.tan := by
    rw [tan_eq_of_bot H' ht]
    change (tanOf (H'.gam.map (flatL d₀ r)) H'.U ⊥).map j = _
    rw [map_jEmb_tanOf, map_unflat_map_flat]
  have hTz : ∀ x ∈ H'.tan, x.2.2.1 = 0 := fun x hx => by
    have := mem_tan_z hx; rw [ht] at this; exact (mem_bot ℂ).mp this
  have hjq : ∀ x ∈ H'.tan, j (q x) = x := fun x hx => jq (hTz x hx)
  have hmap : ∀ S : Submodule ℂ (TanAV d₀ d₁ r B), S ≤ H'.tan → (S.comap j).map j = S := by
    intro S hS
    rw [Submodule.map_comap_eq]
    refine inf_eq_right.mpr (hS.trans ?_)
    rw [← hT0]; exact LinearMap.map_le_range
  have hWR : W ≤ H'.tan := hWV.trans hVT
  set Vs := V.comap j with hVs_def
  set Ws := W.comap j with hWs_def
  set Ys := Y.map q.toAddMonoidHom with hYs_def
  have hVs : finrank ℂ Vs = finrank ℂ V := by rw [← finrank_map_inj jEmb_injective, hmap V hVT]
  have hWs : finrank ℂ Ws = finrank ℂ W := by rw [← finrank_map_inj jEmb_injective, hmap W hWR]
  have hfT0 : finrank ℂ H₀.tan = finrank ℂ H'.tan := by rw [← hT0, finrank_map_inj jEmb_injective]
  have hVsT : Vs ≤ H₀.tan := by
    intro x hx
    have h := hVT (show j x ∈ V from hx)
    rw [← hT0] at h
    obtain ⟨y, hy, hyx⟩ := h
    rw [← jEmb_injective hyx]; exact hy
  have hWsrat : RationalOverQbarB Ws := by
    have hWs_eq : Ws = W.map q := by
      ext x; constructor
      · intro hx; exact ⟨j x, hx, qj x⟩
      · rintro ⟨w, hw, rfl⟩
        change j (q w) ∈ W
        rw [hjq w (hWR hw)]; exact hw
    have hWs_span : Ws = span ℂ (q '' {w | w ∈ W ∧ AlgTanAV w}) := by
      rw [hWs_eq]; conv_lhs => rw [hWrat]
      rw [map_span]
    refine le_antisymm (hWs_span.le.trans (span_mono ?_)) (span_le.mpr fun x hx => hx.1)
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨by rw [hWs_eq]; exact ⟨s, hs.1, rfl⟩, ?_, hs.2.2.1, fun k => k.elim0⟩
    exact algVec_flat ⟨hs.2.1, hs.2.2.2.2⟩
  have hYsfg : Ys.FG := K11.fg_map_addSubgroup hYfg _
  have hYsmem : ∀ x ∈ Ys, x ∈ Vs ∧ x ∈ LamB (d₀ + r) d₁ An₀ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyV, hyL⟩ := hY y hy
    have hyz := hTz y (hVT hyV)
    refine ⟨?_, ?_, hyL.2.1, fun k => k.elim0⟩
    · change j (q y) ∈ V
      rw [hjq y (hVT hyV)]; exact hyV
    · have hs : sPart M y = y.2.2.2 := by
        unfold sPart; rw [hyz, etaB_zero', Matrix.mulVec_zero, sub_zero]
      exact algVec_flat ⟨hyL.1, hs ▸ hyL.2.2.2⟩
  -- the `ℚ`-structures
  set jq' := j.restrictScalars ℚ with hjq'
  have hinjq : Function.Injective jq' := jEmb_injective
  set Yq := span ℚ (Y : Set (TanAV d₀ d₁ r B)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  have hYR : Yq ≤ H'.tan.restrictScalars ℚ := span_le.mpr fun y hy => hVT (hY y hy).1
  have hYmap : (span ℚ (Ys : Set (MEB.Tan (d₀ + r) d₁ B₀))).map jq' = Yq := by
    rw [map_span]; congr 1
    ext v; constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      change j (q y) ∈ Y
      rw [hjq y (hVT (hY y hy).1)]; exact hy
    · intro hv; exact ⟨q v, ⟨v, hv, rfl⟩, hjq v (hVT (hY v hv).1)⟩
  set R := LinearMap.range j with hR
  have hTR : H'.tan ≤ R := by rw [← hT0]; exact LinearMap.map_le_range
  have hYR' : Yq ≤ R.restrictScalars ℚ := hYR.trans hTR
  have hPmap : (OmB (d₀ + r) d₁ B₀).map jq' = OmAV d₀ d₁ B M ⊓ R.restrictScalars ℚ := by
    apply le_antisymm
    · rw [map_span, span_le]
      rintro _ ⟨p, hp, rfl⟩
      refine ⟨subset_span ⟨?_, hp.2.1, fun k => (B k).base.per.zero_mem, ?_⟩, ⟨p, rfl⟩⟩
      · change (unflatL d₀ r p.1).1 = 0
        rw [hp.1]; rfl
      · change (unflatL d₀ r p.1).2 = M.mulVec (etaB B 0)
        rw [hp.1, etaB_zero', Matrix.mulVec_zero]; rfl
    · rintro x ⟨hxΩ, ⟨y, hyx⟩⟩
      have hxz : x.2.2.1 = 0 := by rw [← hyx]; rfl
      obtain ⟨N, hN, hNx⟩ := exists_nsmul_of_mem_span hxΩ
      have hqN : q (N • x) ∈ MEB.Per (d₀ + r) d₁ B₀ := by
        have hNz : (N • x).2.2.1 = 0 := by
          change N • x.2.2.1 = 0; rw [hxz, smul_zero]
        have hNs : (N • x).2.2.2 = 0 := by rw [hNx.2.2.2, hNz, etaB_zero', Matrix.mulVec_zero]
        refine ⟨?_, hNx.2.1, fun k => k.elim0⟩
        change flatL d₀ r ((N • x).1, (N • x).2.2.2) = 0
        rw [hNx.1, hNs]; exact (flatL d₀ r).map_zero
      have hqx : q x ∈ OmB (d₀ + r) d₁ B₀ := by
        refine mem_span_rat_of_nsmul hN ?_
        rw [← map_nsmul]; exact subset_span hqN
      exact ⟨q x, hqx, jq hxz⟩
  have rk1 : finrank ℚ (span ℚ (Ys : Set (MEB.Tan (d₀ + r) d₁ B₀))) = finrank ℚ Yq := by
    rw [← finrank_map_inj hinjq, hYmap]
  have rk2 : finrank ℚ ↥(span ℚ (Ys : Set (MEB.Tan (d₀ + r) d₁ B₀)) ⊓ OmB (d₀ + r) d₁ B₀) =
      finrank ℚ ↥(Yq ⊓ OmAV d₀ d₁ B M) := by
    rw [← finrank_map_inj hinjq, Submodule.map_inf _ hinjq, hYmap, hPmap,
      inf_comm (OmAV d₀ d₁ B M), ← inf_assoc, inf_eq_left.mpr hYR']
  have hTors : TorInjB Vs := by
    intro v hv hvP hv1
    have h1 : j v ∈ OmAV d₀ d₁ B M := (hPmap.le ⟨v, hvP, rfl⟩).1
    have h2 : (j v).2.1 = 0 := hv1
    exact jEmb_injective (by rw [hTor (j v) hv h1 h2, map_zero])
  obtain ⟨Hs, hHsT, hτs, hineqs⟩ := trans41B An₀ H₀ (thm41SubAtB_bot An₀ _ _) Vs Ws Ys hVsT
    (by rw [hVs, hfT0]; exact hVdim) (Submodule.comap_mono hWV) hWsrat hYsfg hYsmem hTors (Or.inr rfl)
  have hHst : Hs.t = ⊥ := Submodule.eq_bot_of_subsingleton
  let H'' : SubgroupDataAV d₀ d₁ B M :=
    { U := Hs.U, t := ⊥, gam := Hs.h0.map (unflatL d₀ r), gam_rat := ratPair_map_unflat Hs.h0_rat,
      t_rat := isRatSub_botB (B := Bb B) }
  have hTan : Hs.tan.map j = H''.tan := by
    rw [tan_eq_of_bot H'' rfl]
    change (tanOf Hs.h0 Hs.U Hs.t).map j = _
    rw [hHst, map_jEmb_tanOf]
  have hT''T : H''.tan ≤ H'.tan := by rw [← hTan, ← hT0]; exact Submodule.map_mono hHsT
  have hWinf : finrank ℂ ↥(Ws ⊓ Hs.tan) = finrank ℂ ↥(W ⊓ H''.tan) := by
    rw [← finrank_map_inj jEmb_injective, Submodule.map_inf _ jEmb_injective, hmap W hWR, hTan]
  have hfT'' : finrank ℂ H''.tan = finrank ℂ Hs.tan := by rw [← hTan, finrank_map_inj jEmb_injective]
  have hTq : (Hs.tan.restrictScalars ℚ).map jq' = H''.tan.restrictScalars ℚ := by
    rw [← hTan]; rfl
  have rk3 : finrank ℚ ↥(span ℚ (Ys : Set (MEB.Tan (d₀ + r) d₁ B₀)) ⊓
      (Hs.tan.restrictScalars ℚ ⊔ OmB (d₀ + r) d₁ B₀)) =
      finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmAV d₀ d₁ B M)) := by
    rw [← finrank_map_inj hinjq, Submodule.map_inf _ hinjq, Submodule.map_sup, hYmap, hTq, hPmap]
    have hT''q : H''.tan.restrictScalars ℚ ≤ R.restrictScalars ℚ := fun x hx => hTR (hT''T hx)
    rw [← sup_inf_assoc_of_le _ hT''q, inf_comm _ (R.restrictScalars ℚ), ← inf_assoc,
      inf_eq_left.mpr hYR']
  -- numerics
  have hn0 : nPB H₀ = finrank ℂ (torusLie H'.U) := by simp [nPB, H₀]
  have hns : nPB Hs = finrank ℂ (torusLie H''.U) := by simp [nPB, hHst, H'']
  have hd2' := Nat.zero_le (d2H H')
  have hd2'' := Nat.zero_le (d2H H'')
  rw [rk1, rk2, rk3, hWs, hWinf, hfT0, ← hfT'', hn0, hns] at hineqs
  simp only [hWs, hWinf, hfT0, ← hfT''] at hτs
  refine ⟨H'', hT''T, hτs, ?_⟩
  simp only [nPAV]
  push_cast
  have hst : (1 : ℤ) ≤ ((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
      ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan)) := by linarith
  have hf : (0 : ℤ) ≤ (((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
      ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan)) - 1) * (d2H H' : ℤ) :=
    mul_nonneg (by linarith) (by exact_mod_cast hd2')
  nlinarith [hineqs, hf]

end LSG.W88
