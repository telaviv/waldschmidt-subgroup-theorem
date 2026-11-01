/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.K5dModel

/-!
# Theorem 4.1 for a subgroup `G' = H₀ × T_U × B` of `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`

`trans41`: Theorem 4.1 for `G'` (with `V' ⊂ T_{G'}` a hyperplane), written in the coordinates of `G`.
It is transported along `ι : (a, c, z) ↦ (A a, C c, z)` from `G_a^{k₀} × G_m^{k₁} × B` in the
coordinates `Tan k₀ k₁ m`, where `A` is a `ℚ̄`-basis matrix of `h₀` and `C` a `ℚ`-basis matrix of
`annQ U` (both with left inverses `B`, `D` over `ℚ̄`, `ℚ`). In the small coordinates it uses
`Thm41SubAt k₀ k₁ Ls t` when (NR) holds, and Roy's theorem (`sub41Concl_bot`, no (NR)) when `t = 0`.
-/

open Complex Module

namespace LSG.W88.K5d

variable {d0 d1 m : ℕ} (Ls : Fin m → PeriodPair)

/-- `d₁' + 2d₂'` of a subgroup. -/
noncomputable abbrev nP (H : SubgroupData (d0 := d0) (d1 := d1) Ls) : ℕ :=
  finrank ℂ (torusLie H.U) + 2 * finrank ℂ H.t

variable {k0 k1 : ℕ}

/-- `ι : (a, c, z) ↦ (A a, C c, z)`. -/
noncomputable def iotaG (A : Matrix (Fin d0) (Fin k0) K11.Kq) (C : Matrix (Fin d1) (Fin k1) ℚ) :
    Tan k0 k1 m →ₗ[ℂ] Tan d0 d1 m :=
  ((cmK K11.Kq A).mulVecLin.comp (LinearMap.fst ℂ _ _)).prod
    (((K11.cm C).mulVecLin.comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))).prod
      ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)))

/-- `π : (u, v, z) ↦ (B u, D v, z)`. -/
noncomputable def piG (B : Matrix (Fin k0) (Fin d0) K11.Kq) (D : Matrix (Fin k1) (Fin d1) ℚ) :
    Tan d0 d1 m →ₗ[ℂ] Tan k0 k1 m :=
  ((cmK K11.Kq B).mulVecLin.comp (LinearMap.fst ℂ _ _)).prod
    (((K11.cm D).mulVecLin.comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))).prod
      ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)))

lemma iotaG_apply (A : Matrix (Fin d0) (Fin k0) K11.Kq) (C : Matrix (Fin d1) (Fin k1) ℚ)
    (x : Tan k0 k1 m) : iotaG A C x = ((cmK K11.Kq A).mulVec x.1, (K11.cm C).mulVec x.2.1, x.2.2) :=
  rfl

lemma piG_apply (B : Matrix (Fin k0) (Fin d0) K11.Kq) (D : Matrix (Fin k1) (Fin d1) ℚ)
    (x : Tan d0 d1 m) : piG B D x = ((cmK K11.Kq B).mulVec x.1, (K11.cm D).mulVec x.2.1, x.2.2) :=
  rfl

lemma mulVec_left_invK {a b : ℕ} {A : Matrix (Fin a) (Fin b) K11.Kq}
    {B : Matrix (Fin b) (Fin a) K11.Kq} (hBA : B * A = 1) (x : Fin b → ℂ) :
    (cmK K11.Kq B).mulVec ((cmK K11.Kq A).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, ← cmK_mul, hBA, cmK_one, Matrix.one_mulVec]

lemma algVec_cmK_mulVec {a b : ℕ} (A : Matrix (Fin a) (Fin b) K11.Kq) {x : Fin b → ℂ}
    (hx : LSG.W88.AlgVec x) : LSG.W88.AlgVec ((cmK K11.Kq A).mulVec x) := by
  intro i
  rw [← K11.mem_Kq]
  simp only [cmK, Matrix.mulVec, dotProduct, Matrix.map_apply, Subfield.coe_subtype]
  exact K11.Kq.sum_mem fun j _ => K11.Kq.mul_mem (SetLike.coe_mem _) (K11.mem_Kq.mpr (hx j))

lemma algVec_cm_mulVec {a b : ℕ} (C : Matrix (Fin a) (Fin b) ℚ) {x : Fin b → ℂ}
    (hx : LSG.W88.AlgVec x) : LSG.W88.AlgVec ((K11.cm C).mulVec x) := by
  intro i
  have : (K11.cm C).mulVec x i = ∑ j, ((C i j : ℚ) : ℂ) * x j := by
    simp [K11.cm, Matrix.mulVec, dotProduct]
  rw [this]; exact K11.isAlg_ratComb _ _ hx

lemma exp_cm_mulVec {a b : ℕ} (C : Matrix (Fin a) (Fin b) ℚ) {x : Fin b → ℂ}
    (hx : ∀ j, IsAlgebraic ℚ (Complex.exp (x j))) (i : Fin a) :
    IsAlgebraic ℚ (Complex.exp ((K11.cm C).mulVec x i)) := by
  have : (K11.cm C).mulVec x i = ∑ j, ((C i j : ℚ) : ℂ) * x j := by
    simp [K11.cm, Matrix.mulVec, dotProduct]
  rw [this]; exact K11.isAlg_exp_ratComb _ _ hx

/-- **Theorem 4.1 for `G' = H'` in the coordinates of `G`** (`V ⊂ T_{G'}` a hyperplane of `T_{G'}`).
Hypotheses: Theorem 4.1 for `G_a^{k₀} × G_m^{k₁} × B` (`h41`), and (NR) for `G'` unless `t' = 0`. -/
theorem trans41 (hLs : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃)
    (H' : SubgroupData (d0 := d0) (d1 := d1) Ls)
    (h41 : Thm41SubAt (finrank ℂ H'.h0) (finrank ℚ (K11.annQ H'.U)) Ls H'.t)
    (V W : Submodule ℂ (Tan d0 d1 m)) (Y : AddSubgroup (Tan d0 d1 m))
    (hVT : V ≤ H'.tan) (hVdim : finrank ℂ V + 1 = finrank ℂ H'.tan)
    (hWV : W ≤ V) (hWrat : RationalOverQbarTan W) (hYfg : Y.FG)
    (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ Lam Ls)
    (hNR : finrank ℂ (torusLie H'.U) + 2 * finrank ℂ H'.h0 +
        finrank ℚ ↥(Submodule.span ℚ (Y : Set (Tan d0 d1 m)) ⊓ Ωs Ls d0 d1) ≤ 2 * finrank ℂ V ∨
      H'.t = ⊥) :
    ∃ H'' : SubgroupData (d0 := d0) (d1 := d1) Ls, H''.tan ≤ H'.tan ∧
      (finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan) <
        (finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan ∧
      ((finrank ℚ (Submodule.span ℚ (Y : Set (Tan d0 d1 m))) : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Y : Set (Tan d0 d1 m)) ⊓
            (H''.tan.restrictScalars ℚ ⊔ Ωs Ls d0 d1)) + ((nP Ls H' : ℤ) - nP Ls H'')) ≤
        (((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
            ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan))) *
          ((nP Ls H' : ℤ) - finrank ℚ ↥(Submodule.span ℚ (Y : Set (Tan d0 d1 m)) ⊓ Ωs Ls d0 d1)) := by
  classical
  set k0 := finrank ℂ H'.h0 with hk0
  set k1 := finrank ℚ (K11.annQ H'.U) with hk1
  obtain ⟨A, B, hBA, hA⟩ := exists_algFrame H'.h0 H'.h0_rat
  obtain ⟨C, D, hDC, hC⟩ := K11.exists_frame (K11.annQ H'.U)
  set ι : Tan k0 k1 m →ₗ[ℂ] Tan d0 d1 m := iotaG A C with hι
  set π : Tan d0 d1 m →ₗ[ℂ] Tan k0 k1 m := piG B D with hπ
  have htl' : torusLie H'.U = LinearMap.range (K11.cm C).mulVecLin := by
    rw [torusLie_eq_annC, K11.annC_eq_cspan, K11.cspan_eq_range hC]
  have hπι : ∀ x, π (ι x) = x := by
    intro x
    rw [hπ, hι, iotaG_apply, piG_apply, mulVec_left_invK hBA, K11.mulVec_left_inv hDC]
  have hinj : Function.Injective ι := fun x y h => by rw [← hπι x, ← hπι y, h]
  set R : Submodule ℂ (Tan d0 d1 m) := H'.h0.prod ((torusLie H'.U).prod ⊤) with hR
  have hιπ : ∀ v ∈ R, ι (π v) = v := by
    intro v hv
    rw [hR, Submodule.mem_prod, Submodule.mem_prod] at hv
    obtain ⟨h1, h2, -⟩ := hv
    rw [← hA] at h1; rw [htl'] at h2
    obtain ⟨a, ha⟩ := h1; obtain ⟨c, hc⟩ := h2
    rw [hι, hπ, piG_apply, iotaG_apply]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · change (cmK K11.Kq A).mulVec ((cmK K11.Kq B).mulVec v.1) = v.1
      rw [← ha]; simp only [Matrix.mulVecLin_apply]; rw [mulVec_left_invK hBA]
    · change (K11.cm C).mulVec ((K11.cm D).mulVec v.2.1) = v.2.1
      rw [← hc]; simp only [Matrix.mulVecLin_apply]; rw [K11.mulVec_left_inv hDC]
  have hrange : LinearMap.range ι = R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hR, Submodule.mem_prod, Submodule.mem_prod, hι, iotaG_apply, ← hA, htl']
      exact ⟨⟨x.1, rfl⟩, ⟨x.2.1, rfl⟩, Submodule.mem_top⟩
    · intro v hv; exact ⟨π v, hιπ v hv⟩
  have hTR : H'.tan ≤ R := by
    intro x hx
    rw [SubgroupData.tan, Submodule.mem_prod, Submodule.mem_prod] at hx
    rw [hR, Submodule.mem_prod, Submodule.mem_prod]
    exact ⟨hx.1, hx.2.1, Submodule.mem_top⟩
  have hTmap : (tanB k0 k1 H'.t).map ι = H'.tan := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      simp only [tanB, SetLike.mem_coe, Submodule.mem_prod] at hx
      have := (hrange ▸ LinearMap.mem_range_self ι x : ι x ∈ R)
      rw [hR, Submodule.mem_prod, Submodule.mem_prod] at this
      rw [SubgroupData.tan, Submodule.mem_prod, Submodule.mem_prod]
      exact ⟨this.1, this.2.1, hx.2.2⟩
    · intro v hv
      refine ⟨π v, ?_, hιπ v (hTR hv)⟩
      rw [SubgroupData.tan, Submodule.mem_prod, Submodule.mem_prod] at hv
      change π v ∈ tanB k0 k1 H'.t
      rw [tanB, Submodule.mem_prod, Submodule.mem_prod, hπ, piG_apply]
      exact ⟨Submodule.mem_top, Submodule.mem_top, hv.2.2⟩
  have hfT : finrank ℂ H'.tan = k0 + k1 + finrank ℂ H'.t := by
    rw [← hTmap, finrank_map_inj hinj, tanB, finrank_prodSub, finrank_prodSub]
    simp [add_assoc]
  have htor' : finrank ℂ (torusLie H'.U) = k1 := by
    have h1 := K11.finrank_annQ H'.U
    have h2 := finrank_torusLie H'.U
    omega
  have hmap : ∀ S : Submodule ℂ (Tan d0 d1 m), S ≤ R → (S.comap ι).map ι = S := by
    intro S hS; rw [Submodule.map_comap_eq, hrange, inf_eq_right.mpr hS]
  set Vs := V.comap ι with hVs_def
  set Ws := W.comap ι with hWs_def
  set Ys := Y.map π.toAddMonoidHom with hYs_def
  have hVR : V ≤ R := hVT.trans hTR
  have hWR : W ≤ R := hWV.trans hVR
  have hVs : finrank ℂ Vs = finrank ℂ V := by rw [← finrank_map_inj hinj, hmap V hVR]
  have hWs : finrank ℂ Ws = finrank ℂ W := by rw [← finrank_map_inj hinj, hmap W hWR]
  have hVsT : Vs ≤ tanB k0 k1 H'.t := by
    intro x hx
    have h := hVT (show ι x ∈ V from hx)
    rw [SubgroupData.tan, Submodule.mem_prod, Submodule.mem_prod] at h
    rw [tanB, Submodule.mem_prod, Submodule.mem_prod]
    exact ⟨Submodule.mem_top, Submodule.mem_top, h.2.2⟩
  have hWsrat : RationalOverQbarTan Ws := by
    set S := {w | w ∈ W ∧ AlgVec w.1 ∧ AlgVec w.2.1 ∧ AlgVec w.2.2} with hS
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
      · rw [hπ, piG_apply]; exact algVec_cmK_mulVec B hs.2.1
      · rw [hπ, piG_apply]; exact algVec_cm_mulVec D hs.2.2.1
      · rw [hπ, piG_apply]; exact hs.2.2.2
    · rw [Submodule.span_le]; exact fun x hx => hx.1
  have hYsfg : Ys.FG := K11.fg_map_addSubgroup hYfg _
  have hYsmem : ∀ x ∈ Ys, x ∈ Vs ∧ x ∈ Lam Ls := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyV, hyL⟩ := hY y hy
    refine ⟨?_, ?_⟩
    · change ι (π y) ∈ V
      rw [hιπ y (hVR hyV)]; exact hyV
    · change π y ∈ Lam Ls
      rw [hπ, piG_apply]
      exact ⟨algVec_cmK_mulVec B hyL.1, exp_cm_mulVec D hyL.2.1, hyL.2.2⟩
  -- the `ℚ`-structures
  set ιq := ι.restrictScalars ℚ with hιq
  have hinjq : Function.Injective ιq := hinj
  set Yq := Submodule.span ℚ (Y : Set (Tan d0 d1 m)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  have hYR : Yq ≤ R.restrictScalars ℚ := Submodule.span_le.mpr fun y hy => hVR (hY y hy).1
  have hYT : Yq ≤ H'.tan.restrictScalars ℚ := Submodule.span_le.mpr fun y hy => hVT (hY y hy).1
  have hYmap : (Submodule.span ℚ (Ys : Set (Tan k0 k1 m))).map ιq = Yq := by
    rw [Submodule.map_span]; congr 1
    ext v; constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      change ι (π y) ∈ Y
      rw [hιπ y (hVR (hY y hy).1)]; exact hy
    · intro hv; exact ⟨π v, ⟨v, hv, rfl⟩, hιπ v (hVR (hY v hv).1)⟩
  have hPmap : (Ωs Ls k0 k1).map ιq = Ωs Ls d0 d1 ⊓ R.restrictScalars ℚ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨c, z, hz, rfl⟩ := mem_Ωs Ls hx
        have : ιq (inT k0 k1 c + inE k0 k1 z) = inT d0 d1 (C.mulVec c) + inE d0 d1 z := by
          change ι _ = _
          rw [hι, iotaG_apply, inT_apply, inT_apply, inE_apply, inE_apply]
          refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
          simp only [Prod.snd_add, Prod.fst_add, add_zero, Matrix.mulVec_smul,
            K11.cm_mulVec_castL]
        rw [this]
        exact Submodule.add_mem _ (inT_mem_Ωs Ls _) (inE_mem_Ωs Ls hz)
      · change ι x ∈ R; rw [← hrange]; exact LinearMap.mem_range_self ι x
    · rintro x ⟨hxΩ, hxR⟩
      obtain ⟨q, z, hz, rfl⟩ := mem_Ωs Ls hxΩ
      have hq : q ∈ K11.annQ H'.U := by
        have h := hxR
        change inT d0 d1 q + inE d0 d1 z ∈ R at h
        rw [hR, Submodule.mem_prod, Submodule.mem_prod] at h
        have h2 := h.2.1
        simp only [inT_apply, inE_apply, Prod.snd_add, Prod.fst_add, add_zero] at h2
        exact castL_mem_torusLie_iff.mp h2
      rw [← hC] at hq
      obtain ⟨c, rfl⟩ := hq
      refine ⟨inT k0 k1 c + inE k0 k1 z, Submodule.add_mem _ (inT_mem_Ωs Ls c)
        (inE_mem_Ωs Ls hz), ?_⟩
      change ι _ = _
      rw [hι, iotaG_apply, inT_apply, inT_apply, inE_apply, inE_apply]
      refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
      simp only [Prod.snd_add, Prod.fst_add, add_zero, Matrix.mulVec_smul, K11.cm_mulVec_castL,
        Matrix.mulVecLin_apply]
  have rk1 : rk Ys = finrank ℚ Yq := by rw [rk, ← finrank_map_inj hinjq, hYmap]
  have rk2 : rk (Ys ⊓ Per Ls) = finrank ℚ ↥(Yq ⊓ Ωs Ls d0 d1) := by
    rw [rk, K11.span_inf_addSubgroup, ← finrank_map_inj hinjq, Submodule.map_inf _ hinjq,
      hYmap, hPmap, inf_comm (Ωs Ls d0 d1), ← inf_assoc, inf_eq_left.mpr hYR]
  -- the small theorem
  obtain ⟨Hs, hHst, -, hτs, hineqs⟩ : Sub41Concl k0 k1 Ls H'.t Vs Ws Ys := by
    by_cases ht : H'.t = ⊥
    · have hVsT' : Vs ≤ tanB k0 k1 ⊥ := ht ▸ hVsT
      have := sub41Concl_bot Ls Vs Ws Ys hVsT' (by rw [hVs]; rw [ht, finrank_bot] at hfT; omega)
        (Submodule.comap_mono hWV) hWsrat hYsfg hYsmem
      rw [ht]; exact this
    · have hNR' := hNR.resolve_right ht
      exact h41 Vs Ws Ys hVsT (by rw [hVs]; omega) (Submodule.comap_mono hWV) hWsrat hYsfg
        hYsmem (by rw [rk2, hVs]; rw [htor'] at hNR'; omega)
  -- the subgroup `G''`
  have hh0rat : RationalOverQbar (Hs.h0.map (cmK K11.Kq A).mulVecLin) := by
    set S := {w | w ∈ Hs.h0 ∧ AlgVec w} with hS
    refine le_antisymm ?_ (Submodule.span_le.mpr fun x hx => hx.1)
    conv_lhs => rw [Hs.h0_rat]
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw.1, rfl⟩, algVec_cmK_mulVec A hw.2⟩
  let H'' : SubgroupData (d0 := d0) (d1 := d1) Ls :=
    { h0 := Hs.h0.map (cmK K11.Kq A).mulVecLin
      U := K11.annQ ((K11.annQ Hs.U).map C.mulVecLin)
      t := Hs.t
      h0_rat := hh0rat
      t_ab := Hs.t_ab }
  have htl'' : (torusLie Hs.U).map (K11.cm C).mulVecLin = torusLie H''.U := by
    rw [torusLie_eq_annC, K11.annC_eq_cspan, K11.map_cspan, torusLie_eq_annC,
      ← K11.cspan_eq_annC]
  have hTan : Hs.tan.map ι = H''.tan := by
    ext ⟨u, v, z⟩
    rw [Submodule.mem_map]
    simp only [H'', SubgroupData.tan, Submodule.mem_prod]
    rw [← htl'']
    constructor
    · rintro ⟨⟨a, c, w⟩, ⟨ha, hc, hw⟩, hx⟩
      rw [hι, iotaG_apply] at hx
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := ⟨congrArg Prod.fst hx,
        congrArg (fun p => p.2.1) hx, congrArg (fun p => p.2.2) hx⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨c, hc, rfl⟩, hw⟩
    · rintro ⟨⟨a, ha, rfl⟩, ⟨c, hc, rfl⟩, hz⟩
      exact ⟨(a, c, z), ⟨ha, hc, hz⟩, rfl⟩
  have hT''T : H''.tan ≤ H'.tan := by
    rw [← hTan, ← hTmap]
    refine Submodule.map_mono ?_
    intro x hx
    rw [SubgroupData.tan, Submodule.mem_prod, Submodule.mem_prod] at hx
    rw [tanB, Submodule.mem_prod, Submodule.mem_prod]
    exact ⟨Submodule.mem_top, Submodule.mem_top, hHst hx.2.2⟩
  have hWinf : finrank ℂ ↥(Ws ⊓ Hs.tan) = finrank ℂ ↥(W ⊓ H''.tan) := by
    rw [← finrank_map_inj hinj, Submodule.map_inf _ hinj, hmap W hWR, hTan]
  have hfT'' : finrank ℂ H''.tan = finrank ℂ Hs.tan := by rw [← hTan, finrank_map_inj hinj]
  have htorS : finrank ℂ (torusLie H''.U) = finrank ℂ (torusLie Hs.U) := by
    rw [← htl'', finrank_map_inj (K11.cm_injective hDC)]
  have hTq : (Submodule.span ℚ ((Hs.tan.toAddSubgroup : AddSubgroup (Tan k0 k1 m)) :
      Set (Tan k0 k1 m))).map ιq = H''.tan.restrictScalars ℚ := by
    rw [K11.span_submodule_coe, ← hTan]; rfl
  have rk3 : rk (Ys ⊓ (Hs.tan.toAddSubgroup ⊔ Per Ls)) =
      finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ωs Ls d0 d1)) := by
    rw [rk, K11.span_inf_addSubgroup, K11.span_sup_addSubgroup, ← finrank_map_inj hinjq,
      Submodule.map_inf _ hinjq, Submodule.map_sup, hYmap, hTq, hPmap]
    have hT''q : H''.tan.restrictScalars ℚ ≤ R.restrictScalars ℚ := fun x hx => hTR (hT''T hx)
    have : Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ωs Ls d0 d1 ⊓ R.restrictScalars ℚ) =
        Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ωs Ls d0 d1) := by
      rw [← sup_inf_assoc_of_le _ hT''q, inf_comm _ (R.restrictScalars ℚ), ← inf_assoc,
        inf_eq_left.mpr hYR]
    rw [this]
  -- numerics
  have hle1 : finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ωs Ls d0 d1)) ≤ finrank ℚ Yq :=
    Submodule.finrank_mono inf_le_left
  have hle2 : finrank ℂ ↥(W ⊓ H''.tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
  have hfTs := finrank_tan Ls Hs
  have hftorS := finrank_torusLie Hs.U
  have hHst' : finrank ℂ Hs.t ≤ finrank ℂ H'.t := Submodule.finrank_mono hHst
  have hh0s : finrank ℂ Hs.h0 ≤ k0 := (Submodule.finrank_le _).trans (by simp)
  have hδ : (Hs.δB H'.t : ℤ) = (finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan := by
    simp only [SubgroupData.δB, SubgroupData.δ0, SubgroupData.δ1]
    rw [hfT'', hfTs, hfT]
    push_cast [Nat.cast_sub hHst', Nat.cast_sub hh0s]
    have : (finrank ℚ Hs.U : ℤ) = k1 - finrank ℂ (torusLie Hs.U) := by omega
    linarith
  have hδ12 : ((Hs.δ1 + 2 * (finrank ℂ H'.t - finrank ℂ Hs.t) : ℕ) : ℤ) =
      (nP Ls H' : ℤ) - nP Ls H'' := by
    simp only [SubgroupData.δ1, nP, htorS, htor']
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
    have e1 : ((finrank ℚ Yq - finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ωs Ls d0 d1)) +
        Hs.δ1 + 2 * (finrank ℂ H'.t - finrank ℂ Hs.t) : ℕ) : ℤ) = (finrank ℚ Yq : ℤ) -
          finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ωs Ls d0 d1)) +
          ((nP Ls H' : ℤ) - nP Ls H'') := by
      rw [← hδ12]; push_cast [Nat.cast_sub hle1]; ring
    have e2 : (((k0 + k1 + finrank ℂ H'.t : ℕ) : ℤ) - finrank ℂ V) = 1 := by
      rw [hfT] at hVdim; omega
    have e3 : ((Hs.δB H'.t : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H''.tan) : ℕ) : ℤ)) =
        ((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
          ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan)) := by
      rw [hδ, Nat.cast_sub hle2]
    have e4 : (((k1 + 2 * finrank ℂ H'.t : ℕ) : ℤ) - finrank ℚ ↥(Yq ⊓ Ωs Ls d0 d1)) =
        (nP Ls H' : ℤ) - finrank ℚ ↥(Yq ⊓ Ωs Ls d0 d1) := by
      simp only [nP, htor']
    rw [e1, e2, e3, e4, mul_one] at hineqs
    exact hineqs

end LSG.W88.K5d
