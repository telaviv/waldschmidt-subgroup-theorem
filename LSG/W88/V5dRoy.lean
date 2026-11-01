/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dTrans

/-!
# Theorem 4.1 for the linear members `G_a^{k₀} × G_m^{k₁}` of the class, without (NR)

`concl41_lin`: for `TanV k₀ k₁ g f` with `g = f = 0` (no elliptic and no fibre part), the conclusion
`Concl41` holds without (NR). Transported from `K5d.sub41Concl_bot` (Roy's Theorem 1 in StrongSix)
along `Tan k₀ k₁ 0 ≅ TanV k₀ k₁ 0 0`.
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

variable {k0 k1 : ℕ}

/-- `Tan k₀ k₁ 0 ≅ TanV k₀ k₁ 0 0`. -/
noncomputable def eqv0 : Tan k0 k1 0 ≃ₗ[ℂ] TanV k0 k1 0 0 where
  toFun x := (x.1, x.2.1, x.2.2, 0)
  invFun y := (y.1, y.2.1, y.2.2.1)
  map_add' x y := by simp
  map_smul' c x := by simp
  left_inv x := rfl
  right_inv y := by
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    funext i; exact i.elim0

lemma eqv0_symm_apply (y : TanV k0 k1 0 0) : (eqv0.symm y : Tan k0 k1 0) = (y.1, y.2.1, y.2.2.1) :=
  rfl

lemma fin0_eq {x y : Fin 0 → ℂ} : x = y := funext fun i => i.elim0

/-- **Theorem 4.1 for `G_a^{k₀} × G_m^{k₁}` in the class, without (NR).** -/
theorem concl41_lin {g f : ℕ} (hg : g = 0) (hf : f = 0) (Ls : Fin g → PeriodPair)
    (M : Matrix (Fin f) (Fin g) ℂ) (V W : Submodule ℂ (TanV k0 k1 g f))
    (Y : AddSubgroup (TanV k0 k1 g f)) (hV : finrank ℂ V < k0 + k1 + g + f) (hWV : W ≤ V)
    (hWrat : RatSubV W) (hYfg : Y.FG) (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M) :
    Concl41 Ls M V W Y := by
  classical
  subst hg hf
  set e : TanV k0 k1 0 0 ≃ₗ[ℂ] Tan k0 k1 0 := (eqv0 (k0 := k0) (k1 := k1)).symm with he
  have einj : Function.Injective e := e.injective
  set V' := V.map e.toLinearMap
  set W' := W.map e.toLinearMap
  set Y' := Y.map e.toLinearMap.toAddMonoidHom
  have hfV : finrank ℂ V' = finrank ℂ V := K5d.finrank_map_inj einj V
  have hfW : finrank ℂ W' = finrank ℂ W := K5d.finrank_map_inj einj W
  have hVT : V' ≤ tanB k0 k1 ⊥ := by
    rintro _ ⟨v, -, rfl⟩
    exact ⟨Submodule.mem_top, Submodule.mem_top, (Submodule.mem_bot ℂ).mpr fin0_eq⟩
  have hWrat' : RationalOverQbarTan W' := by
    rw [← K5d.ratT_iff]
    refine ⟨e '' {w | w ∈ W ∧ AlgVecV w}, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩; exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2.1⟩
    · change W.map e.toLinearMap = _
      conv_lhs => rw [hWrat]
      rw [Submodule.map_span]; rfl
  have hY' : ∀ y ∈ Y', y ∈ V' ∧ y ∈ Lam Ls := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyV, hyL⟩ := hY y hy
    exact ⟨⟨y, hyV, rfl⟩, ⟨hyL.1, hyL.2.1, fun j => hyL.2.2.1 j⟩⟩
  obtain ⟨H, -, -, hτ, hin⟩ := K5d.sub41Concl_bot Ls V' W' Y' hVT (by simpa [hfV] using hV)
    (Submodule.map_mono hWV) hWrat' (K11.fg_map_addSubgroup hYfg _) hY'
  -- the member of the class
  have hgam : RatPair (H.h0.prod (⊤ : Submodule ℂ (Fin 0 → ℂ))) := by
    apply le_antisymm _ (Submodule.span_le.mpr fun _ hw => hw.1)
    rintro ⟨a, s⟩ ⟨ha, -⟩
    have ha' : a ∈ Submodule.span ℂ {w | w ∈ H.h0 ∧ AlgVec w} := by rw [← H.h0_rat]; exact ha
    have hs : s = 0 := fin0_eq
    subst hs
    have hmap : (Submodule.span ℂ {w | w ∈ H.h0 ∧ AlgVec w}).map (LinearMap.inl ℂ _ (Fin 0 → ℂ)) ≤
        Submodule.span ℂ {w | w ∈ H.h0.prod (⊤ : Submodule ℂ (Fin 0 → ℂ)) ∧ AlgPair w} := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      exact Submodule.subset_span ⟨⟨hw.1, Submodule.mem_top⟩, hw.2, fun i => i.elim0⟩
    exact hmap ⟨a, ha', rfl⟩
  let H' : SubgroupDataV (d0 := k0) (d1 := k1) Ls M :=
    { U := H.U, t := H.t, gam := H.h0.prod ⊤, gam_rat := hgam, t_ab := H.t_ab }
  have hmemT : ∀ x : TanV k0 k1 0 0, x ∈ H'.tan ↔ x.1 ∈ H.h0 ∧ x.2.1 ∈ torusLie H.U := by
    intro x
    constructor
    · intro hx
      have := tan_le_prod H' hx
      refine ⟨?_, this.2.1⟩
      obtain ⟨γ, hγ, hγx⟩ := this.1
      rw [← hγx]; exact hγ.1
    · rintro ⟨h1, h2⟩
      have hx : x = vecIncl (x.1, (0 : Fin 0 → ℂ)) + torIncl x.2.1 := by
        refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext fin0_eq fin0_eq))
      rw [hx]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left
        ⟨_, ⟨h1, Submodule.mem_top⟩, rfl⟩)) (Submodule.mem_sup_left (Submodule.mem_sup_right
          ⟨_, h2, rfl⟩))
  have hTmap : H.tan = H'.tan.map e.toLinearMap := by
    ext x
    constructor
    · intro hx
      refine ⟨eqv0 x, (hmemT _).mpr ⟨hx.1, hx.2.1⟩, ?_⟩
      change e (eqv0 x) = x
      rw [he, LinearEquiv.symm_apply_apply]
    · rintro ⟨y, hy, rfl⟩
      have hy' := (hmemT y).mp hy
      refine ⟨hy'.1, hy'.2, ?_⟩
      have h0 : ∀ z : Fin 0 → ℂ, z ∈ H.t := fun z => by
        rw [fin0_eq (x := z) (y := 0)]; exact H.t.zero_mem
      exact h0 _
  have hPmap : (Per Ls : AddSubgroup (Tan k0 k1 0)) =
      (PerV Ls M).map e.toLinearMap.toAddMonoidHom := by
    ext x
    constructor
    · intro hx
      refine ⟨eqv0 x, ⟨hx.1, hx.2.1, fun j => j.elim0, fin0_eq⟩, ?_⟩
      change e (eqv0 x) = x
      rw [he, LinearEquiv.symm_apply_apply]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, hy.2.1, fun j => j.elim0⟩
  -- ranks
  set φ := e.toLinearMap.toAddMonoidHom
  have hφ : Function.Injective φ := einj
  have rkY : rk Y' = rk Y := LSG.CM.rk_map_of_injective φ hφ Y
  have rkP : rk (Y' ⊓ Per Ls) = rk (Y ⊓ PerV Ls M) := by
    rw [hPmap, ← AddSubgroup.map_inf_eq _ _ φ hφ, LSG.CM.rk_map_of_injective φ hφ]
  have rkT : rk (Y' ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) =
      rk (Y ⊓ (H'.tan.toAddSubgroup ⊔ PerV Ls M)) := by
    have : H.tan.toAddSubgroup = H'.tan.toAddSubgroup.map φ := by
      rw [hTmap]; rfl
    rw [this, hPmap, ← AddSubgroup.map_sup, ← AddSubgroup.map_inf_eq _ _ φ hφ,
      LSG.CM.rk_map_of_injective φ hφ]
  have hWinf : finrank ℂ ↥(W' ⊓ H.tan) = finrank ℂ ↥(W ⊓ H'.tan) := by
    rw [hTmap, ← Submodule.map_inf _ einj, K5d.finrank_map_inj einj]
  -- dimensions
  have hfT : finrank ℂ H.tan = finrank ℂ H'.tan := by rw [hTmap, K5d.finrank_map_inj einj]
  have hfT2 := K5d.finrank_tan Ls H
  have htl := K5d.finrank_torusLie H.U
  have hgam0' : H'.gam.map (LinearMap.fst ℂ (Fin k0 → ℂ) (Fin 0 → ℂ)) = H.h0 := by
    ext a; constructor
    · rintro ⟨⟨a', s⟩, ⟨ha, -⟩, rfl⟩; exact ha
    · intro ha; exact ⟨(a, 0), ⟨ha, Submodule.mem_top⟩, rfl⟩
  have hgam0 : finrank ℂ (H'.gam.map (LinearMap.fst ℂ (Fin k0 → ℂ) (Fin 0 → ℂ))) =
      finrank ℂ H.h0 := by rw [hgam0']
  have ht0 : finrank ℂ H.t = 0 := by
    have : H.t = ⊥ := by
      rw [eq_bot_iff]; intro z _; rw [Submodule.mem_bot]; exact fin0_eq
    rw [this, finrank_bot]
  have hh0 : finrank ℂ H.h0 ≤ k0 := (Submodule.finrank_le _).trans (by simp)
  have hδ : H'.δ = H.δB ⊥ := by
    simp only [SubgroupDataV.δ, SubgroupData.δB, SubgroupData.δ0, SubgroupData.δ1, finrank_bot]
    rw [← hfT]; omega
  have hδ0 : H'.δ0 = H.δ0 := by simp only [SubgroupDataV.δ0, SubgroupData.δ0, hgam0]
  have hδ1 : H'.δ1 = H.δ1 := rfl
  have hδ2 : H'.δ2 = 0 := by
    simp only [SubgroupDataV.δ2, hδ, hδ0, hδ1, SubgroupData.δB, finrank_bot]; omega
  refine ⟨H', ?_, ?_, ?_⟩
  · change H'.δ ≠ 0
    rw [hδ]
    omega
  · rw [hδ, ← hfW, hWinf.symm]; exact hτ
  · rw [rkY, rkT, rkP, hfW, hWinf, finrank_bot, hfV] at hin
    rw [hδ, hδ2, hδ1]
    simpa using hin

end LSG.W88.V5d
