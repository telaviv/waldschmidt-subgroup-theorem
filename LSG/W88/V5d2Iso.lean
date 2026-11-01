/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dIso
import LSG.W88.V5d2Stmt

/-!
# Transfer of `HyperplaneKappaVec2` to a `lean_mstar` group model

`hyperplaneKappa_of_iso2`: `hyperplaneKappa_of_iso` (`V5dIso.lean`, same hypotheses (i)–(v)) for
`d₀ = 0`, `r ≤ 2`, from `HyperplaneKappaVec2`.
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

variable {d0 d1 m r : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

/-- **Transfer of W88 §5d along a linear isomorphism of tangent spaces** (`d₀ = 0`, `r ≤ 2`). -/
theorem hyperplaneKappa_of_iso2 (h : HyperplaneKappaVec2)
    (hLs : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) (hM : AlgMat M) (hd0 : d0 = 0) (hr : r ≤ 2)
    (hLA : LiftAlg Ls) (hPT : PerTanRat Ls)
    {Vt : Type*} [AddCommGroup Vt] [Module ℂ Vt] [Module ℚ Vt] [IsScalarTower ℚ ℂ Vt]
    (G : MStarCopy.GroupModel Vt) (ι : TanV d0 d1 m r ≃ₗ[ℂ] Vt)
    (halg : ∀ v, G.alg v → AlgVecV (ι.symm v))
    (Λs : AddSubgroup (TanV d0 d1 m r)) (hΛs : ∀ x ∈ Λs, x ∈ LamV Ls M)
    (hlam : ∀ y ∈ G.lam, ∃ N : ℕ, 0 < N ∧ N • ι.symm y ∈ Λs)
    (hper : G.per ≤ (OmV d0 d1 Ls M).map (ι.toLinearMap.restrictScalars ℚ))
    (hd1 : G.d₁ = d1) (hd2 : G.d₂ = m + r)
    (hsub : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan ≠ ⊥ →
      G.sub (H.tan.map ι.toLinearMap)) :
    MStarCopy.HyperplaneKappa G := by
  classical
  intro V W n y hV hWV hWrat hy hineq
  set ιq : TanV d0 d1 m r →ₗ[ℚ] Vt := ι.toLinearMap.restrictScalars ℚ with hιq
  set ιs : Vt →ₗ[ℚ] TanV d0 d1 m r := ι.symm.toLinearMap.restrictScalars ℚ with hιs
  have hιsq : Function.Injective ιs := ι.symm.injective
  have hfTan : finrank ℂ Vt = d0 + d1 + m + r := by
    rw [← ι.finrank_eq]; simp [add_assoc]
  set V' := V.comap ι.toLinearMap with hV'
  set W' := W.comap ι.toLinearMap with hW'
  have hfV' : finrank ℂ V' = finrank ℂ V := by
    rw [hV', Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hfW' : finrank ℂ W' = finrank ℂ W := by
    rw [hW', Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hW'rat : RatSubV W' := by
    obtain ⟨S, hS, rfl⟩ := hWrat
    rw [← ratV_iff]
    refine ⟨ι.symm '' S, ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩; exact halg s (hS s hs)
    · rw [hW', Submodule.comap_equiv_eq_map_symm, Submodule.map_span]; rfl
  choose N hN hNΛ using fun i => hlam (y i) (hy i).2
  let y' : Fin n → TanV d0 d1 m r := fun i => N i • ι.symm (y i)
  set Y := AddSubgroup.closure (Set.range y') with hY
  have hYfg : Y.FG := (AddSubgroup.fg_iff _).mpr ⟨_, rfl, Set.finite_range y'⟩
  have hYΛ : Y ≤ Λs := (AddSubgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hNΛ i)
  have hYV : Y ≤ V'.toAddSubgroup := (AddSubgroup.closure_le _).mpr (by
    rintro _ ⟨i, rfl⟩
    change ι (N i • ι.symm (y i)) ∈ V
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    exact V.nsmul_mem (hy i).1 _)
  have hspanY : Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) =
      (Submodule.span ℚ (Set.range y)).map ιs := by
    rw [hY, K11.span_closure_eq, Submodule.map_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change N i • ιs (y i) ∈ Submodule.span ℚ (ιs '' Set.range y)
      have hmem : ιs (y i) ∈ Submodule.span ℚ (ιs '' Set.range y) :=
        Submodule.subset_span ⟨y i, ⟨i, rfl⟩, rfl⟩
      exact nsmul_mem hmem _
    · rw [Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have h0 : ((N i : ℚ)⁻¹ • y' i) = ιs (y i) := by
        change (N i : ℚ)⁻¹ • (N i • ι.symm (y i)) = ι.symm (y i)
        rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (hN i).ne'),
          one_smul]
      rw [SetLike.mem_coe, ← h0]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrkY : rk Y = finrank ℚ (Submodule.span ℚ (Set.range y)) := by
    rw [rk, hspanY, K5d.finrank_map_inj hιsq]
  have hκ : finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ G.per) ≤ rk (Y ⊓ PerV Ls M) := by
    rw [rk, K11.span_inf_addSubgroup, hspanY, ← K5d.finrank_map_inj hιsq
      (Submodule.span ℚ (Set.range y) ⊓ G.per)]
    have hfin : FiniteDimensional ℚ ↥((Submodule.span ℚ (Set.range y)).map ιs) := by
      rw [Submodule.map_span]
      exact FiniteDimensional.span_of_finite ℚ ((Set.finite_range y).image _)
    have : FiniteDimensional ℚ ↥((Submodule.span ℚ (Set.range y)).map ιs ⊓ OmV d0 d1 Ls M) :=
      Submodule.finiteDimensional_of_le inf_le_left
    refine Submodule.finrank_mono ?_
    rw [Submodule.map_inf _ hιsq]
    refine inf_le_inf_left _ ?_
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hper hp
    change ι.symm (ι q) ∈ _
    rw [LinearEquiv.symm_apply_apply]; exact hq
  have : FiniteDimensional ℂ Vt := LinearEquiv.finiteDimensional ι
  have hdimW : finrank ℂ W ≤ finrank ℂ V := Submodule.finrank_mono hWV
  obtain ⟨H, hHne, hHV⟩ := h d0 d1 m r Ls M hLs hM hd0 hr hLA hPT V' W' Y
    (by rw [hfV']; omega) (Submodule.comap_mono hWV) hW'rat hYfg
    (fun z hz => ⟨hYV hz, hΛs z (hYΛ hz)⟩) (by
      rw [hrkY, hfW']
      rw [hd1, hd2, hfTan] at hineq
      have h1 : ((d0 + d1 + m + r : ℕ) : ℤ) - 1 - finrank ℂ W ≥ 0 := by
        have := hV; rw [hfTan] at this; omega
      push_cast at hineq h1 ⊢
      nlinarith [hκ])
  refine ⟨H.tan.map ι.toLinearMap, hsub H hHne, ?_, ?_⟩
  · intro h0
    apply hHne
    rw [← Submodule.map_bot ι.toLinearMap] at h0
    exact Submodule.map_injective_of_injective ι.injective h0
  · rintro _ ⟨x, hx, rfl⟩; exact hHV hx

end LSG.W88.V5d
