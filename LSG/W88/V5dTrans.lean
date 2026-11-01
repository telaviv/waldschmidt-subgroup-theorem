/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dPush

/-!
# Theorem 4.1 for a member `G'` of the class, in the coordinates of `G`

`trans41V`: given a frame `F` of a member `H'` and the conclusion of Theorem 4.1 for the class-`𝒞`
group `G_H` and the transported data `(Psi⁻¹ V, Psi⁻¹ W, Phi(Y))`, Theorem 4.1 holds for `G'` with
`(V, W, Y)`, written in the coordinates of `G` with `nPV` (`d₁' + 2d₂'`, W88's projection-based
dimensions). `trans_premises`: the transported data satisfy the premises of `Theorem41VecLA`.
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

variable {d0 d1 m r : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

/-- `d₁' + 2d₂'` of a member (W88's projection-based `d₁' = dim π₁(G')`, `d₂' = d' − d₀' − d₁'`). -/
noncomputable def nPV (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) : ℤ :=
  (finrank ℂ (torusLie H.U) : ℤ) + 2 * ((finrank ℂ H.tan : ℤ) -
    finrank ℂ (H.gam.map (LinearMap.fst ℂ (Fin d0 → ℂ) (Fin r → ℂ))) - finrank ℂ (torusLie H.U))

lemma tan_le_prod (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) :
    H.tan ≤ (H.gam.map (LinearMap.fst ℂ (Fin d0 → ℂ) (Fin r → ℂ))).prod
      ((torusLie H.U).prod ⊤) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨⟨γ, hγ, rfl⟩, (torusLie H.U).zero_mem, Submodule.mem_top⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨Submodule.zero_mem _, hv, Submodule.mem_top⟩
  · rintro _ ⟨p, -, rfl⟩
    exact ⟨Submodule.zero_mem _, (torusLie H.U).zero_mem, Submodule.mem_top⟩

lemma finrank_tan_le (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) :
    finrank ℂ H.tan ≤ finrank ℂ (H.gam.map (LinearMap.fst ℂ (Fin d0 → ℂ) (Fin r → ℂ))) +
      finrank ℂ (torusLie H.U) + (m + r) := by
  refine (Submodule.finrank_mono (tan_le_prod H)).trans ?_
  rw [K5d.finrank_prodSub, K5d.finrank_prodSub, finrank_top, Module.finrank_prod]
  simp [add_assoc]

lemma finrank_gam_fst_le (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) :
    finrank ℂ (H.gam.map (LinearMap.fst ℂ (Fin d0 → ℂ) (Fin r → ℂ))) ≤ d0 :=
  (Submodule.finrank_le _).trans (by simp)

namespace Frame

variable {H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M} (F : Frame H)

omit F in
lemma finrank_torusLie' : finrank ℂ (torusLie H.U) = fk1 H := by
  have h1 := K11.finrank_annQ H.U
  have h2 := K5d.finrank_torusLie H.U
  simp only [fk1]; omega

include F in
lemma nPV_eq : nPV H = fk1 H + 2 * (fg H + ff H) := by
  rw [nPV, F.finrank_tan, finrank_torusLie']; push_cast; ring

lemma ff_le : ff H ≤ r := (Submodule.finrank_le _).trans (by simp)

lemma nPV_push (Hs : SubgroupDataV (d0 := fk0 H) (d1 := fk1 H) F.LsH F.MH) :
    nPV (F.push Hs) = nPV Hs := by
  rw [nPV, nPV, F.finrank_push_tan, F.finrank_push_gam_fst, F.finrank_torusLie_push]

end Frame

/-- **Theorem 4.1 for `G'` in the coordinates of `G`**, from Theorem 4.1 for `G_H` and the
transported data. -/
theorem trans41V {H' : SubgroupDataV (d0 := d0) (d1 := d1) Ls M} (F : Frame H')
    (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r))
    (hVT : V ≤ H'.tan) (hVdim : finrank ℂ V + 1 = finrank ℂ H'.tan) (hWV : W ≤ V)
    (hYfg : Y.FG) (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M)
    (hC : Concl41 F.LsH F.MH (V.comap F.Psi) (W.comap F.Psi) (Y.map F.Phi.toAddMonoidHom)) :
    ∃ H'' : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H''.tan ≤ H'.tan ∧
      (finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan) < (finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan ∧
      ((finrank ℚ (Submodule.span ℚ (Y : Set (TanV d0 d1 m r))) : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) ⊓
            (H''.tan.restrictScalars ℚ ⊔ OmV d0 d1 Ls M)) + (nPV H' - nPV H'')) ≤
        (((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
            ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan))) *
          (nPV H' - finrank ℚ ↥(Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) ⊓ OmV d0 d1 Ls M)) := by
  classical
  obtain ⟨Hs, -, hτs, hineqs⟩ := hC
  set Ψ := F.Psi with hΨ
  set Φ := F.Phi with hΦ
  have hinj : Function.Injective Ψ := F.Psi_injective
  have hrange : LinearMap.range Ψ = H'.tan := F.range_Psi
  have hmap : ∀ S : Submodule ℂ (TanV d0 d1 m r), S ≤ H'.tan → (S.comap Ψ).map Ψ = S := by
    intro S hS; rw [Submodule.map_comap_eq, hrange, inf_eq_right.mpr hS]
  have hWT : W ≤ H'.tan := hWV.trans hVT
  set Vs := V.comap Ψ with hVs_def
  set Ws := W.comap Ψ with hWs_def
  set Ys := Y.map Φ.toAddMonoidHom with hYs_def
  have hVs : finrank ℂ Vs = finrank ℂ V := by rw [← K5d.finrank_map_inj hinj, hmap V hVT]
  have hWs : finrank ℂ Ws = finrank ℂ W := by rw [← K5d.finrank_map_inj hinj, hmap W hWT]
  -- the `ℚ`-structures
  set Ψq := Ψ.restrictScalars ℚ with hΨq
  have hinjq : Function.Injective Ψq := hinj
  set Yq := Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) with hYq
  set Ω := OmV d0 d1 Ls M with hΩ
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  have hYT : Yq ≤ H'.tan.restrictScalars ℚ := Submodule.span_le.mpr fun y hy => hVT (hY y hy).1
  have hYmap :
      (Submodule.span ℚ (Ys : Set (TanV (fk0 H') (fk1 H') (fg H') (ff H')))).map Ψq = Yq := by
    rw [Submodule.map_span]; congr 1
    ext v; constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      change Ψ (Φ y) ∈ Y
      rw [F.Psi_Phi (hVT (hY y hy).1)]; exact hy
    · intro hv; exact ⟨Φ v, ⟨v, hv, rfl⟩, F.Psi_Phi (hVT (hY v hv).1)⟩
  have hPmap := F.map_span_per
  have rk1 : rk Ys = finrank ℚ Yq := by rw [rk, ← K5d.finrank_map_inj hinjq, hYmap]
  have rk2 : rk (Ys ⊓ PerV F.LsH F.MH) = finrank ℚ ↥(Yq ⊓ Ω) := by
    rw [rk, K11.span_inf_addSubgroup, ← K5d.finrank_map_inj hinjq, Submodule.map_inf _ hinjq,
      hYmap, hPmap, inf_comm Ω, ← inf_assoc, inf_eq_left.mpr hYT]
  -- the subgroup `G''`
  set H'' := F.push Hs with hH''
  have hTan : Hs.tan.map Ψ = H''.tan := (F.push_tan Hs).symm
  have hT''T : H''.tan ≤ H'.tan := F.push_tan_le Hs
  have hWinf : finrank ℂ ↥(Ws ⊓ Hs.tan) = finrank ℂ ↥(W ⊓ H''.tan) := by
    rw [← K5d.finrank_map_inj hinj, Submodule.map_inf _ hinj, hmap W hWT, hTan]
  have hfT'' : finrank ℂ H''.tan = finrank ℂ Hs.tan := F.finrank_push_tan Hs
  have hTq : (Submodule.span ℚ ((Hs.tan.toAddSubgroup : AddSubgroup _) :
      Set (TanV (fk0 H') (fk1 H') (fg H') (ff H')))).map Ψq = H''.tan.restrictScalars ℚ := by
    rw [K11.span_submodule_coe, ← hTan]; rfl
  have rk3 : rk (Ys ⊓ (Hs.tan.toAddSubgroup ⊔ PerV F.LsH F.MH)) =
      finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) := by
    rw [rk, K11.span_inf_addSubgroup, K11.span_sup_addSubgroup, ← K5d.finrank_map_inj hinjq,
      Submodule.map_inf _ hinjq, Submodule.map_sup, hYmap, hTq, hPmap]
    have hT''q : H''.tan.restrictScalars ℚ ≤ H'.tan.restrictScalars ℚ := fun x hx => hT''T hx
    have : Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω ⊓ H'.tan.restrictScalars ℚ) =
        Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω) := by
      rw [← sup_inf_assoc_of_le _ hT''q, inf_comm _ (H'.tan.restrictScalars ℚ), ← inf_assoc,
        inf_eq_left.mpr hYT]
    rw [this]
  -- numerics
  have hfT' := F.finrank_tan
  have hnP' := F.nPV_eq
  have hnP'' : nPV H'' = nPV Hs := F.nPV_push Hs
  have hle1 : finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) ≤ finrank ℚ Yq :=
    Submodule.finrank_mono inf_le_left
  have hle2 : finrank ℂ ↥(W ⊓ H''.tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
  have hTs := finrank_tan_le Hs
  have htlS := K5d.finrank_torusLie Hs.U
  have hp0 := finrank_gam_fst_le Hs
  have hTsle : finrank ℂ Hs.tan ≤ fk0 H' + fk1 H' + fg H' + ff H' := by
    have := Submodule.finrank_le Hs.tan
    simpa [Module.finrank_prod, add_assoc] using this
  have hδv : Hs.δ = fk0 H' + fk1 H' + fg H' + ff H' - finrank ℂ Hs.tan := rfl
  have hδ0v : Hs.δ0 = fk0 H' - finrank ℂ (Hs.gam.map (LinearMap.fst ℂ (Fin (fk0 H') → ℂ)
    (Fin (ff H') → ℂ))) := rfl
  have hδ1v : Hs.δ1 = finrank ℚ Hs.U := rfl
  have hδ2v : Hs.δ2 = Hs.δ - Hs.δ0 - Hs.δ1 := rfl
  have hδ : (Hs.δ : ℤ) = (finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan := by
    rw [hδv, hfT'', hfT']; omega
  have hδ12 : ((Hs.δ1 + 2 * Hs.δ2 : ℕ) : ℤ) = nPV H' - nPV H'' := by
    rw [hnP'', hnP', nPV, hδ2v, hδv, hδ0v, hδ1v]
    omega
  refine ⟨H'', hT''T, ?_, ?_⟩
  · rw [hWs, hWinf] at hτs
    have := (Nat.cast_lt (α := ℤ)).mpr hτs
    rw [Nat.cast_sub hle2, hδ] at this
    exact this
  · rw [rk1, rk3, rk2, hVs, hWs, hWinf] at hineqs
    have e1 : ((finrank ℚ Yq - finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) +
        Hs.δ1 + 2 * Hs.δ2 : ℕ) : ℤ) = (finrank ℚ Yq : ℤ) -
          finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ Ω)) + (nPV H' - nPV H'') := by
      rw [← hδ12]; push_cast [Nat.cast_sub hle1]; ring
    have e2 : (((fk0 H' + fk1 H' + fg H' + ff H' : ℕ) : ℤ) - finrank ℂ V) = 1 := by
      rw [hfT'] at hVdim; omega
    have e3 : ((Hs.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H''.tan) : ℕ) : ℤ)) =
        ((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
          ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan)) := by
      rw [hδ, Nat.cast_sub hle2]
    have e4 : (((fk1 H' + 2 * (fg H' + ff H') : ℕ) : ℤ) - finrank ℚ ↥(Yq ⊓ Ω)) =
        nPV H' - finrank ℚ ↥(Yq ⊓ Ω) := by
      rw [hnP']; push_cast; ring
    rw [e1, e2, e3, e4, mul_one] at hineqs
    exact hineqs

/-- The transported data satisfy the premises of `Theorem41VecLA` (except (NR)). -/
lemma trans_premises (hM : AlgMat M) (hLA : LiftAlg Ls)
    {H' : SubgroupDataV (d0 := d0) (d1 := d1) Ls M}
    (F : Frame H') (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r))
    (hVT : V ≤ H'.tan) (hVdim : finrank ℂ V + 1 = finrank ℂ H'.tan) (hWV : W ≤ V)
    (hWrat : RatSubV W) (hYfg : Y.FG) (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M)
    (hVfib : V ⊓ fibreV = ⊥) :
    finrank ℂ (V.comap F.Psi) < fk0 H' + fk1 H' + fg H' + ff H' ∧
      W.comap F.Psi ≤ V.comap F.Psi ∧ RatSubV (W.comap F.Psi) ∧ V.comap F.Psi ⊓ fibreV = ⊥ ∧
      (Y.map F.Phi.toAddMonoidHom).FG ∧
      (∀ y ∈ Y.map F.Phi.toAddMonoidHom, y ∈ V.comap F.Psi ∧ y ∈ LamV F.LsH F.MH) ∧
      finrank ℂ (V.comap F.Psi) = finrank ℂ V ∧
      rk (Y.map F.Phi.toAddMonoidHom ⊓ PerV F.LsH F.MH) =
        finrank ℚ ↥(Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) ⊓ OmV d0 d1 Ls M) := by
  classical
  have hinj := F.Psi_injective
  have hrange := F.range_Psi
  have hmap : ∀ S : Submodule ℂ (TanV d0 d1 m r), S ≤ H'.tan → (S.comap F.Psi).map F.Psi = S := by
    intro S hS; rw [Submodule.map_comap_eq, hrange, inf_eq_right.mpr hS]
  have hWT : W ≤ H'.tan := hWV.trans hVT
  have hVs : finrank ℂ (V.comap F.Psi) = finrank ℂ V := by
    rw [← K5d.finrank_map_inj hinj, hmap V hVT]
  have hfT' := F.finrank_tan
  refine ⟨by omega, Submodule.comap_mono hWV, ?_, F.comap_inf_fibreV hVfib,
    K11.fg_map_addSubgroup hYfg _, ?_, hVs, ?_⟩
  · -- rationality of `Psi⁻¹ W = Phi(W)`
    have hWs_eq : W.comap F.Psi = W.map F.Phi := by
      ext x; constructor
      · intro hx; exact ⟨F.Psi x, hx, F.Phi_Psi x⟩
      · rintro ⟨w, hw, rfl⟩
        change F.Psi (F.Phi w) ∈ W
        rw [F.Psi_Phi (hWT hw)]; exact hw
    rw [hWs_eq, hWrat, Submodule.map_span]
    refine ratV_of_span _ ?_
    rintro _ ⟨w, hw, rfl⟩
    exact F.algVecV_Phi hM hw.2
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyV, hyL⟩ := hY y hy
    refine ⟨?_, F.Phi_mem_lamV hM hLA hyL (hVT hyV)⟩
    change F.Psi (F.Phi y) ∈ V
    rw [F.Psi_Phi (hVT hyV)]; exact hyV
  · have hYT : Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) ≤ H'.tan.restrictScalars ℚ :=
      Submodule.span_le.mpr fun y hy => hVT (hY y hy).1
    have hinjq : Function.Injective (F.Psi.restrictScalars ℚ) := hinj
    have hYmap : (Submodule.span ℚ ((Y.map F.Phi.toAddMonoidHom : AddSubgroup _) :
        Set (TanV (fk0 H') (fk1 H') (fg H') (ff H')))).map (F.Psi.restrictScalars ℚ) =
        Submodule.span ℚ (Y : Set (TanV d0 d1 m r)) := by
      rw [Submodule.map_span]; congr 1
      ext v; constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        change F.Psi (F.Phi y) ∈ Y
        rw [F.Psi_Phi (hVT (hY y hy).1)]; exact hy
      · intro hv; exact ⟨F.Phi v, ⟨v, hv, rfl⟩, F.Psi_Phi (hVT (hY v hv).1)⟩
    rw [rk, K11.span_inf_addSubgroup, ← K5d.finrank_map_inj hinjq, Submodule.map_inf _ hinjq,
      hYmap, F.map_span_per, inf_comm (OmV d0 d1 Ls M), ← inf_assoc, inf_eq_left.mpr hYT]

end LSG.W88.V5d
