/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dFrame2

/-!
# Subgroups of `G_H` pushed into `G`, and `LiftAlg` for sub-families of curves

* `map_perQ_perTanId`: `perQ(T((B_s)^♮)) = T((lift B_s)^♮)` for an abelian subvariety `B_s` of `∏ₖ
  E_{ι k}`;
* `Frame.push`: a member `H_s` of `G_H` gives the member `push H_s` of `G` with
  `T_{push H_s} = Psi(T_{H_s})` (`push_tan`), `dim pr₀ Γ` and `dim U^⊥` unchanged;
* `liftAlg_comp`: `LiftAlg Ls → LiftAlg (Ls ∘ ι)` for injective `ι` (extension by zero), and
  `chart_ι_injective`.
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

/-! ### `perQ` maps `T(B_s^♮)` onto `T((lift B_s)^♮)` -/

section PerPush

variable {m : ℕ} {Ls : Fin m → PeriodPair} {t : Submodule ℂ (Fin m → ℂ)} (c : LSG.CM.Chart t)
  (ht : IsAbelianTangent Ls t)

theorem map_perQ_perTanId (ts : Submodule ℂ (Fin (finrank ℂ t) → ℂ)) :
    (perTanId (Ls ∘ c.ι) ts).map (perQ c ht) = perTanId Ls (ts.map c.lift) := by
  apply le_antisymm
  · rw [perTanId, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨⟨μ, y⟩, ⟨hμ, hlat, hy⟩, rfl⟩
    simp only at hμ hlat hy
    subst hy
    obtain ⟨n, hn, hl⟩ := c.exists_nsmul_lift_mem ht hlat
    have hmem : ((c.lift (n • μ), etaV Ls (c.lift (n • μ))) : (Fin m → ℂ) × (Fin m → ℂ)) ∈
        perTanId Ls (ts.map c.lift) :=
      Submodule.subset_span ⟨⟨n • μ, ts.smul_of_tower_mem n hμ, rfl⟩, hl, rfl⟩
    have hP : ((c.lift (n • μ), etaV Ls (c.lift (n • μ))) : (Fin m → ℂ) × (Fin m → ℂ)) ∈
        perTanId Ls t := Submodule.subset_span ⟨c.lift_mem _, hl, rfl⟩
    have h2 : ((c.lift (n • μ), etaV Ls (c.lift (n • μ))) : (Fin m → ℂ) × (Fin m → ℂ)) =
        (n : ℂ) • perQ c ht (μ, etaV (Ls ∘ c.ι) μ) := by
      conv_lhs => rw [← perQ_perP c ht hP]
      rw [perP_apply, proj_etaV, c.proj_lift, ← map_smul]
      congr 1
      refine Prod.ext ?_ ?_
      · change n • μ = (n : ℂ) • μ; rw [Nat.cast_smul_eq_nsmul]
      · change etaV (Ls ∘ c.ι) (n • μ) = (n : ℂ) • etaV (Ls ∘ c.ι) μ
        rw [← natCast_zsmul, etaV_zsmul _ hlat, natCast_zsmul, Nat.cast_smul_eq_nsmul]
    have hNC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have : perQ c ht (μ, etaV (Ls ∘ c.ι) μ) = (n : ℂ)⁻¹ •
        ((c.lift (n • μ), etaV Ls (c.lift (n • μ))) : (Fin m → ℂ) × (Fin m → ℂ)) := by
      rw [h2, smul_smul, inv_mul_cancel₀ hNC, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ hmem
  · rw [perTanId, Submodule.span_le]
    rintro ⟨l, w⟩ ⟨⟨μ, hμ, hlμ⟩, hlat, hw⟩
    simp only at hlμ hlat hw
    subst hw hlμ
    have hP : ((c.lift μ, etaV Ls (c.lift μ)) : (Fin m → ℂ) × (Fin m → ℂ)) ∈ perTanId Ls t :=
      Submodule.subset_span ⟨c.lift_mem μ, hlat, rfl⟩
    refine ⟨(μ, etaV (Ls ∘ c.ι) μ), Submodule.subset_span ⟨hμ, fun k => ?_, rfl⟩, ?_⟩
    · have := hlat (c.ι k); rwa [c.lift_apply] at this
    · conv_rhs => rw [← perQ_perP c ht hP]
      rw [perP_apply, proj_etaV, c.proj_lift]

end PerPush

/-! ### Pushing members of `G_H` into `G` -/

variable {d0 d1 m r : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

namespace Frame

variable {H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M} (F : Frame H)

/-- `(a, σ) ↦ (A a, G a + Fm σ)`. -/
noncomputable def Lgam :
    ((Fin (fk0 H) → ℂ) × (Fin (ff H) → ℂ)) →ₗ[ℂ] ((Fin d0 → ℂ) × (Fin r → ℂ)) :=
  (F.A ∘ₗ LinearMap.fst ℂ _ _).prod (F.G ∘ₗ LinearMap.fst ℂ _ _ + F.Fm ∘ₗ LinearMap.snd ℂ _ _)

lemma Lgam_apply (p : (Fin (fk0 H) → ℂ) × (Fin (ff H) → ℂ)) :
    F.Lgam p = (F.A p.1, F.G p.1 + F.Fm p.2) := rfl

lemma ratPair_map_Lgam {Γs : Submodule ℂ ((Fin (fk0 H) → ℂ) × (Fin (ff H) → ℂ))} (h : RatPair Γs) :
    RatPair (Γs.map F.Lgam) := by
  have e : Γs.map F.Lgam = Submodule.span ℂ (F.Lgam '' {w | w ∈ Γs ∧ AlgPair w}) := by
    conv_lhs => rw [h]
    rw [Submodule.map_span]
  rw [e]
  refine ratPair_of_span _ ?_
  rintro _ ⟨w, hw, rfl⟩
  rw [Lgam_apply]
  exact ⟨F.algA _ hw.2.1, algVec_add (F.algG _ hw.2.1) (F.algFm _ hw.2.2)⟩

/-- **The member of `G` pushed from a member `H_s` of `G_H`.** -/
noncomputable def push (Hs : SubgroupDataV (d0 := fk0 H) (d1 := fk1 H) F.LsH F.MH) :
    SubgroupDataV (d0 := d0) (d1 := d1) Ls M where
  U := K11.annQ ((K11.annQ Hs.U).map F.C.mulVecLin)
  t := Hs.t.map F.c.lift
  gam := Hs.gam.map F.Lgam
  gam_rat := F.ratPair_map_Lgam Hs.gam_rat
  t_ab := F.c.isAbelianTangent_map H.t_ab Hs.t_ab

variable (Hs : SubgroupDataV (d0 := fk0 H) (d1 := fk1 H) F.LsH F.MH)

lemma torusLie_push : torusLie (F.push Hs).U = (torusLie Hs.U).map (K11.cm F.C).mulVecLin := by
  change torusLie (K11.annQ ((K11.annQ Hs.U).map F.C.mulVecLin)) = _
  rw [K5d.torusLie_eq_annC, ← K11.cspan_eq_annC, K5d.torusLie_eq_annC, K11.annC_eq_cspan,
    K11.map_cspan]

/-- **`T_{push H_s} = Psi(T_{H_s})`.** -/
theorem push_tan : (F.push Hs).tan = Hs.tan.map F.Psi := by
  simp only [SubgroupDataV.tan, Submodule.map_sup]
  congr 1
  · congr 1
    · change (Hs.gam.map F.Lgam).map vecIncl = _
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      refine LinearMap.ext fun p => ?_
      simp only [LinearMap.comp_apply, Lgam_apply, vecIncl_apply, Psi_apply, map_zero,
        Matrix.mulVec_zero, add_zero]
    · rw [F.torusLie_push, ← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, torIncl_apply, Psi_apply, map_zero, Matrix.mulVec_zero,
        add_zero, Matrix.mulVecLin_apply]
  · change (perTan Ls M (Hs.t.map F.c.lift)).map g2Incl = _
    rw [perTan, perTan, ← map_perQ_perTanId F.c H.t_ab, ← Submodule.map_comp,
      ← Submodule.map_comp, ← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      g2Incl_apply, Psi_apply, map_zero, Matrix.mulVec_zero, zero_add, Matrix.mulVecLin_apply,
      F.Fm_MH]
    obtain ⟨μ, y⟩ := p
    rw [perQ_apply]
    simp [Matrix.mulVec_add]

lemma push_gam_fst : (F.push Hs).gam.map (LinearMap.fst ℂ _ _) =
    (Hs.gam.map (LinearMap.fst ℂ _ _)).map F.A := by
  change (Hs.gam.map F.Lgam).map _ = _
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  rfl

lemma A_injective : Function.Injective F.A := fun x y h => by
  rw [← F.BA x, ← F.BA y, h]

lemma finrank_push_gam_fst : finrank ℂ ((F.push Hs).gam.map (LinearMap.fst ℂ _ _)) =
    finrank ℂ (Hs.gam.map (LinearMap.fst ℂ _ _)) := by
  rw [F.push_gam_fst, K5d.finrank_map_inj F.A_injective]

lemma finrank_torusLie_push : finrank ℂ (torusLie (F.push Hs).U) = finrank ℂ (torusLie Hs.U) := by
  rw [F.torusLie_push, K5d.finrank_map_inj (K11.cm_injective F.DC)]

lemma finrank_push_tan : finrank ℂ (F.push Hs).tan = finrank ℂ Hs.tan := by
  rw [F.push_tan, K5d.finrank_map_inj F.Psi_injective]

lemma push_tan_le : (F.push Hs).tan ≤ H.tan := by
  rw [F.push_tan]; rintro _ ⟨x, -, rfl⟩; exact F.Psi_mem_tan x

end Frame

/-! ### `LiftAlg` for sub-families -/

section Incl

variable {g : ℕ} (ι : Fin g → Fin m)

/-- Extension by zero along `ι`. -/
noncomputable def inclL : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ) where
  toFun u j := ∑ k, if ι k = j then u k else 0
  map_add' u v := by
    funext j
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
  map_smul' c u := by funext j; simp [Finset.mul_sum]

variable {ι}

lemma inclL_apply_ι (hι : Function.Injective ι) (u : Fin g → ℂ) (k : Fin g) :
    inclL ι u (ι k) = u k := by
  change ∑ k', (if ι k' = ι k then u k' else 0) = u k
  rw [Finset.sum_eq_single k (fun b _ hb => by
    have : ι b ≠ ι k := fun h => hb (hι h)
    simp [this]) (by simp)]
  simp

lemma inclL_apply_of (u : Fin g → ℂ) {j : Fin m} (hj : ∀ k, ι k ≠ j) : inclL ι u j = 0 := by
  change ∑ k, (if ι k = j then u k else 0) = 0
  exact Finset.sum_eq_zero fun k _ => by simp [hj k]

lemma proj_inclL (hι : Function.Injective ι) (u : Fin g → ℂ) : LSG.CM.proj ι (inclL ι u) = u := by
  funext k; exact inclL_apply_ι hι u k

lemma inclL_cases (hι : Function.Injective ι) (u : Fin g → ℂ) (j : Fin m) :
    (∃ k, ι k = j ∧ inclL ι u j = u k) ∨ inclL ι u j = 0 := by
  by_cases h : ∃ k, ι k = j
  · obtain ⟨k, rfl⟩ := h; exact Or.inl ⟨k, rfl, inclL_apply_ι hι u k⟩
  · push Not at h; exact Or.inr (inclL_apply_of u h)

lemma latVec_inclL (hι : Function.Injective ι) {u : Fin g → ℂ} (hu : LatVec (Ls ∘ ι) u) :
    LatVec Ls (inclL ι u) := fun j => by
  rcases inclL_cases hι u j with ⟨k, rfl, h⟩ | h
  · rw [h]; exact hu k
  · rw [h]; exact (Ls j).lattice.zero_mem

/-- **`LiftAlg` is inherited by sub-families of curves.** -/
theorem liftAlg_comp (hι : Function.Injective ι) (h : LiftAlg Ls) : LiftAlg (Ls ∘ ι) := by
  intro ts hts z hz hzc
  set T := ts.map (inclL ι) with hT
  have hTab : IsAbelianTangent Ls T := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : u ∈ ts.restrictScalars ℝ := hu
      rw [hts] at hu'
      have hmap := Submodule.mem_map_of_mem (f := (inclL ι).restrictScalars ℝ) hu'
      rw [← Submodule.span_image] at hmap
      refine (Submodule.span_le.mpr ?_) hmap
      rintro _ ⟨v, ⟨hv, hvl⟩, rfl⟩
      exact Submodule.subset_span ⟨⟨v, hv, rfl⟩, latVec_inclL hι hvl⟩
    · rw [Submodule.span_le]; exact fun x hx => hx.1
  have hzT : inclL ι z ∈ T := ⟨z, hz, rfl⟩
  have hzc' : ∀ j, inclL ι z j ∈ (Ls j).lattice ∨
      IsAlgebraic ℚ ((Ls j).weierstrassP (inclL ι z j)) := fun j => by
    rcases inclL_cases hι z j with ⟨k, rfl, h⟩ | h
    · rw [h]; exact hzc k
    · rw [h]; exact Or.inl (Ls j).lattice.zero_mem
  obtain ⟨w, hw, hwa⟩ := h T hTab (inclL ι z) hzT hzc'
  have hle : (perTanId Ls T).map (LinearMap.prodMap (LSG.CM.proj ι) (LSG.CM.proj ι)) ≤
      perTanId (Ls ∘ ι) ts := by
    rw [perTanId, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨⟨l, e⟩, ⟨⟨u, hu, rfl⟩, hlat, he⟩, rfl⟩
    simp only at hlat he
    subst he
    refine Submodule.subset_span ⟨?_, fun k => ?_, rfl⟩
    · simp only [LinearMap.prodMap_apply, proj_inclL hι]; exact hu
    · simp only [LinearMap.prodMap_apply, proj_inclL hι]
      have := hlat (ι k); rwa [inclL_apply_ι hι] at this
  refine ⟨LSG.CM.proj ι w, ?_, ?_⟩
  · have := hle ⟨_, hw, rfl⟩
    simpa [LinearMap.prodMap_apply, proj_inclL hι] using this
  · have e : LSG.CM.proj ι w - zetaV (Ls ∘ ι) z = LSG.CM.proj ι (w - zetaV Ls (inclL ι z)) := by
      funext k; simp [zetaV, inclL_apply_ι hι]
    rw [e]; exact algLin_proj ι _ hwa

end Incl

/-- Chart coordinates are distinct. -/
lemma chart_ι_injective {t : Submodule ℂ (Fin m → ℂ)} (c : LSG.CM.Chart t) :
    Function.Injective c.ι := by
  intro k k' hkk
  by_contra hne
  have h1 := c.lift_apply (Pi.single k 1) k
  have h2 := c.lift_apply (Pi.single k 1) k'
  rw [← hkk, h1] at h2
  simp [Ne.symm hne] at h2

end LSG.W88.V5d
