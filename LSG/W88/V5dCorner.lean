/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dRoy

/-!
# Period ranks, and the (NR) corner of the §5d engine for the vector-extension class

* `finrank_OmV_le`: `dim_ℚ span Ω(G) ≤ d₁ + 2m` (the fibre coordinate of a period is determined
  by its other coordinates);
* `finrank_OmV_inf_ge`: `dim_ℚ (span Ω ∩ T_{G'}) ≥ dim U^⊥ + 2 dim t`;
* `corner_falseV`: if `G' ∩ G₂ = B̃` has no fibre part (`f = 0`), `dim t ≥ 1`, and the periods in
  `V`
  have rank `≥ dim U^⊥ + 2 dim t − 1`, then `V ⊇ T_{B̃} ≠ 0` (contradiction with "no subgroup in
  `V`").
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

variable {d0 d1 m r : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

/-- Description of `span_ℚ Ω`. -/
lemma mem_OmV {x : TanV d0 d1 m r} (hx : x ∈ OmV d0 d1 Ls M) :
    x.1 = 0 ∧ (∃ q : Fin d1 → ℚ, x.2.1 = (2 * Real.pi * I : ℂ) • K11.castL d1 q) ∧
      x.2.2.1 ∈ K5d.latQ Ls ∧ (x.2.2.1 = 0 → x.2.2.2 = 0) := by
  obtain ⟨n, hn, hnx⟩ := K11.exists_nsmul_mem_of_mem_span _ hx
  obtain ⟨h1, h2, h3, h4⟩ := hnx
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsm : ∀ {k : ℕ} (v : Fin k → ℂ), (n • v = 0) → v = 0 := by
    intro k v hv
    rw [← Nat.cast_smul_eq_nsmul ℂ] at hv
    exact (smul_eq_zero.mp hv).resolve_left hnC
  refine ⟨hsm _ h1, ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := torPer_eq h2
    refine ⟨(n : ℚ)⁻¹ • q, ?_⟩
    have hq' : (n : ℚ) • x.2.1 = (2 * Real.pi * I : ℂ) • K11.castL d1 q := by
      rw [Nat.cast_smul_eq_nsmul]; exact hq
    rw [map_smul, smul_comm, ← hq', smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
      one_smul]
  · have h3' : n • x.2.2.1 ∈ (K5d.latQ Ls).toAddSubgroup := Submodule.subset_span h3
    have := K11.mem_span_of_nsmul_mem (K5d.latQ Ls).toAddSubgroup hn h3'
    rwa [show (((K5d.latQ Ls).toAddSubgroup : AddSubgroup (Fin m → ℂ)) : Set (Fin m → ℂ)) =
      (K5d.latQ Ls : Set (Fin m → ℂ)) from rfl, Submodule.span_eq] at this
  · intro hz
    have : (n • x).2.2.2 = 0 := by
      rw [h4]
      have hz' : (n • x).2.2.1 = 0 := by simp [hz]
      rw [hz', etaV_zero', Matrix.mulVec_zero]
    exact hsm _ this

/-- `(a, b, z, s) ↦ (a, b, z)`. -/
noncomputable def forgetS : TanV d0 d1 m r →ₗ[ℚ] Tan d0 d1 m :=
  ((LinearMap.fst ℚ _ _).prod ((LinearMap.fst ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _).prod
    (LinearMap.fst ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _)))

lemma forgetS_inj {x : TanV d0 d1 m r} (hx : x ∈ OmV d0 d1 Ls M) (h0 : forgetS x = 0) : x = 0 := by
  have h1 : x.1 = 0 := congrArg Prod.fst h0
  have h2 : x.2.1 = 0 := congrArg (fun p => p.2.1) h0
  have h3 : x.2.2.1 = 0 := congrArg (fun p => p.2.2) h0
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 ((mem_OmV hx).2.2.2 h3)))

lemma map_forgetS_le : (OmV d0 d1 Ls M).map forgetS ≤ K5d.Ωs Ls d0 d1 := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Submodule.subset_span ⟨hx.1, hx.2.1, hx.2.2.1⟩

lemma ker_forgetS : OmV d0 d1 Ls M ⊓ LinearMap.ker forgetS = ⊥ := by
  rw [eq_bot_iff]; rintro x ⟨hx, hk⟩; exact (Submodule.mem_bot ℚ).mpr (forgetS_inj hx hk)

instance finiteDimensional_OmV : FiniteDimensional ℚ (OmV d0 d1 Ls M) := by
  have : FiniteDimensional ℚ ↥((OmV d0 d1 Ls M).map forgetS) :=
    Submodule.finiteDimensional_of_le map_forgetS_le
  let f := forgetS.domRestrict (OmV d0 d1 Ls M)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx; exact Subtype.ext (forgetS_inj x.2 hx)
  exact Module.Finite.of_injective (f.codRestrict ((OmV d0 d1 Ls M).map forgetS)
    (fun x => ⟨x.1, x.2, rfl⟩)) (fun a b h => hf (congrArg Subtype.val h))

/-- **`dim span Ω(G) ≤ d₁ + 2m`.** -/
lemma finrank_OmV_le : finrank ℚ (OmV d0 d1 Ls M) ≤ d1 + 2 * m := by
  have e := K5d.finrank_map_add_inf_ker forgetS (OmV d0 d1 Ls M)
  rw [ker_forgetS, finrank_bot] at e
  have := Submodule.finrank_mono (map_forgetS_le (d0 := d0) (d1 := d1) (Ls := Ls) (M := M))
  have := K5d.finrank_Ωs_le (d0 := d0) (d1 := d1) Ls
  omega

/-- **`dim (span Ω ∩ T_{G'}) ≥ dim U^⊥ + 2 dim t`.** -/
lemma finrank_OmV_inf_ge (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) :
    finrank ℂ (torusLie H.U) + 2 * finrank ℂ H.t ≤
      finrank ℚ ↥(OmV d0 d1 Ls M ⊓ H.tan.restrictScalars ℚ) := by
  classical
  let inT' : (Fin d1 → ℚ) →ₗ[ℚ] TanV d0 d1 m r :=
    { toFun := fun q => (0, (2 * Real.pi * I : ℂ) • K11.castL d1 q, 0, 0)
      map_add' := fun a b => by simp [smul_add]
      map_smul' := fun c a => by
        refine Prod.ext (by simp) (Prod.ext ?_ (Prod.ext (by simp) (by simp)))
        simp only [map_smul, RingHom.id_apply, Prod.smul_mk, smul_zero]
        rw [smul_comm] }
  let inE' : (Fin m → ℂ) →ₗ[ℚ] TanV d0 d1 m r :=
    { toFun := fun z => (0, 0, z, 0)
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  set A := (K11.annQ H.U).map inT' with hA
  set B := (K5d.latT Ls H.t).map inE' with hB
  -- `A ⊂ Ω ∩ T`
  have hAle : A ≤ OmV d0 d1 Ls M ⊓ H.tan.restrictScalars ℚ := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨torPer_mem q, ?_⟩
    change ((0 : Fin d0 → ℂ), (2 * Real.pi * I : ℂ) • K11.castL d1 q, (0 : Fin m → ℂ),
      (0 : Fin r → ℂ)) ∈ H.tan
    exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, K5d.castL_mem_torusLie_iff.mpr hq,
      rfl⟩)
  -- `pr_z (Ω ∩ T) ⊇ latT t`
  let pz : TanV d0 d1 m r →ₗ[ℚ] (Fin m → ℂ) :=
    LinearMap.fst ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _
  let pb : TanV d0 d1 m r →ₗ[ℚ] (Fin d1 → ℂ) := LinearMap.fst ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _
  set Z := OmV d0 d1 Ls M ⊓ H.tan.restrictScalars ℚ with hZ
  have : FiniteDimensional ℚ Z := Submodule.finiteDimensional_of_le inf_le_left
  have hlat : K5d.latT Ls H.t ≤ Z.map pz := by
    rw [K5d.latT, Submodule.span_le]
    intro z hz
    refine ⟨(0, 0, z, M.mulVec (etaV Ls z)), ⟨Submodule.subset_span ⟨rfl, fun i => ⟨0, by simp⟩,
      hz.2, rfl⟩, ?_⟩, rfl⟩
    change ((0 : Fin d0 → ℂ), (0 : Fin d1 → ℂ), z, M.mulVec (etaV Ls z)) ∈ H.tan
    refine Submodule.mem_sup_right ⟨(z, M.mulVec (etaV Ls z)), ⟨(z, etaV Ls z),
      Submodule.subset_span ⟨hz.1, hz.2, rfl⟩, rfl⟩, rfl⟩
  have hAker : A ≤ Z ⊓ LinearMap.ker pz := by
    intro x hx
    refine ⟨hAle hx, ?_⟩
    obtain ⟨q, -, rfl⟩ := hx
    rfl
  have hAdim : finrank ℚ A = finrank ℂ (torusLie H.U) := by
    have hinj : Function.Injective inT' := by
      intro a b h
      have := congrArg (fun p => p.2.1) h
      exact K11.castL_injective d1 (smul_right_injective _ K11.two_pi_I_ne_zero this)
    rw [hA, K5d.finrank_map_inj hinj]
    have h1 := K11.finrank_annQ H.U
    have h2 := K5d.finrank_torusLie H.U
    omega
  have e := K5d.finrank_map_add_inf_ker pz Z
  have h1 := Submodule.finrank_mono hlat
  have h2 := Submodule.finrank_mono hAker
  have h3 := K5d.two_mul_le_finrank_latT Ls H.t_ab
  omega

/-- **The (NR) corner** of the §5d engine: `f = 0` (no fibre part in `G' ∩ G₂`), `dim t ≥ 1`, and a
`ℚ`-space `X ⊂ span Ω ∩ T_{G'} ∩ V` of dimension `≥ dim U^⊥ + 2 dim t − 1`. Then `V ⊇ T_{B̃}`. -/
theorem corner_falseV {H' : SubgroupDataV (d0 := d0) (d1 := d1) Ls M} (F : Frame H')
    (hf : ff H' = 0) (hg : 1 ≤ fg H') (V : Submodule ℂ (TanV d0 d1 m r))
    (hno : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan ≤ V → H.tan = ⊥)
    (X : Submodule ℚ (TanV d0 d1 m r)) (hXΩ : X ≤ OmV d0 d1 Ls M ⊓ H'.tan.restrictScalars ℚ)
    (hXV : X ≤ V.restrictScalars ℚ)
    (hX : finrank ℂ (torusLie H'.U) + 2 * fg H' ≤ finrank ℚ X + 1) : False := by
  classical
  have : FiniteDimensional ℚ X := Submodule.finiteDimensional_of_le (hXΩ.trans inf_le_left)
  let p₂ : TanV d0 d1 m r →ₗ[ℚ] (Fin d1 → ℂ) := LinearMap.fst ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _
  let p₃ : TanV d0 d1 m r →ₗ[ℚ] (Fin m → ℂ) :=
    LinearMap.fst ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _
  let g2π : (Fin d1 → ℚ) →ₗ[ℚ] (Fin d1 → ℂ) :=
    (2 * Real.pi * I : ℂ) • (K11.castL d1).restrictScalars ℚ
  -- the toric image has dimension `≤ dim U^⊥`
  have himg : X.map p₂ ≤ (K11.annQ H'.U).map g2π := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨-, ⟨q, hq⟩, -, -⟩ := mem_OmV (hXΩ hx).1
    have hb : x.2.1 ∈ torusLie H'.U := (tan_le_prod H' (hXΩ hx).2).2.1
    rw [hq] at hb
    exact ⟨q, K5d.castL_mem_torusLie_iff.mp hb, by simp [g2π, p₂, hq]⟩
  have hgdim : finrank ℚ ↥((K11.annQ H'.U).map g2π) ≤ finrank ℂ (torusLie H'.U) := by
    have h1 := K11.finrank_annQ H'.U
    have h2 := K5d.finrank_torusLie H'.U
    have h3 := Submodule.finrank_map_le g2π (K11.annQ H'.U)
    omega
  set K₁ := X ⊓ LinearMap.ker p₂ with hK₁
  have : FiniteDimensional ℚ K₁ := Submodule.finiteDimensional_of_le inf_le_left
  have hK₁dim : finrank ℚ X ≤ finrank ℚ K₁ + finrank ℂ (torusLie H'.U) := by
    have e1 := K5d.finrank_map_add_inf_ker p₂ X
    rw [← hK₁] at e1
    have e2 := Submodule.finrank_mono himg
    omega
  set K := K₁.map p₃ with hK
  have hKinj : K₁ ⊓ LinearMap.ker p₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxX, hx2⟩, hx3⟩
    rw [Submodule.mem_bot]
    have h := mem_OmV (hXΩ hxX).1
    have h3 : x.2.2.1 = 0 := hx3
    exact Prod.ext h.1 (Prod.ext hx2 (Prod.ext h3 (h.2.2.2 h3)))
  have hKdim : finrank ℚ K = finrank ℚ K₁ := by
    have := K5d.finrank_map_add_inf_ker p₃ K₁
    rw [hKinj, finrank_bot] at this; omega
  have hKlat : K ≤ K5d.latQ Ls := by
    rintro _ ⟨x, ⟨hxX, -⟩, rfl⟩
    exact (mem_OmV (hXΩ hxX).1).2.2.1
  have hKt : K ≤ H'.t.restrictScalars ℚ := by
    rintro _ ⟨x, ⟨hxX, -⟩, rfl⟩
    exact F.mem_t_of_tan (hXΩ hxX).2
  -- the map `L z = (0, 0, lift(z ∘ ι), M κ_t(z ∘ ι))`
  let L : (Fin m → ℂ) →ₗ[ℂ] TanV d0 d1 m r :=
    (0 : (Fin m → ℂ) →ₗ[ℂ] (Fin d0 → ℂ)).prod ((0 : (Fin m → ℂ) →ₗ[ℂ] (Fin d1 → ℂ)).prod
      ((F.c.lift ∘ₗ LSG.CM.proj F.c.ι).prod (M.mulVecLin ∘ₗ F.K ∘ₗ LSG.CM.proj F.c.ι)))
  have hL : ∀ z, L z =
      (0, 0, F.c.lift (LSG.CM.proj F.c.ι z), M.mulVec (F.K (LSG.CM.proj F.c.ι z))) :=
    fun z => rfl
  have hσ : ∀ σ : Fin (ff H') → ℂ, σ = 0 := fun σ => funext fun i => absurd i.2 (by omega)
  have hxform : ∀ x ∈ K₁, x = L (p₃ x) := by
    rintro x ⟨hxX, hx2⟩
    have hT := (hXΩ hxX).2
    have h := mem_OmV (hXΩ hxX).1
    have hx2' : x.2.1 = 0 := hx2
    conv_lhs => rw [← F.Psi_Phi hT]
    rw [Frame.Psi_apply, Frame.Phi_apply, hL, h.1, hx2', hσ (F.Fl _)]
    simp [p₃]
  -- `span_ℂ K = t`
  set S := Submodule.span ℂ (K : Set (Fin m → ℂ)) with hS
  have hSt : S ≤ H'.t := Submodule.span_le.mpr fun z hz => hKt hz
  have hreal : finrank ℚ K ≤ 2 * finrank ℂ S := by
    refine (K5d.finrank_le_real Ls K hKlat).trans ?_
    rw [← K5d.finrank_real_restrict]
    refine Submodule.finrank_mono ?_
    rw [Submodule.span_le]; intro z hz; exact Submodule.subset_span hz
  have hSdim : finrank ℂ S ≤ finrank ℂ H'.t := Submodule.finrank_mono hSt
  have hSeq : S = H'.t := Submodule.eq_of_le_of_finrank_eq hSt (by simp only [fg] at hX; omega)
  -- `L(t) ⊂ V`
  have hLV : H'.t.map L ≤ V := by
    rw [← hSeq, hS, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨z, ⟨x, hxK₁, rfl⟩, rfl⟩
    rw [← hxform x hxK₁]
    exact hXV hxK₁.1
  -- the subgroup `0 × 0 × B̃`
  have hVf : Vf H' = ⊥ := Submodule.finrank_eq_zero.mp hf
  have hgam : RatPair (⊥ : Submodule ℂ ((Fin d0 → ℂ) × (Fin r → ℂ))) :=
    le_antisymm bot_le (Submodule.span_le.mpr fun _ hw => hw.1)
  let Hab : SubgroupDataV (d0 := d0) (d1 := d1) Ls M :=
    { U := ⊤, t := H'.t, gam := ⊥, gam_rat := hgam, t_ab := H'.t_ab }
  have hle : Hab.tan ≤ V := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨γ, hγ, rfl⟩
      rw [(Submodule.mem_bot ℂ).mp hγ, map_zero]; exact V.zero_mem
    · rintro _ ⟨v, hv, rfl⟩
      change v ∈ torusLie (⊤ : Submodule ℚ (Fin d1 → ℚ)) at hv
      rw [K5d.torusLie_top, Submodule.mem_bot] at hv
      rw [hv, map_zero]; exact V.zero_mem
    · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have he := perTanId_eq F.c H'.t_ab hp
      have hMN : M.mulVec (F.N (LSG.CM.proj F.c.ι p.2)) = 0 := by
        have := F.MN_mem_Vf (LSG.CM.proj F.c.ι p.2)
        rwa [hVf, Submodule.mem_bot] at this
      have : g2Incl ((LinearMap.prodMap LinearMap.id M.mulVecLin) p) =
          L (F.c.lift (LSG.CM.proj F.c.ι p.1)) := by
        conv_lhs => rw [he]
        rw [hL, F.c.proj_lift]
        simp [Matrix.mulVec_add, hMN]
      rw [this]
      exact hLV ⟨_, F.c.lift_mem _, rfl⟩
  have hbot := hno Hab hle
  -- but `T_{B̃} ≠ 0`
  set μ₀ : Fin (fg H') → ℂ := Pi.single ⟨0, hg⟩ 1
  have hmem : g2Incl ((LinearMap.prodMap LinearMap.id M.mulVecLin)
      (F.c.lift μ₀, F.K μ₀ + F.N 0)) ∈ Hab.tan :=
    Submodule.mem_sup_right ⟨_, ⟨_, mem_perTanId_lift F.c H'.t_ab μ₀ 0, rfl⟩, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  have h3 : F.c.lift μ₀ = 0 := congrArg (fun p => p.2.2.1) hmem
  have : μ₀ = 0 := by rw [← F.c.proj_lift μ₀, h3, map_zero]
  have h1 := congrFun this ⟨0, hg⟩
  simp [μ₀] at h1

end LSG.W88.V5d
