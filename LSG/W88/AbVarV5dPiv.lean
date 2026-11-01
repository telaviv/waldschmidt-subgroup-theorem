/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarV5dCore
import LSG.W88.K5dTrans
import LSG.MEB.Rational

/-!
# M2.7c: Theorem 4.1 for a member with `t ≠ 0`, by one transport (frames + pivot)

**`trans41AV_ne`**: `Trans41AV An H′` for a member `H′` with `t′ ≠ 0`, from `Thm41FamV` (Theorem 4.1 for the pivot
subfamily `B ∘ e` with push-out matrix `M′ = M A`). Under `PerTanFib`, `T_{H′} = pr₀ Γ × U^⊥ × t × ℂ^r`
(`mem_tan_iff_of_ne`); the transport is

  `ι (a, b, μ, s) = (A₀ a, C b, σ μ, s) : TanAV k₀ k₁ r (B ∘ e) → TanAV d₀ d₁ r B`,

`A₀` a `ℚ̄`-frame of `pr₀ Γ`, `C` a `ℚ`-frame of `annQ U`, `σ = (z ↦ z ∘ e)|_t⁻¹` the inverse pivot
(`LSG.MEB.pivot`), with left inverse `π (u, v, z, s) = (B₀ u, D v, z ∘ e, s)`. `PerTanPiv` gives `M η(z) = M′ η(z ∘ e)`
on the periods of `t`, so `π` preserves `LamAV` (`sPart` is unchanged) and `M′` is onto (`PerTanFib`). Periods:
`ι(Ω′) = Ω ∩ T_{H′}` (the pivot finite index, as `thm41SubAtB_of`). Members of `G_{H′}` push forward to members
(`(A₀ × id) Γ_s`, `annQ (C annQ U_s)`, `σ t_s`; the `T(B̃)` parts match by `perTanA_eq_prod`, using
`PerTanFib (B ∘ e) M′`). Numerics: `d₂` and `dim U^⊥` are preserved, `dim G_{H′} = dim T_{H′}`.
-/

open Complex Module Submodule LSG.AuxAV LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.W88.AVS

open LSG.MEB (IsRatSub perAb)
open LSG.MEBV (VBlock perTanId perBase)
open LSG.W88.Vec (RatPair AlgPair AlgMat)
open K5d (cmK algVec_cmK_mulVec algVec_cm_mulVec exp_cm_mulVec mulVec_left_invK exists_algFrame
  finrank_map_inj torusLie_eq_annC castL_mem_torusLie_iff finrank_torusLie)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {M : Matrix (Fin r) (Fin m) ℂ}

/-! ### Toric and block periods -/

/-- The toric inclusion `q ↦ (0, 2πi q, 0, 0)`. -/
def inTV (d₀ d₁ r : ℕ) (B : Fin m → VBlock) : (Fin d₁ → ℚ) →ₗ[ℚ] TanAV d₀ d₁ r B where
  toFun q := (0, (2 * Real.pi * I : ℂ) • K11.castL d₁ q, 0, 0)
  map_add' a b := by
    refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
    simp [smul_add]
  map_smul' c a := by
    refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
    simp only [map_smul, RingHom.id_apply, Prod.smul_snd, Prod.smul_fst]
    rw [smul_comm]

lemma inTV_apply (q : Fin d₁ → ℚ) :
    inTV d₀ d₁ r B q = (0, (2 * Real.pi * I : ℂ) • K11.castL d₁ q, 0, 0) := rfl

lemma inTV_mem_OmAV (q : Fin d₁ → ℚ) : inTV d₀ d₁ r B q ∈ OmAV d₀ d₁ B M := by
  classical
  rw [show q = ∑ i, q i • (Pi.single i 1 : Fin d₁ → ℚ) by
    funext j; simp [Finset.sum_apply, Pi.single_apply], map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_smul]
  refine smul_mem _ _ (subset_span ⟨rfl, fun j => ?_, fun k => (B k).base.per.zero_mem, ?_⟩)
  · by_cases h : j = i
    · subst h; exact ⟨1, by simp [inTV_apply, K11.castL]⟩
    · exact ⟨0, by simp [inTV_apply, K11.castL, Pi.single_apply, h]⟩
  · change (0 : Fin r → ℂ) = M.mulVec (etaB B 0)
    rw [etaB_zero', Matrix.mulVec_zero]

lemma blk_mem_perAVf {z : ∀ k, Fin (B k).g → ℂ} (hz : ∀ k, z k ∈ (B k).base.per) :
    ((0, 0, z, M.mulVec (etaB B z)) : TanAV d₀ d₁ r B) ∈ PerAVf d₀ d₁ B M :=
  ⟨rfl, fun _ => ⟨0, by simp⟩, hz, rfl⟩

lemma etaB_nsmul {z : ∀ k, Fin (B k).g → ℂ} (hz : ∀ k, z k ∈ (B k).base.per) (N : ℕ) :
    etaB B (N • z) = N • etaB B z := by
  induction N with
  | zero => simp [etaB_zero']
  | succ N ih =>
    have h : etaB B ((N + 1) • z) = etaB B (N • z) + etaB B z := funext fun k => by
      rw [succ_nsmul]
      exact (B k).η_add ((B k).base.per.nsmul_mem (hz k) N) (hz k)
    rw [h, ih, succ_nsmul]

lemma isAlgebraic_matrix_mul {a b c : ℕ} {P : Matrix (Fin a) (Fin b) ℂ} {Q : Matrix (Fin b) (Fin c) ℂ}
    (hP : AlgMat P) (hQ : AlgMat Q) : AlgMat (P * Q) := fun i j => by
  rw [Matrix.mul_apply]
  exact (IsIntegral.sum _ fun k _ => (hP i k).isIntegral.mul (hQ k j).isIntegral).isAlgebraic

/-- `ι (a, b, μ, s) = (A a, C b, σ μ, s)`. -/
def iotaAV {n k0 k1 : ℕ} {B' : Fin n → VBlock} (A : Matrix (Fin d₀) (Fin k0) ℂ) (C : Matrix (Fin d₁) (Fin k1) ℂ)
    (σ : (∀ i, Fin (B' i).g → ℂ) →ₗ[ℂ] (∀ k, Fin (B k).g → ℂ)) : TanAV k0 k1 r B' →ₗ[ℂ] TanAV d₀ d₁ r B where
  toFun x := (A.mulVec x.1, C.mulVec x.2.1, σ x.2.2.1, x.2.2.2)
  map_add' x y := by ext <;> simp [Matrix.mulVec_add]
  map_smul' c x := by ext <;> simp [Matrix.mulVec_smul]

/-- `π (u, v, z, s) = (A′ u, C′ v, p z, s)`. -/
def piAV {n k0 k1 : ℕ} {B' : Fin n → VBlock} (A : Matrix (Fin k0) (Fin d₀) ℂ) (C : Matrix (Fin k1) (Fin d₁) ℂ)
    (p : (∀ k, Fin (B k).g → ℂ) →ₗ[ℂ] (∀ i, Fin (B' i).g → ℂ)) : TanAV d₀ d₁ r B →ₗ[ℂ] TanAV k0 k1 r B' where
  toFun x := (A.mulVec x.1, C.mulVec x.2.1, p x.2.2.1, x.2.2.2)
  map_add' x y := by ext <;> simp [Matrix.mulVec_add]
  map_smul' c x := by ext <;> simp [Matrix.mulVec_smul]

/-! ### Pivot data -/

/-- **The pushed tangent is rational** (finite index of the pivot image). -/
lemma isRatSub_map_sigma {n : ℕ} {B' : Fin n → VBlock}
    (σ : (∀ i, Fin (B' i).g → ℂ) →ₗ[ℂ] (∀ k, Fin (B k).g → ℂ))
    (hfin : ∀ w ∈ perBase B', ∃ N : ℕ, 0 < N ∧ σ (N • w) ∈ perBase B)
    {ts : Submodule ℂ (∀ i, Fin (B' i).g → ℂ)} (hts : IsRatSub (perBase B') ts) :
    IsRatSub (perBase B) (ts.map σ) := by
  unfold IsRatSub at hts ⊢
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ (ts.restrictScalars ℝ : Submodule ℝ _) := hw
    rw [hts] at hw'
    have hle : (span ℝ {z | z ∈ ts ∧ z ∈ perBase B'}).map (σ.restrictScalars ℝ) ≤
        span ℝ {z | z ∈ ts.map σ ∧ z ∈ perBase B} := by
      rw [map_span, span_le]
      rintro _ ⟨w', ⟨hw't, hw'P⟩, rfl⟩
      obtain ⟨N, hN, hNw⟩ := hfin w' hw'P
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have e : σ w' = (N : ℝ)⁻¹ • σ (N • w') := by
        rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN', one_smul]
      change σ w' ∈ _
      rw [e]
      exact smul_mem _ _ (subset_span ⟨⟨N • w', ts.nsmul_mem hw't N, rfl⟩, hNw⟩)
    exact hle ⟨w, hw', rfl⟩
  · rw [span_le]; exact fun z hz => hz.1

lemma perTanA_bot' : perTanA B M (⊥ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨p, hp, rfl⟩
  have hp1 : p.1 = 0 := (mem_bot ℂ).mp (perTanId_le_fst ⊥ hp)
  have hle : perTanId B (⊥ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) ≤ ⊥ := by
    rw [perTanId, span_le]
    rintro q ⟨hq1, hq2⟩
    have h0 : q.1 = 0 := (mem_bot ℂ).mp hq1
    have h2 : q.2 = 0 := funext fun k => by
      have := (hq2 k).2
      change q.2 k = (B k).η (q.1 k) at this
      change q.2 k = 0
      rw [this, h0]; exact (B k).η_zero
    exact (mem_bot ℂ).mpr (Prod.ext h0 h2)
  have := (mem_bot ℂ).mp (hle hp)
  rw [this]; simp

set_option maxHeartbeats 4000000 in
-- the transport of all the data
/-- **Theorem 4.1 for a member with `t ≠ 0`, in the coordinates of `G`.** -/
theorem trans41AV_ne (An : ∀ k, VBlockAn (B k)) (hF : PerTanFib B M) (hP : PerTanPiv B)
    (hMa : AlgMat M) (h41 : Thm41FamV An r) (H' : SubgroupDataAV d₀ d₁ B M) (hne : H'.t ≠ ⊥) :
    Trans41AV An H' := by
  classical
  intro V W Y hVT hVdim hWV hWrat hYfg hY hTor hNR
  replace hNR := hNR.resolve_right hne
  -- frames
  set Γ0 := H'.gam.map (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin r → ℂ)) with hΓ0
  have hrat0 : RationalOverQbar Γ0 := by
    apply le_antisymm
    · conv_lhs => rw [hΓ0, H'.gam_rat]
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      exact Submodule.subset_span ⟨⟨s, hs.1, rfl⟩, hs.2.1⟩
    · exact Submodule.span_le.mpr fun _ hw => hw.1
  set k0 := finrank ℂ Γ0 with hk0
  set k1 := finrank ℚ (K11.annQ H'.U) with hk1
  obtain ⟨A, Bm, hBA, hA⟩ := exists_algFrame Γ0 hrat0
  obtain ⟨C, D, hDC, hC⟩ := K11.exists_frame (K11.annQ H'.U)
  have htl' : torusLie H'.U = LinearMap.range (K11.cm C).mulVecLin := by
    rw [torusLie_eq_annC, K11.annC_eq_cspan, K11.cspan_eq_range hC]
  -- the pivot
  obtain ⟨J, hJinj, hJsurj⟩ := LSG.MEB.pivot H'.t_rat
  set n := J.card with hn
  let eo := J.orderEmbOfFin (rfl : J.card = n)
  set e : Fin n → Fin m := fun i => eo i with he_def
  have he : Function.Injective e := eo.injective
  have heJ : ∀ i, e i ∈ J := fun i => J.orderEmbOfFin_mem rfl i
  have hJe : ∀ k ∈ J, ∃ i, e i = k := fun k hk => by
    have : k ∈ Set.range eo := by rw [Finset.range_orderEmbOfFin]; exact hk
    exact this
  set B' : Fin n → VBlock := fun i => B (e i) with hB'
  set An' : ∀ i, VBlockAn (B' i) := fun i => An (e i) with hAn'
  let pJ : (∀ k, Fin (B k).g → ℂ) →ₗ[ℂ] (∀ i, Fin (B' i).g → ℂ) := LinearMap.pi fun i => LinearMap.proj (e i)
  have pJ_apply : ∀ z i, pJ z i = z (e i) := fun _ _ => rfl
  have hinjt0 : ∀ z ∈ H'.t, (∀ i, z (e i) = 0) → z = 0 := fun z hz h => hJinj z hz fun k hk => by
    obtain ⟨i, rfl⟩ := hJe k hk; exact h i
  have hinjt : ∀ z ∈ H'.t, pJ z = 0 → z = 0 := fun z hz h => hinjt0 z hz fun i => congrFun h i
  let ext : (∀ i, Fin (B' i).g → ℂ) → (∀ k, Fin (B k).g → ℂ) := fun w => ∑ i, Pi.single (e i) (w i)
  have ext_e : ∀ w j, ext w (e j) = w j := by
    intro w j
    simp only [ext, Finset.sum_apply]
    rw [Finset.sum_eq_single j (fun i _ hij => Pi.single_eq_of_ne (fun h => hij (he h).symm) _)
      (by simp), Pi.single_eq_same]
  have hsurjt0 : ∀ w : ∀ i, Fin (B' i).g → ℂ, ∃ z ∈ H'.t, ∀ i, z (e i) = w i := fun w => by
    obtain ⟨z, hz, hzy⟩ := hJsurj (ext w)
    exact ⟨z, hz, fun j => by rw [hzy _ (heJ j), ext_e]⟩
  have hsurjt : ∀ w, ∃ z ∈ H'.t, pJ z = w := fun w => by
    obtain ⟨z, hz, hzw⟩ := hsurjt0 w
    exact ⟨z, hz, funext hzw⟩
  let pJt : H'.t ≃ₗ[ℂ] (∀ i, Fin (B' i).g → ℂ) := LinearEquiv.ofBijective (pJ ∘ₗ H'.t.subtype)
    ⟨fun a b h => Subtype.ext (sub_eq_zero.mp (hinjt _ (H'.t.sub_mem a.2 b.2)
        (by simpa [map_sub, sub_eq_zero] using h))),
      fun w => by obtain ⟨z, hz, rfl⟩ := hsurjt w; exact ⟨⟨z, hz⟩, rfl⟩⟩
  let σ : (∀ i, Fin (B' i).g → ℂ) →ₗ[ℂ] (∀ k, Fin (B k).g → ℂ) := H'.t.subtype ∘ₗ pJt.symm.toLinearMap
  have hσt : ∀ w, σ w ∈ H'.t := fun w => (pJt.symm w).2
  have hpσ : ∀ w, pJ (σ w) = w := fun w => pJt.apply_symm_apply w
  have hσp : ∀ z ∈ H'.t, σ (pJ z) = z := fun z hz => by
    have : pJt.symm (pJt ⟨z, hz⟩) = ⟨z, hz⟩ := pJt.symm_apply_apply _
    exact congrArg Subtype.val this
  have hσinj : Function.Injective σ := fun a b h => by rw [← hpσ a, ← hpσ b, h]
  have hft : finrank ℂ H'.t = ∑ i, (B' i).g := by
    rw [pJt.finrank_eq]; simp [Module.finrank_pi_fintype]
  -- finite index of `π_J (t ∩ per)` in `per (B ∘ e)`
  have hfin : ∀ w ∈ perBase B', ∃ N : ℕ, 0 < N ∧ σ (N • w) ∈ perBase B := by
    intro w hw
    let L : AddSubgroup (∀ i, Fin (B' i).g → ℂ) :=
      (H'.t.toAddSubgroup ⊓ perBase B).map pJ.toAddMonoidHom
    have hLle : L ≤ perBase B' := by
      rintro _ ⟨z, ⟨-, hz⟩, rfl⟩ i _
      exact hz (e i) (Set.mem_univ _)
    have hLset : (L : Set (∀ i, Fin (B' i).g → ℂ)) = pJ '' {z | z ∈ H'.t ∧ z ∈ perBase B} := by
      ext x; simp [L, AddSubgroup.coe_map]
    have hLspan : Submodule.span ℝ (L : Set (∀ i, Fin (B' i).g → ℂ)) = ⊤ := by
      rw [hLset, eq_top_iff]
      intro w' _
      obtain ⟨z, hz, rfl⟩ := hsurjt w'
      have hz' : z ∈ H'.t.restrictScalars ℝ := hz
      rw [H'.t_rat] at hz'
      have hm : (Submodule.span ℝ {z | z ∈ H'.t ∧ z ∈ perBase B}).map (pJ.restrictScalars ℝ) ≤
          Submodule.span ℝ (pJ '' {z | z ∈ H'.t ∧ z ∈ perBase B}) := by
        rw [Submodule.map_span]; exact le_rfl
      exact hm ⟨z, hz', rfl⟩
    obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent ℝ (L : Set (∀ i, Fin (B' i).g → ℂ))
    have : Finite s := hli.finite
    let b : Basis s ℝ (∀ i, Fin (B' i).g → ℂ) := Basis.mk hli (by rw [Subtype.range_coe, hspan, hLspan])
    have hb : ∀ i, b i ∈ perBase B' := fun i => by rw [Basis.mk_apply]; exact hLle (hsL i.2)
    have := LSG.MEB.discreteTopology_perAb (B := fun i => (B' i).base)
    obtain ⟨N, hN, hNw⟩ := isNsmulIn_closure_basis b (perBase B') hb w hw
    have hcl : AddSubgroup.closure (Set.range b) ≤ L := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [Basis.mk_apply]; exact hsL i.2
    obtain ⟨z, ⟨hzt, hzP⟩, hzw⟩ := hcl hNw
    refine ⟨N, hN, ?_⟩
    have : σ (N • w) = z := by
      have e1 : N • w = pJ z := hzw.symm
      rw [e1, hσp z hzt]
    rw [this]; exact hzP
  -- the push-out matrix `M′ = M A`
  obtain ⟨Ap, hApa, hAp⟩ := hP H'.t H'.t_rat n e he hinjt0 hsurjt0
  set M' : Matrix (Fin r) (Fin n) ℂ := M * Ap with hM'
  have hη : ∀ z ∈ H'.t, (∀ k, z k ∈ (B k).base.per) →
      M.mulVec (etaB B z) = M'.mulVec (etaB B' (pJ z)) := fun z hz hzp => by
    rw [hAp z hz hzp, hM', Matrix.mulVec_mulVec]; rfl
  have hfib : ∀ p ∈ perTanId B H'.t, p.2 = Ap.mulVec (fun i => p.2 (e i)) := by
    let φ : ((∀ k, Fin (B k).g → ℂ) × (Fin m → ℂ)) →ₗ[ℂ] (Fin m → ℂ) :=
      LinearMap.snd ℂ _ _ - Ap.mulVecLin ∘ₗ (LinearMap.pi fun i => LinearMap.proj (e i)) ∘ₗ LinearMap.snd ℂ _ _
    have hle : perTanId B H'.t ≤ LinearMap.ker φ := span_le.mpr fun q hq => by
      have hw : q.2 = etaB B q.1 := funext fun k => (hq.2 k).2
      have h1 := hAp q.1 hq.1 fun k => (hq.2 k).1
      change q.2 - Ap.mulVec (fun i => q.2 (e i)) = 0
      rw [sub_eq_zero]
      conv_lhs => rw [hw]
      rw [h1]
      congr 1; funext i; exact ((hq.2 (e i)).2).symm
    intro p hp
    have := hle hp
    rw [LinearMap.mem_ker] at this
    exact sub_eq_zero.mp this
  have hM'onto : Function.Surjective M'.mulVec := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hF H'.t H'.t_rat hne x
    have hx : M.mulVec p.2 = x := congrArg Prod.snd hpx
    refine ⟨fun i => p.2 (e i), ?_⟩
    rw [hM', ← Matrix.mulVec_mulVec, ← hfib p hp, hx]
  have hM'a : AlgMat M' := isAlgebraic_matrix_mul hMa hApa
  have H41 := h41 n e he M' hM'onto hM'a
  -- `PerTanFib` for the subfamily
  have hσrat : ∀ ts : Submodule ℂ (∀ i, Fin (B' i).g → ℂ), IsRatSub (perBase B') ts →
      IsRatSub (perBase B) (ts.map σ) := fun ts hts => isRatSub_map_sigma σ hfin hts
  have hσne : ∀ ts : Submodule ℂ (∀ i, Fin (B' i).g → ℂ), ts ≠ ⊥ → ts.map σ ≠ ⊥ := fun ts hts h =>
    hts (by
      rw [eq_bot_iff]; intro w hw
      have : σ w = 0 := (mem_bot ℂ).mp (h ▸ ⟨w, hw, rfl⟩ : σ w ∈ (⊥ : Submodule ℂ _))
      exact (mem_bot ℂ).mpr (hσinj (by rw [this, map_zero])))
  have hF' : PerTanFib B' M' := by
    intro ts hts htsne x
    obtain ⟨p, hp, hpx⟩ := hF _ (hσrat ts hts) (hσne ts htsne) x
    have hp1 : p.1 = 0 := congrArg Prod.fst hpx
    have hp2 : M.mulVec p.2 = x := congrArg Prod.snd hpx
    have hσts : ts.map σ ≤ H'.t := by rintro _ ⟨w, -, rfl⟩; exact hσt w
    have hpt : p ∈ perTanId B H'.t := by
      refine (span_mono ?_ : perTanId B (ts.map σ) ≤ perTanId B H'.t) hp
      exact fun q hq => ⟨hσts hq.1, hq.2⟩
    have hq : (pJ p.1, fun i => p.2 (e i)) ∈ perTanId B' ts := by
      clear hpx hp1 hp2 hpt
      induction hp using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨⟨w, hw, hwq⟩, hq2⟩ := hq
        refine subset_span ⟨?_, fun i => ⟨(hq2 (e i)).1, (hq2 (e i)).2⟩⟩
        change pJ q.1 ∈ ts
        rw [← hwq, hpσ]; exact hw
      | zero =>
        convert (perTanId B' ts).zero_mem using 1
        ext <;> simp
      | add x y _ _ hx hy =>
        have := (perTanId B' ts).add_mem hx hy
        convert this using 1
        ext <;> simp
      | smul c x _ hx =>
        have := (perTanId B' ts).smul_mem c hx
        convert this using 1
        ext <;> simp
    refine ⟨_, hq, ?_⟩
    change ((LinearMap.id : _ →ₗ[ℂ] _) (pJ p.1), M'.mulVec (fun i => p.2 (e i))) = _
    rw [hp1, map_zero, hM', ← Matrix.mulVec_mulVec, ← hfib p hpt, hp2]; rfl
  -- the transport maps
  set ι : TanAV k0 k1 r B' →ₗ[ℂ] TanAV d₀ d₁ r B := iotaAV (cmK K11.Kq A) (K11.cm C) σ with hι
  set π : TanAV d₀ d₁ r B →ₗ[ℂ] TanAV k0 k1 r B' := piAV (cmK K11.Kq Bm) (K11.cm D) pJ with hπ
  have hι_apply : ∀ x, ι x = ((cmK K11.Kq A).mulVec x.1, (K11.cm C).mulVec x.2.1, σ x.2.2.1, x.2.2.2) :=
    fun _ => rfl
  have hπ_apply : ∀ x, π x = ((cmK K11.Kq Bm).mulVec x.1, (K11.cm D).mulVec x.2.1, pJ x.2.2.1, x.2.2.2) :=
    fun _ => rfl
  have hπι : ∀ x, π (ι x) = x := by
    intro x
    rw [hι_apply, hπ_apply, mulVec_left_invK hBA, K11.mulVec_left_inv hDC, hpσ]
  have hinj : Function.Injective ι := fun x y h => by rw [← hπι x, ← hπι y, h]
  have hιπ : ∀ v ∈ H'.tan, ι (π v) = v := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := (mem_tan_iff_of_ne hF H' hne).mp hv
    have h1' : v.1 ∈ LinearMap.range (cmK K11.Kq A).mulVecLin := by rw [hA]; exact h1
    rw [htl'] at h2
    obtain ⟨a, ha⟩ := h1'; obtain ⟨c, hc⟩ := h2
    change ((cmK K11.Kq A).mulVec ((cmK K11.Kq Bm).mulVec v.1), (K11.cm C).mulVec ((K11.cm D).mulVec v.2.1),
      σ (pJ v.2.2.1), v.2.2.2) = v
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext (hσp _ h3) rfl))
    · change (cmK K11.Kq A).mulVec ((cmK K11.Kq Bm).mulVec v.1) = v.1
      rw [← ha]; simp only [Matrix.mulVecLin_apply]; rw [mulVec_left_invK hBA]
    · change (K11.cm C).mulVec ((K11.cm D).mulVec v.2.1) = v.2.1
      rw [← hc]; simp only [Matrix.mulVecLin_apply]; rw [K11.mulVec_left_inv hDC]
  have hrange : LinearMap.range ι = H'.tan := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine (mem_tan_iff_of_ne hF H' hne).mpr ⟨?_, ?_, hσt _⟩
      · have := LinearMap.mem_range_self (cmK K11.Kq A).mulVecLin x.1
        rw [hA] at this; exact this
      · change (K11.cm C).mulVec x.2.1 ∈ torusLie H'.U
        rw [htl']; exact ⟨x.2.1, rfl⟩
    · intro v hv; exact ⟨π v, hιπ v hv⟩
  have hfT : finrank ℂ H'.tan = k0 + k1 + (∑ i, (B' i).g + r) := by
    rw [← hrange, LinearMap.finrank_range_of_inj hinj, finrank_TanAV]; ring
  have htor' : finrank ℂ (torusLie H'.U) = k1 := by
    have h1 := K11.finrank_annQ H'.U
    have h2 := finrank_torusLie H'.U
    omega
  have hmap : ∀ S : Submodule ℂ (TanAV d₀ d₁ r B), S ≤ H'.tan → (S.comap ι).map ι = S := by
    intro S hS; rw [Submodule.map_comap_eq, hrange, inf_eq_right.mpr hS]
  set Vs := V.comap ι with hVs_def
  set Ws := W.comap ι with hWs_def
  set Ys := Y.map π.toAddMonoidHom with hYs_def
  have hWR : W ≤ H'.tan := hWV.trans hVT
  have hVs : finrank ℂ Vs = finrank ℂ V := by rw [← finrank_map_inj hinj, hmap V hVT]
  have hWs : finrank ℂ Ws = finrank ℂ W := by rw [← finrank_map_inj hinj, hmap W hWR]
  have hWsrat : RationalOverQbarAV Ws := by
    set S := {w | w ∈ W ∧ AlgTanAV w} with hS
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
      refine ⟨by rw [hWs_eq]; exact ⟨s, hs.1, rfl⟩, ?_, ?_, ?_, ?_⟩
      · rw [hπ_apply]; exact algVec_cmK_mulVec Bm hs.2.1
      · rw [hπ_apply]; exact algVec_cm_mulVec D hs.2.2.1
      · intro i j; rw [hπ_apply]; exact hs.2.2.2.1 (e i) j
      · rw [hπ_apply]; exact hs.2.2.2.2
    · rw [Submodule.span_le]; exact fun x hx => hx.1
  have hYsfg : Ys.FG := K11.fg_map_addSubgroup hYfg _
  have hYsmem : ∀ x ∈ Ys, x ∈ Vs ∧ x ∈ LamAV k0 k1 An' M' := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyV, hyL⟩ := hY y hy
    refine ⟨?_, ?_⟩
    · change ι (π y) ∈ V
      rw [hιπ y (hVT hyV)]; exact hyV
    · change π y ∈ LamAV k0 k1 An' M'
      have hyt : y.2.2.1 ∈ H'.t := mem_tan_z (hVT hyV)
      have hs : sPart M' (π y) = sPart M y := by
        unfold sPart
        rw [hπ_apply, hη _ hyt fun k => (An k).an.lat_le (hyL.2.2.1 k)]
      refine ⟨?_, ?_, fun i => hyL.2.2.1 (e i), ?_⟩
      · rw [hπ_apply]; exact algVec_cmK_mulVec Bm hyL.1
      · rw [hπ_apply]; exact exp_cm_mulVec D hyL.2.1
      · rw [hs]; exact hyL.2.2.2
  -- the `ℚ`-structures
  set ιq := ι.restrictScalars ℚ with hιq
  have hinjq : Function.Injective ιq := hinj
  set Yq := Submodule.span ℚ (Y : Set (TanAV d₀ d₁ r B)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  have hYR : Yq ≤ H'.tan.restrictScalars ℚ := Submodule.span_le.mpr fun y hy => hVT (hY y hy).1
  have hYmap : (Submodule.span ℚ (Ys : Set (TanAV k0 k1 r B'))).map ιq = Yq := by
    rw [Submodule.map_span]; congr 1
    ext v; constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      change ι (π y) ∈ Y
      rw [hιπ y (hVT (hY y hy).1)]; exact hy
    · intro hv; exact ⟨π v, ⟨v, hv, rfl⟩, hιπ v (hVT (hY v hv).1)⟩
  have hPmap : (OmAV k0 k1 B' M').map ιq = OmAV d₀ d₁ B M ⊓ H'.tan.restrictScalars ℚ := by
    apply le_antisymm
    · rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨p, hp, rfl⟩
      refine ⟨?_, by change ι p ∈ H'.tan; rw [← hrange]; exact LinearMap.mem_range_self ι p⟩
      choose nv hnv using hp.2.1
      have hpz : ∀ i, p.2.2.1 i ∈ (B' i).base.per := hp.2.2.1
      obtain ⟨N, hN, hNσ⟩ := hfin p.2.2.1 fun i _ => hpz i
      have hdec : ι p = inTV d₀ d₁ r B ((C.mulVec fun i => (nv i : ℚ))) +
          ((0, 0, σ p.2.2.1, M'.mulVec (etaB B' p.2.2.1)) : TanAV d₀ d₁ r B) := by
        rw [hι_apply, inTV_apply, hp.1, hp.2.2.2]
        refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
        have hb : p.2.1 = (2 * Real.pi * I : ℂ) • K11.castL k1 (fun i => (nv i : ℚ)) := by
          funext i; simp [hnv i, K11.castL, mul_comm]
        simp only [Prod.snd_add, Prod.fst_add, add_zero, hb, Matrix.mulVec_smul]
        congr 1; exact K11.cm_mulVec_castL C _
      change ι p ∈ OmAV d₀ d₁ B M
      rw [hdec]
      refine add_mem (inTV_mem_OmAV _) (mem_span_rat_of_nsmul hN (subset_span ?_))
      have hσz : ∀ k, σ (N • p.2.2.1) k ∈ (B k).base.per := fun k => hNσ k (Set.mem_univ k)
      have e1 : N • ((0, 0, σ p.2.2.1, M'.mulVec (etaB B' p.2.2.1)) : TanAV d₀ d₁ r B) =
          (0, 0, σ (N • p.2.2.1), M.mulVec (etaB B (σ (N • p.2.2.1)))) := by
        have hη2 : M.mulVec (etaB B (σ (N • p.2.2.1))) = N • M'.mulVec (etaB B' p.2.2.1) := by
          rw [hη _ (hσt _) hσz, hpσ, etaB_nsmul hpz, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.mulVec_smul,
            Nat.cast_smul_eq_nsmul]
        rw [hη2, map_nsmul]
        ext <;> simp
      rw [e1]; exact blk_mem_perAVf hσz
    · rintro x ⟨hxΩ, hxR⟩
      have hxR' : x ∈ H'.tan := hxR
      obtain ⟨N, hN, hNx⟩ := exists_nsmul_of_mem_span hxΩ
      have hNxt : N • x ∈ H'.tan := H'.tan.toAddSubgroup.nsmul_mem hxR' N
      have hLt : (N • x).2.2.1 ∈ H'.t := mem_tan_z hNxt
      choose nv hnv using hNx.2.1
      have hπN : π (N • x) ∈ OmAV k0 k1 B' M' := by
        have hdec : π (N • x) = inTV k0 k1 r B' ((D.mulVec fun i => (nv i : ℚ))) +
            ((0, 0, pJ (N • x).2.2.1, M'.mulVec (etaB B' (pJ (N • x).2.2.1))) : TanAV k0 k1 r B') := by
          rw [hπ_apply, inTV_apply, hNx.1, hNx.2.2.2, hη _ hLt hNx.2.2.1]
          refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
          have hb : (N • x).2.1 = (2 * Real.pi * I : ℂ) • K11.castL d₁ (fun i => (nv i : ℚ)) := by
            funext i; simp only [Pi.smul_apply, smul_eq_mul, K11.castL, LinearMap.coe_mk, AddHom.coe_mk]
            rw [hnv i]; push_cast; ring
          simp only [Prod.snd_add, Prod.fst_add, add_zero, hb, Matrix.mulVec_smul]
          congr 1; exact K11.cm_mulVec_castL D _
        rw [hdec]
        exact add_mem (inTV_mem_OmAV _) (subset_span (blk_mem_perAVf fun i => hNx.2.2.1 (e i)))
      have hπx : π x ∈ OmAV k0 k1 B' M' := by
        refine mem_span_rat_of_nsmul hN ?_
        rw [← map_nsmul]; exact hπN
      exact ⟨π x, hπx, hιπ x hxR'⟩
  have hspanP : ∀ {k0' k1' : ℕ} {n' : ℕ} {B'' : Fin n' → VBlock} (An'' : ∀ i, VBlockAn (B'' i))
      (M'' : Matrix (Fin r) (Fin n') ℂ),
      Submodule.span ℚ (PerAV k0' k1' An'' M'' : Set (TanAV k0' k1' r B'')) = OmAV k0' k1' B'' M'' :=
    fun An'' M'' => span_perAV_eq An''
  have rk1 : rk Ys = finrank ℚ Yq := by rw [rk, ← finrank_map_inj hinjq, hYmap]
  have rk2 : rk (Ys ⊓ PerAV k0 k1 An' M') = finrank ℚ ↥(Yq ⊓ OmAV d₀ d₁ B M) := by
    rw [rk, K11.span_inf_addSubgroup, hspanP, ← finrank_map_inj hinjq, Submodule.map_inf _ hinjq,
      hYmap, hPmap, inf_comm (OmAV d₀ d₁ B M), ← inf_assoc, inf_eq_left.mpr hYR]
  -- toric injectivity of `Vs`
  have hTors : TorInjAV M' Vs := by
    intro v hv hvP hv1
    have h1 : ι v ∈ OmAV d₀ d₁ B M := (hPmap.le ⟨v, hvP, rfl⟩).1
    have h2 : (ι v).2.1 = 0 := by rw [hι_apply]; simp [hv1]
    exact hinj (by rw [hTor (ι v) hv h1 h2, map_zero])
  -- the small theorem
  have hsum : (∑ i, ((fun i => B (e i)) i).g) = ∑ i, (B' i).g := rfl
  obtain ⟨Hs, -, hτs, hineqs⟩ := H41 k0 k1 Vs Ws Ys (by rw [hVs]; omega)
    (Submodule.comap_mono hWV) hWsrat hYsfg hYsmem hTors (by rw [rk2, hVs]; rw [htor'] at hNR; omega)
  -- the pushed member `G''`
  set Pa : ((Fin k0 → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] ((Fin d₀ → ℂ) × (Fin r → ℂ)) :=
    LinearMap.prodMap (cmK K11.Kq A).mulVecLin LinearMap.id with hPa
  have hgamrat : RatPair (Hs.gam.map Pa) := by
    refine le_antisymm ?_ (Submodule.span_le.mpr fun x hx => hx.1)
    conv_lhs => rw [Hs.gam_rat]
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw.1, rfl⟩, algVec_cmK_mulVec A hw.2.1, hw.2.2⟩
  let H'' : SubgroupDataAV d₀ d₁ B M :=
    { U := K11.annQ ((K11.annQ Hs.U).map C.mulVecLin)
      t := Hs.t.map σ
      gam := Hs.gam.map Pa
      gam_rat := hgamrat
      t_rat := hσrat _ Hs.t_rat }
  have htl'' : (torusLie Hs.U).map (K11.cm C).mulVecLin = torusLie H''.U := by
    rw [torusLie_eq_annC, K11.annC_eq_cspan, K11.map_cspan, torusLie_eq_annC,
      ← K11.cspan_eq_annC]
  have hPerT : (perTanA B' M' Hs.t).map (LinearMap.prodMap σ LinearMap.id) = perTanA B M (Hs.t.map σ) := by
    by_cases hts : Hs.t = ⊥
    · have h0 : Hs.t.map σ = ⊥ := by rw [hts, Submodule.map_bot]
      rw [h0, hts, perTanA_bot', perTanA_bot', Submodule.map_bot]
    · rw [perTanA_eq_prod hF' Hs.t_rat hts, perTanA_eq_prod hF (hσrat _ Hs.t_rat) (hσne _ hts)]
      ext ⟨z, s⟩; constructor
      · rintro ⟨⟨w, s'⟩, ⟨hw, -⟩, h⟩
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
        exact ⟨⟨w, hw, rfl⟩, mem_top⟩
      · rintro ⟨⟨w, hw, rfl⟩, -⟩
        exact ⟨(w, s), ⟨hw, mem_top⟩, rfl⟩
  have hTan : Hs.tan.map ι = H''.tan := by
    simp only [SubgroupDataAV.tan, Submodule.map_sup, Submodule.map_comp]
    have e1 : ι.comp (vecInclA : _ →ₗ[ℂ] TanAV k0 k1 r B') = vecInclA.comp Pa := by
      apply LinearMap.ext; intro x; rw [LinearMap.comp_apply, hι_apply]; ext <;> simp [vecInclA, Pa]
    have e2 : ι.comp (torInclA : _ →ₗ[ℂ] TanAV k0 k1 r B') = torInclA.comp (K11.cm C).mulVecLin := by
      apply LinearMap.ext; intro x; rw [LinearMap.comp_apply, hι_apply]; ext <;> simp [torInclA]
    have e3 : ι.comp (g2InclA : _ →ₗ[ℂ] TanAV k0 k1 r B') =
        g2InclA.comp (LinearMap.prodMap σ LinearMap.id) := by
      apply LinearMap.ext; intro x; rw [LinearMap.comp_apply, hι_apply]; ext <;> simp [g2InclA]
    rw [← Submodule.map_comp, ← Submodule.map_comp, ← Submodule.map_comp, e1, e2, e3, Submodule.map_comp,
      Submodule.map_comp, Submodule.map_comp, htl'', hPerT]
  have hT''T : H''.tan ≤ H'.tan := by
    rw [← hTan, ← hrange]; exact LinearMap.map_le_range
  have hWinf : finrank ℂ ↥(Ws ⊓ Hs.tan) = finrank ℂ ↥(W ⊓ H''.tan) := by
    rw [← finrank_map_inj hinj, Submodule.map_inf _ hinj, hmap W hWR, hTan]
  have hfT'' : finrank ℂ H''.tan = finrank ℂ Hs.tan := by rw [← hTan, finrank_map_inj hinj]
  have htorS : finrank ℂ (torusLie H''.U) = finrank ℂ (torusLie Hs.U) := by
    rw [← htl'', finrank_map_inj (K11.cm_injective hDC)]
  have hAinj : Function.Injective (cmK K11.Kq A).mulVecLin := fun x y h => by
    rw [← mulVec_left_invK hBA x, ← mulVec_left_invK hBA y]
    exact congrArg (cmK K11.Kq Bm).mulVec h
  have hpr0 : finrank ℂ (H''.gam.map (LinearMap.fst ℂ _ _)) = finrank ℂ (Hs.gam.map (LinearMap.fst ℂ _ _)) := by
    have : H''.gam.map (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin r → ℂ)) =
        (Hs.gam.map (LinearMap.fst ℂ _ _)).map (cmK K11.Kq A).mulVecLin := by
      change (Hs.gam.map Pa).map _ = _
      rw [← Submodule.map_comp, ← Submodule.map_comp]; rfl
    rw [this, finrank_map_inj hAinj]
  have hTq : (Submodule.span ℚ ((Hs.tan.toAddSubgroup : AddSubgroup (TanAV k0 k1 r B')) :
      Set (TanAV k0 k1 r B'))).map ιq = H''.tan.restrictScalars ℚ := by
    rw [K11.span_submodule_coe, ← hTan]; rfl
  have rk3 : rk (Ys ⊓ (Hs.tan.toAddSubgroup ⊔ PerAV k0 k1 An' M')) =
      finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmAV d₀ d₁ B M)) := by
    rw [rk, K11.span_inf_addSubgroup, K11.span_sup_addSubgroup, hspanP, ← finrank_map_inj hinjq,
      Submodule.map_inf _ hinjq, Submodule.map_sup, hYmap, hTq, hPmap]
    have hT''q : H''.tan.restrictScalars ℚ ≤ H'.tan.restrictScalars ℚ := fun x hx => hT''T hx
    have : Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmAV d₀ d₁ B M ⊓ H'.tan.restrictScalars ℚ) =
        Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmAV d₀ d₁ B M) := by
      rw [← sup_inf_assoc_of_le _ hT''q, inf_comm _ (H'.tan.restrictScalars ℚ), ← inf_assoc,
        inf_eq_left.mpr hYR]
    rw [this]
  -- numerics
  have hle1 : finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmAV d₀ d₁ B M)) ≤ finrank ℚ Yq :=
    Submodule.finrank_mono inf_le_left
  have hle2 : finrank ℂ ↥(W ⊓ H''.tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
  have hfTs := finrank_tan_eq Hs
  have hfT''e := finrank_tan_eq H''
  have hftorS := finrank_torusLie Hs.U
  have hd2s := d2H_le Hs
  have hts' : finrank ℂ Hs.t ≤ ∑ i, (B' i).g :=
    (Submodule.finrank_le _).trans (by simp [Module.finrank_pi_fintype]; exact le_rfl)
  have hp0s : finrank ℂ (Hs.gam.map (LinearMap.fst ℂ _ _)) ≤ k0 := (Submodule.finrank_le _).trans (by simp)
  have hd2' := d2H_eq_of_ne hF H' hne
  have hTsle : finrank ℂ Hs.tan ≤ k0 + k1 + ∑ i, (B' i).g + r := by
    have := Submodule.finrank_le Hs.tan
    rw [finrank_TanAV] at this; exact this
  have hδ : (Hs.δ : ℤ) = (finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan := by
    simp only [SubgroupDataAV.δ]
    rw [hfT'', Nat.cast_sub hTsle, hfT]; push_cast; ring
  have hδ12 : ((Hs.δ1 + 2 * Hs.δ2 : ℕ) : ℤ) = (nPAV H' : ℤ) - nPAV H'' := by
    simp only [SubgroupDataAV.δ2, SubgroupDataAV.δ, SubgroupDataAV.δ0, SubgroupDataAV.δ1, nPAV]
    rw [htorS, htor', hd2', ← hft]
    rw [hfT'', hpr0, htorS] at hfT''e
    omega
  refine ⟨H'', hT''T, ?_, ?_⟩
  · rw [hWs, hWinf] at hτs
    have := (Nat.cast_lt (α := ℤ)).mpr hτs
    rw [Nat.cast_sub hle2, hδ] at this
    exact this
  · rw [rk1, rk3, rk2, hVs, hWs, hWinf] at hineqs
    have e1 : ((finrank ℚ Yq - finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmAV d₀ d₁ B M)) +
        Hs.δ1 + 2 * Hs.δ2 : ℕ) : ℤ) = (finrank ℚ Yq : ℤ) -
          finrank ℚ ↥(Yq ⊓ (H''.tan.restrictScalars ℚ ⊔ OmAV d₀ d₁ B M)) +
          ((nPAV H' : ℤ) - nPAV H'') := by
      rw [← hδ12]; push_cast [Nat.cast_sub hle1]; ring
    have e2 : (((k0 + k1 + ∑ i, (B' i).g + r : ℕ) : ℤ) - finrank ℂ V) = 1 := by
      rw [hfT] at hVdim; omega
    have e3 : ((Hs.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H''.tan) : ℕ) : ℤ)) =
        ((finrank ℂ H'.tan : ℤ) - finrank ℂ H''.tan) -
          ((finrank ℂ W : ℤ) - finrank ℂ ↥(W ⊓ H''.tan)) := by
      rw [hδ, Nat.cast_sub hle2]
    have e4 : (((k1 + 2 * (∑ i, (B' i).g + r) : ℕ) : ℤ) - finrank ℚ ↥(Yq ⊓ OmAV d₀ d₁ B M)) =
        (nPAV H' : ℤ) - finrank ℚ ↥(Yq ⊓ OmAV d₀ d₁ B M) := by
      simp only [nPAV, htor', hd2', hft]
    rw [e1, e2, e3, e4, mul_one] at hineqs
    exact hineqs

end LSG.W88
