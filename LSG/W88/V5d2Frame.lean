/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dTrans
import LSG.W88.V5dMain
import LSG.W88.V5d2Stmt

/-!
# Frames of members for every `r`, and the fibre bookkeeping of the §5d engine at `r ≤ 2`

`exists_frame` (`V5dFrame.lean`) needs `r ≤ 1` only to make `V_f = M(fib B^♮) + Γ_fib` rational.
Here:
* `ratPair_inf_ker`, `rational_comap_inr`, `rational_map_algLin`, `rational_sup`: rationality is
  preserved by intersections with algebraic kernels, `comap inr`, algebraic images and sums;
* **`rational_Vf`** (`PerTanRat`, `AlgMat M`), hence **`exists_frame2`**: every member has a frame,
  for every `r`; `topV_tan2`;
* **`perTanRat_comp`**: `PerTanRat` is inherited by sub-families of curves (as `liftAlg_comp`);
* `finrank_inf_fibreV_le_one`: if no nonzero member lies in `V` and `r ≤ 2`, then
  `dim (V ∩ fibre) ≤ 1` (the fibre is a member);
* `Frame.finrank_comap_inf_fibreV`, `trans_premises2`: `trans_premises` without `V ∩ fibre = 0`.
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

variable {d0 d1 m r : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

/-! ### Rationality lemmas -/

section Rat

variable {a b : ℕ}

lemma ratPair_iff' (W : Submodule ℂ ((Fin a → ℂ) × (Fin b → ℂ))) :
    (∃ S : Set ((Fin a → ℂ) × (Fin b → ℂ)), (∀ v ∈ S, AlgPair v) ∧ W = Submodule.span ℂ S) ↔
      RatPair W := by
  constructor
  · rintro ⟨S, hS, rfl⟩; exact ratPair_of_span S hS
  · intro h; exact ⟨_, fun v hv => hv.2, h⟩

/-- `W ⊓ ker f` is rational for `W` rational and `f` algebraic. -/
lemma ratPair_inf_ker {W : Submodule ℂ ((Fin a → ℂ) × (Fin b → ℂ))} (hW : RatPair W)
    {f : ((Fin a → ℂ) × (Fin b → ℂ)) →ₗ[ℂ] ℂ} (hf : ∀ v, AlgPair v → IsAlgebraic ℚ (f v)) :
    RatPair (W ⊓ LinearMap.ker f) := by
  classical
  rw [← ratPair_iff'] at hW ⊢
  obtain ⟨S, hSalg, rfl⟩ := hW
  by_cases h : ∀ s ∈ S, f s = 0
  · refine ⟨S, hSalg, ?_⟩
    refine inf_eq_left.mpr (Submodule.span_le.mpr fun s hs => ?_)
    exact LinearMap.mem_ker.mpr (h s hs)
  push Not at h
  obtain ⟨s₀, hs₀, hfs₀⟩ := h
  let g : ((Fin a → ℂ) × (Fin b → ℂ)) → ((Fin a → ℂ) × (Fin b → ℂ)) :=
    fun s => s + (-(f s / f s₀)) • s₀
  refine ⟨g '' S, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine algPair_add (hSalg s hs) (algPair_smul ?_ (hSalg s₀ hs₀))
    rw [← K11.mem_Kq]
    exact K11.Kq.neg_mem (K11.Kq.div_mem (K11.mem_Kq.mpr (hf s (hSalg s hs)))
      (K11.mem_Kq.mpr (hf s₀ (hSalg s₀ hs₀))))
  apply le_antisymm
  · rintro w ⟨hw, hwk⟩
    have key : ∀ w ∈ Submodule.span ℂ S, g w ∈ Submodule.span ℂ (g '' S) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp [g]
      | add x y _ _ hx hy =>
        have : g (x + y) = g x + g y := by
          simp only [g, map_add, add_div, neg_add, add_smul]; abel
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        have : g (c • x) = c • g x := by
          simp only [g, map_smul, smul_eq_mul, smul_add, smul_smul, mul_div_assoc, mul_neg]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have := key w hw
    rwa [show g w = w by simp [g, LinearMap.mem_ker.mp hwk]] at this
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨Submodule.add_mem _ (Submodule.subset_span hs)
      (Submodule.smul_mem _ _ (Submodule.subset_span hs₀)), ?_⟩
    change g s ∈ LinearMap.ker f
    rw [LinearMap.mem_ker, map_add, map_smul, smul_eq_mul, neg_mul, div_mul_cancel₀ _ hfs₀,
      add_neg_cancel]

/-- The first coordinate forms. -/
noncomputable def fstCoord (i : Fin a) : ((Fin a → ℂ) × (Fin b → ℂ)) →ₗ[ℂ] ℂ :=
  (LinearMap.proj i).comp (LinearMap.fst ℂ _ _)

lemma ratPair_inf_fst {W : Submodule ℂ ((Fin a → ℂ) × (Fin b → ℂ))} (hW : RatPair W)
    (s : Finset (Fin a)) : RatPair (W ⊓ s.inf fun i => LinearMap.ker (fstCoord (b := b) i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hW
  | insert c s _ ih =>
    rw [Finset.inf_insert, inf_comm (LinearMap.ker (fstCoord c)), ← inf_assoc]
    exact ratPair_inf_ker ih fun v hv => hv.1 c

lemma rational_span_alg {n : ℕ} (T : Set (Fin n → ℂ)) (hT : ∀ v ∈ T, AlgVec v) :
    RationalOverQbar (Submodule.span ℂ T) := by
  apply le_antisymm
  · exact Submodule.span_mono fun v hv => ⟨Submodule.subset_span hv, hT v hv⟩
  · exact Submodule.span_le.mpr fun _ hw => hw.1

/-- **`{w | (0, w) ∈ P}` is rational for `P` rational.** -/
lemma rational_comap_inr {P : Submodule ℂ ((Fin a → ℂ) × (Fin b → ℂ))} (hP : RatPair P) :
    RationalOverQbar (P.comap (LinearMap.inr ℂ (Fin a → ℂ) (Fin b → ℂ))) := by
  classical
  set Q := P ⊓ Finset.univ.inf fun i => LinearMap.ker (fstCoord (b := b) i) with hQdef
  have hQ : RatPair Q := ratPair_inf_fst hP Finset.univ
  have e : P.comap (LinearMap.inr ℂ (Fin a → ℂ) (Fin b → ℂ)) = Q.map (LinearMap.snd ℂ _ _) := by
    ext w; constructor
    · intro hw
      refine ⟨(0, w), ⟨hw, ?_⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_finsetInf]
      intro i _; simp [fstCoord]
    · rintro ⟨x, ⟨hxP, hx0⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_finsetInf] at hx0
      have hx1 : x.1 = 0 := funext fun i => by
        simpa [fstCoord] using hx0 i (Finset.mem_univ i)
      change (0, x.2) ∈ P
      have : ((0 : Fin a → ℂ), x.2) = x := Prod.ext hx1.symm rfl
      rw [this]; exact hxP
  rw [e, hQ, Submodule.map_span]
  refine rational_span_alg _ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hv.2.2

lemma rational_map_algLin {n n' : ℕ} {S : Submodule ℂ (Fin n → ℂ)} (hS : RationalOverQbar S)
    {f : (Fin n → ℂ) →ₗ[ℂ] (Fin n' → ℂ)} (hf : AlgLin f) : RationalOverQbar (S.map f) := by
  rw [hS, Submodule.map_span]
  refine rational_span_alg _ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hf v hv.2

lemma rational_sup {n : ℕ} {S S' : Submodule ℂ (Fin n → ℂ)} (hS : RationalOverQbar S)
    (hS' : RationalOverQbar S') : RationalOverQbar (S ⊔ S') := by
  apply le_antisymm _ (Submodule.span_le.mpr fun _ hw => hw.1)
  refine sup_le ?_ ?_
  · rw [hS]; exact Submodule.span_mono fun v hv => ⟨Submodule.mem_sup_left (hS ▸ hv.1), hv.2⟩
  · rw [hS']; exact Submodule.span_mono fun v hv => ⟨Submodule.mem_sup_right (hS' ▸ hv.1), hv.2⟩

end Rat

/-! ### Frames for every `r` -/

/-- **`V_f` is rational** (`PerTanRat`, `M` algebraic). -/
theorem rational_Vf (hM : AlgMat M) (hPT : PerTanRat Ls)
    (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) : RationalOverQbar (Vf H) :=
  rational_sup (rational_map_algLin (rational_comap_inr (hPT _ H.t_ab)) (algLin_mat hM))
    (rational_comap_inr H.gam_rat)

/-- **Every member has a frame** (every `r`; `PerTanRat`, `M` algebraic). -/
theorem exists_frame2 (hM : AlgMat M) (hPT : PerTanRat Ls)
    (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) : Nonempty (Frame H) := by
  obtain ⟨c0⟩ := LSG.CM.nonempty_chart H.t
  obtain ⟨A0, B0, G0, hBA, hA, hAG, hAa, hBa, hGa⟩ := exists_secFrame H.gam_rat
  obtain ⟨C0, D0, hDC, hC⟩ := K11.exists_frame (K11.annQ H.U)
  obtain ⟨F0, L0, hLF, hF⟩ := K5d.exists_algFrame (Vf H) (rational_Vf hM hPT H)
  exact ⟨{
    c := c0, A := A0, Bm := B0, G := G0, C := C0, D := D0,
    Fm := (K5d.cmK K11.Kq F0).mulVecLin, Fl := (K5d.cmK K11.Kq L0).mulVecLin,
    BA := hBA, rangeA := hA, AG := hAG, DC := hDC, rangeC := hC,
    FlFm := fun σ => K5d.mulVec_left_invK hLF σ, rangeFm := hF,
    algA := hAa, algB := hBa, algG := hGa, algFm := algLin_cmK F0, algFl := algLin_cmK L0,
    algK := algLin_perK c0 H.t_ab (hPT _ H.t_ab), algN := algLin_perN c0 H.t_ab (hPT _ H.t_ab),
    algLift := algLin_lift c0 H.t_ab (hPT _ H.t_ab) }⟩

lemma topV_tan2 (hM : AlgMat M) (hPT : PerTanRat Ls) :
    (topV (d0 := d0) (d1 := d1) Ls M).tan = ⊤ := by
  obtain ⟨F⟩ := exists_frame2 hM hPT (topV (d0 := d0) (d1 := d1) Ls M)
  apply Submodule.eq_top_of_finrank_eq
  rw [F.finrank_tan]
  have h0 : fk0 (topV (d0 := d0) (d1 := d1) Ls M) = d0 := finrank_map_fst_top
  have h1 : fk1 (topV (d0 := d0) (d1 := d1) Ls M) = d1 := by
    have := K11.finrank_annQ (⊥ : Submodule ℚ (Fin d1 → ℚ))
    simp only [finrank_bot, add_zero] at this
    exact this
  have h2 : fg (topV (d0 := d0) (d1 := d1) Ls M) = m := by
    change finrank ℂ (⊤ : Submodule ℂ (Fin m → ℂ)) = m
    rw [finrank_top, Module.finrank_fin_fun]
  have h3 : ff (topV (d0 := d0) (d1 := d1) Ls M) = r := by
    have : Vf (topV (d0 := d0) (d1 := d1) Ls M) = ⊤ := by
      rw [eq_top_iff]; intro s _
      exact Submodule.mem_sup_right (Submodule.mem_comap.mpr Submodule.mem_top)
    change finrank ℂ (Vf (topV (d0 := d0) (d1 := d1) Ls M)) = r
    rw [this, finrank_top, Module.finrank_fin_fun]
  rw [h0, h1, h2, h3]; simp [add_assoc]

/-! ### `PerTanRat` for sub-families -/

section Incl

variable {g : ℕ} {ι : Fin g → Fin m}

lemma etaV_inclL (hι : Function.Injective ι) (u : Fin g → ℂ) :
    etaV Ls (inclL ι u) = inclL ι (etaV (Ls ∘ ι) u) := by
  funext j
  by_cases h : ∃ k, ι k = j
  · obtain ⟨k, rfl⟩ := h
    rw [inclL_apply_ι hι, etaV, inclL_apply_ι hι]; rfl
  · push Not at h
    rw [inclL_apply_of _ h, etaV, inclL_apply_of _ h, LSG.Weierstrass.eta_zero]

/-- **`PerTanRat` is inherited by sub-families of curves.** -/
theorem perTanRat_comp (hι : Function.Injective ι) (h : PerTanRat Ls) : PerTanRat (Ls ∘ ι) := by
  intro ts hts
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
  have heq : perTanId (Ls ∘ ι) ts =
      (perTanId Ls T).map (LinearMap.prodMap (LSG.CM.proj ι) (LSG.CM.proj ι)) := by
    apply le_antisymm
    · rw [perTanId, Submodule.span_le]
      rintro ⟨l, e⟩ ⟨hl, hlat, he⟩
      simp only at hl hlat he
      subst he
      refine ⟨(inclL ι l, etaV Ls (inclL ι l)),
        Submodule.subset_span ⟨⟨l, hl, rfl⟩, latVec_inclL hι hlat, rfl⟩, ?_⟩
      simp only [LinearMap.prodMap_apply, proj_inclL hι, etaV_inclL hι]
    · rw [perTanId, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨⟨l, e⟩, ⟨⟨u, hu, rfl⟩, hlat, he⟩, rfl⟩
      simp only at hlat he
      subst he
      refine Submodule.subset_span ⟨?_, fun k => ?_, rfl⟩
      · simp only [LinearMap.prodMap_apply, proj_inclL hι]; exact hu
      · simp only [LinearMap.prodMap_apply, proj_inclL hι]
        have := hlat (ι k); rwa [inclL_apply_ι hι] at this
  rw [heq]
  have hrat := h T hTab
  rw [hrat, Submodule.map_span]
  refine ratPair_of_span _ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨algLin_proj ι _ hv.2.1, algLin_proj ι _ hv.2.2⟩

end Incl

/-! ### The fibre -/

/-- If no nonzero member lies in `V` and `r ≤ 2`, then `dim (V ∩ fibre) ≤ 1`. -/
lemma finrank_inf_fibreV_le_one (hr : r ≤ 2) (V : Submodule ℂ (TanV d0 d1 m r))
    (hno : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan ≤ V → H.tan = ⊥) :
    finrank ℂ ↥(V ⊓ fibreV) ≤ 1 := by
  by_cases hle : (fibreV : Submodule ℂ (TanV d0 d1 m r)) ≤ V
  · have := hno (fibSub Ls M) (by rw [fibSub_tan]; exact hle)
    rw [fibSub_tan] at this; rw [this, inf_bot_eq, finrank_bot]; omega
  · have hf : finrank ℂ (fibreV : Submodule ℂ (TanV d0 d1 m r)) ≤ 2 := by
      refine (LinearMap.finrank_range_le _).trans ?_
      simp; omega
    have hlt : V ⊓ fibreV < fibreV :=
      lt_of_le_of_ne inf_le_right (fun h => hle (h ▸ inf_le_left))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega

namespace Frame

variable {H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M} (F : Frame H)

lemma finrank_comap_inf_fibreV (V : Submodule ℂ (TanV d0 d1 m r)) :
    finrank ℂ ↥(V.comap F.Psi ⊓ fibreV) ≤ finrank ℂ ↥(V ⊓ fibreV) := by
  have hmap : (V.comap F.Psi ⊓ fibreV).map F.Psi ≤ V ⊓ fibreV := by
    rintro _ ⟨x, ⟨hxV, hxF⟩, rfl⟩
    rw [SetLike.mem_coe, mem_fibreV_iff] at hxF
    have hx : x = (0, 0, 0, x.2.2.2) := Prod.ext hxF.1 (Prod.ext hxF.2.1 (Prod.ext hxF.2.2 rfl))
    refine ⟨hxV, ?_⟩
    rw [hx, F.Psi_fibre, SetLike.mem_coe, mem_fibreV_iff]; simp
  calc finrank ℂ ↥(V.comap F.Psi ⊓ fibreV)
      = finrank ℂ ↥((V.comap F.Psi ⊓ fibreV).map F.Psi) :=
        (Submodule.equivMapOfInjective _ F.Psi_injective _).finrank_eq
    _ ≤ _ := Submodule.finrank_mono hmap

end Frame

/-- `trans_premises` without `V ∩ fibre = 0` (and without its conclusion for `Psi⁻¹ V`). -/
lemma trans_premises2 (hM : AlgMat M) (hLA : LiftAlg Ls)
    {H' : SubgroupDataV (d0 := d0) (d1 := d1) Ls M}
    (F : Frame H') (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r))
    (hVT : V ≤ H'.tan) (hVdim : finrank ℂ V + 1 = finrank ℂ H'.tan) (hWV : W ≤ V)
    (hWrat : RatSubV W) (hYfg : Y.FG) (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M) :
    finrank ℂ (V.comap F.Psi) < fk0 H' + fk1 H' + fg H' + ff H' ∧
      W.comap F.Psi ≤ V.comap F.Psi ∧ RatSubV (W.comap F.Psi) ∧
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
  refine ⟨by omega, Submodule.comap_mono hWV, ?_,
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
