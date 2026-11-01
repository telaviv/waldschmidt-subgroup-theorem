/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVar5dRoy
import LSG.W88.AbVarSec7
import LSG.MEB.Rational

/-!
# A5.9e: the pivot transport and the §5d theorem on `G_a^{d₀} × G_m^{d₁} × ∏ B_k` (`STAGE_A5.md` §6.6 (a)3)

**`thm41SubAtB_of`**: `Thm41SubAtB An k₀ k₁ t` for every `t` rational for `perAb B`, from `Theorem41B` for the
subfamilies `B ∘ e` (`e` injective). For `t = 0` it is Roy (`thm41SubAtB_bot`); otherwise the pivot lemma
(`LSG.MEB.pivot`) gives `J` with `π_J|_t : t ≃ ∏_{k ∈ J} ℂ^{g_k}`, and the data are transported along
`ι = (id, id, σ)`, `σ = (π_J|_t)⁻¹`. Periods: `π_J (t ∩ perAb)` spans over `ℝ` and lies in the discrete `perAb (B ∘ e)`,
so it has finite index (`exists_nsmul_sigma_mem`, via `isNsmulIn_closure_basis`); hence `σ` maps `span_ℚ` periods
to `span_ℚ` periods, toric injectivity and the ranks transfer, and `σ(t″)` is rational for `perAb B`.

**`hyperplaneKappaB_of_41`**, **`hyperplaneKappaB_of_ME`**: the W88 §5d hypothesis on toric-injective hyperplanes from
`Theorem41B` of all subfamilies (resp. from `MultEstB` and Taylor packages), and `hrat`.
-/

open Complex Module LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.MEB (AbBlock perAb IsRatSub tanOf PerL)
open K5d (finrank_map_inj finrank_prodSub)

variable {m : ℕ} {B : Fin m → AbBlock}

set_option maxHeartbeats 3200000 in
-- the pivot transport
/-- **Theorem 4.1 for `G_a^{k₀} × G_m^{k₁} × B′` from Theorem 4.1 for the pivot subfamily.** -/
theorem thm41SubAtB_of (An : ∀ k, AbBlockAn (B k))
    (h41 : ∀ (n : ℕ) (e : Fin n → Fin m), Function.Injective e → Theorem41B (fun i => An (e i)))
    (k0 k1 : ℕ) (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) (ht : IsRatSub (perAb B) t) :
    Thm41SubAtB An k0 k1 t := by
  classical
  intro V W Y hVT hdim hWV hWrat hYfg hY hTor hNR
  rcases hNR with hNR | hbot
  swap
  · subst hbot
    exact thm41SubAtB_bot An k0 k1 V W Y hVT hdim hWV hWrat hYfg hY hTor (Or.inr rfl)
  obtain ⟨J, hJinj, hJsurj⟩ := LSG.MEB.pivot ht
  set n := J.card with hn
  let eo := J.orderEmbOfFin (rfl : J.card = n)
  set e : Fin n → Fin m := fun i => eo i with he_def
  have he : Function.Injective e := eo.injective
  have heJ : ∀ i, e i ∈ J := fun i => J.orderEmbOfFin_mem rfl i
  have hJe : ∀ k ∈ J, ∃ i, e i = k := fun k hk => by
    have : k ∈ Set.range eo := by rw [Finset.range_orderEmbOfFin]; exact hk
    exact this
  have H41 := h41 n e he
  set B' : Fin n → AbBlock := fun i => B (e i) with hB'
  set An' : ∀ i, AbBlockAn (B' i) := fun i => An (e i) with hAn'
  -- the projection and its section on `t`
  let pJ : (∀ k, Fin (B k).g → ℂ) →ₗ[ℂ] (∀ i, Fin (B' i).g → ℂ) := LinearMap.pi fun i => LinearMap.proj (e i)
  have pJ_apply : ∀ z i, pJ z i = z (e i) := fun _ _ => rfl
  have hinjt : ∀ z ∈ t, pJ z = 0 → z = 0 := fun z hz h => hJinj z hz fun k hk => by
    obtain ⟨i, rfl⟩ := hJe k hk; exact congrFun h i
  let ext : (∀ i, Fin (B' i).g → ℂ) → (∀ k, Fin (B k).g → ℂ) := fun w => ∑ i, Pi.single (e i) (w i)
  have ext_e : ∀ w j, ext w (e j) = w j := by
    intro w j
    simp only [ext, Finset.sum_apply]
    rw [Finset.sum_eq_single j (fun i _ hij => Pi.single_eq_of_ne (fun h => hij (he h).symm) _)
      (by simp), Pi.single_eq_same]
  have hsurjt : ∀ w, ∃ z ∈ t, pJ z = w := fun w => by
    obtain ⟨z, hz, hzy⟩ := hJsurj (ext w)
    exact ⟨z, hz, funext fun j => by rw [pJ_apply, hzy _ (heJ j), ext_e]⟩
  let pJt : t ≃ₗ[ℂ] (∀ i, Fin (B' i).g → ℂ) := LinearEquiv.ofBijective (pJ ∘ₗ t.subtype)
    ⟨fun a b h => Subtype.ext (sub_eq_zero.mp (hinjt _ (t.sub_mem a.2 b.2)
        (by simpa [map_sub, sub_eq_zero] using h))),
      fun w => by obtain ⟨z, hz, rfl⟩ := hsurjt w; exact ⟨⟨z, hz⟩, rfl⟩⟩
  let σ : (∀ i, Fin (B' i).g → ℂ) →ₗ[ℂ] (∀ k, Fin (B k).g → ℂ) := t.subtype ∘ₗ pJt.symm.toLinearMap
  have hσt : ∀ w, σ w ∈ t := fun w => (pJt.symm w).2
  have hpσ : ∀ w, pJ (σ w) = w := fun w => pJt.apply_symm_apply w
  have hσp : ∀ z ∈ t, σ (pJ z) = z := fun z hz => by
    have : pJt.symm (pJt ⟨z, hz⟩) = ⟨z, hz⟩ := pJt.symm_apply_apply _
    exact congrArg Subtype.val this
  have hσinj : Function.Injective σ := fun a b h => by rw [← hpσ a, ← hpσ b, h]
  have hft : finrank ℂ t = ∑ i, (B' i).g := by
    rw [pJt.finrank_eq]; simp [Module.finrank_pi_fintype]
  -- finite index of `π_J (t ∩ perAb)` in `perAb (B ∘ e)`
  have hfin : ∀ w ∈ perAb B', ∃ N : ℕ, 0 < N ∧ σ (N • w) ∈ perAb B := by
    intro w hw
    let L : AddSubgroup (∀ i, Fin (B' i).g → ℂ) :=
      (t.toAddSubgroup ⊓ perAb B).map pJ.toAddMonoidHom
    have hLle : L ≤ perAb B' := by
      rintro _ ⟨z, ⟨-, hz⟩, rfl⟩ i _
      exact hz (e i) (Set.mem_univ _)
    have hLset : (L : Set (∀ i, Fin (B' i).g → ℂ)) = pJ '' {z | z ∈ t ∧ z ∈ perAb B} := by
      ext x; simp [L, AddSubgroup.coe_map]
    have hLspan : Submodule.span ℝ (L : Set (∀ i, Fin (B' i).g → ℂ)) = ⊤ := by
      rw [hLset, eq_top_iff]
      intro w' _
      obtain ⟨z, hz, rfl⟩ := hsurjt w'
      have hz' : z ∈ t.restrictScalars ℝ := hz
      rw [ht] at hz'
      have hm : (Submodule.span ℝ {z | z ∈ t ∧ z ∈ perAb B}).map (pJ.restrictScalars ℝ) ≤
          Submodule.span ℝ (pJ '' {z | z ∈ t ∧ z ∈ perAb B}) := by
        rw [Submodule.map_span]; exact le_rfl
      exact hm ⟨z, hz', rfl⟩
    obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent ℝ (L : Set (∀ i, Fin (B' i).g → ℂ))
    have : Finite s := hli.finite
    let b : Basis s ℝ (∀ i, Fin (B' i).g → ℂ) := Basis.mk hli (by rw [Subtype.range_coe, hspan, hLspan])
    have hb : ∀ i, b i ∈ perAb B' := fun i => by rw [Basis.mk_apply]; exact hLle (hsL i.2)
    have := LSG.MEB.discreteTopology_perAb (B := B')
    obtain ⟨N, hN, hNw⟩ := isNsmulIn_closure_basis b (perAb B') hb w hw
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
  have hσspan : ∀ w ∈ Submodule.span ℚ (perAb B' : Set (∀ i, Fin (B' i).g → ℂ)),
      σ w ∈ Submodule.span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ)) := by
    intro w hw
    have hle : (Submodule.span ℚ (perAb B' : Set (∀ i, Fin (B' i).g → ℂ))).map (σ.restrictScalars ℚ) ≤
        Submodule.span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨w', hw', rfl⟩
      obtain ⟨N, hN, hNw⟩ := hfin w' hw'
      refine mem_span_rat_of_nsmul hN (Submodule.subset_span ?_)
      change N • σ w' ∈ perAb B
      rw [← map_nsmul]; exact hNw
    exact hle ⟨w, hw, rfl⟩
  have hpJspan : ∀ z ∈ Submodule.span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ)),
      pJ z ∈ Submodule.span ℚ (perAb B' : Set (∀ i, Fin (B' i).g → ℂ)) := by
    intro z hz
    have hle : (Submodule.span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ))).map (pJ.restrictScalars ℚ) ≤
        Submodule.span ℚ (perAb B' : Set (∀ i, Fin (B' i).g → ℂ)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨z', hz', rfl⟩
      exact Submodule.subset_span fun i _ => hz' (e i) (Set.mem_univ _)
    exact hle ⟨z, hz, rfl⟩
  -- the transport maps
  let ι : MEB.Tan k0 k1 B' →ₗ[ℂ] MEB.Tan k0 k1 B :=
    (LinearMap.fst ℂ _ _).prod (((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)).prod
      (σ.comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))))
  let π : MEB.Tan k0 k1 B →ₗ[ℂ] MEB.Tan k0 k1 B' :=
    (LinearMap.fst ℂ _ _).prod (((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)).prod
      (pJ.comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))))
  have ι_apply : ∀ x, ι x = (x.1, x.2.1, σ x.2.2) := fun _ => rfl
  have π_apply : ∀ x, π x = (x.1, x.2.1, pJ x.2.2) := fun _ => rfl
  have hπι : ∀ x, π (ι x) = x := fun x => by rw [ι_apply, π_apply, hpσ]
  have hinj : Function.Injective ι := fun x y h => by rw [← hπι x, ← hπι y, h]
  set R := tanBB k0 k1 t with hR
  have hιπ : ∀ v ∈ R, ι (π v) = v := fun v hv => by
    rw [π_apply, ι_apply, hσp _ hv.2.2]
  have hιR : ∀ x, ι x ∈ R := fun x => ⟨Submodule.mem_top, Submodule.mem_top, hσt _⟩
  have hrange : LinearMap.range ι = R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact hιR x
    · intro v hv; exact ⟨π v, hιπ v hv⟩
  have hmap : ∀ S : Submodule ℂ (MEB.Tan k0 k1 B), S ≤ R → (S.comap ι).map ι = S := by
    intro S hS; rw [Submodule.map_comap_eq, hrange, inf_eq_right.mpr hS]
  have hιTA : ∀ (c : Fin k1 → ℚ) (w : ∀ i, Fin (B' i).g → ℂ),
      ι (inTB k0 k1 B' c + inAb k0 k1 B' w) = inTB k0 k1 B c + inAb k0 k1 B (σ w) := by
    intro c w
    rw [ι_apply]
    refine Prod.ext (by simp [inTB_apply, inAb_apply]) (Prod.ext (by simp [inTB_apply, inAb_apply]) ?_)
    simp [inTB_apply, inAb_apply]
  set Vs := V.comap ι with hVs_def
  set Ws := W.comap ι with hWs_def
  set Ys := Y.map π.toAddMonoidHom with hYs_def
  have hWR : W ≤ R := hWV.trans hVT
  have hVs : finrank ℂ Vs = finrank ℂ V := by rw [← finrank_map_inj hinj, hmap V hVT]
  have hWs : finrank ℂ Ws = finrank ℂ W := by rw [← finrank_map_inj hinj, hmap W hWR]
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
      · rw [π_apply]; exact hs.2.1
      · rw [π_apply]; exact hs.2.2.1
      · rw [π_apply]; exact fun i j => hs.2.2.2 (e i) j
    · rw [Submodule.span_le]; exact fun x hx => hx.1
  have hYsfg : Ys.FG := K11.fg_map_addSubgroup hYfg _
  have hYsmem : ∀ x ∈ Ys, x ∈ Vs ∧ x ∈ LamB k0 k1 An' := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyV, hyL⟩ := hY y hy
    refine ⟨?_, ?_⟩
    · change ι (π y) ∈ V
      rw [hιπ y (hVT hyV)]; exact hyV
    · change π y ∈ LamB k0 k1 An'
      rw [π_apply]
      exact ⟨hyL.1, hyL.2.1, fun i => hyL.2.2 (e i)⟩
  -- the `ℚ`-structures
  set ιq := ι.restrictScalars ℚ with hιq
  have hinjq : Function.Injective ιq := hinj
  set Yq := Submodule.span ℚ (Y : Set (MEB.Tan k0 k1 B)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  have hYR : Yq ≤ R.restrictScalars ℚ := Submodule.span_le.mpr fun y hy => hVT (hY y hy).1
  have hYmap : (Submodule.span ℚ (Ys : Set (MEB.Tan k0 k1 B'))).map ιq = Yq := by
    rw [Submodule.map_span]; congr 1
    ext v; constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      change ι (π y) ∈ Y
      rw [hιπ y (hVT (hY y hy).1)]; exact hy
    · intro hv; exact ⟨π v, ⟨v, hv, rfl⟩, hιπ v (hVT (hY v hv).1)⟩
  have hPmap : (OmB k0 k1 B').map ιq = OmB k0 k1 B ⊓ R.restrictScalars ℚ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, hιR x⟩
      obtain ⟨c, w, hw, rfl⟩ := mem_OmB hx
      change ι _ ∈ _
      rw [hιTA]
      exact Submodule.add_mem _ (inTB_mem_span_Per _) (inAb_mem_OmB (hσspan w hw))
    · rintro x ⟨hxΩ, hxR⟩
      obtain ⟨c, z, hz, rfl⟩ := mem_OmB hxΩ
      have hzt : z ∈ t := by
        have h := hxR.2.2
        simpa [inTB_apply, inAb_apply] using h
      refine ⟨inTB k0 k1 B' c + inAb k0 k1 B' (pJ z), Submodule.add_mem _ (inTB_mem_span_Per c)
        (inAb_mem_OmB (hpJspan z hz)), ?_⟩
      change ι _ = _
      rw [hιTA, hσp z hzt]
  have rk1 : rk Ys = rk Y := by rw [rk, ← finrank_map_inj hinjq, hYmap]; rfl
  have rk2 : rk (Ys ⊓ MEB.Per k0 k1 B') = rk (Y ⊓ MEB.Per k0 k1 B) := by
    rw [rk, rk, K11.span_inf_addSubgroup, K11.span_inf_addSubgroup, ← finrank_map_inj hinjq,
      Submodule.map_inf _ hinjq, hYmap, hPmap, inf_comm (OmB k0 k1 B), ← inf_assoc, inf_eq_left.mpr hYR]
  have hΛle' : ∀ i, latF An' i ≤ (B' i).per := fun i => (An' i).lat_le
  have hΛ' : ∀ i, IsNsmulIn (latF An' i) (B' i).per := fun i => (An' i).lat_nsmul
  have rk2' : rk (Ys ⊓ PerL k0 k1 B' (latF An')) = rk (Y ⊓ MEB.Per k0 k1 B) := by
    rw [LSG.MEB.rk_inf_perL hΛle' hΛ', rk2]
  have hTors : TorInjB Vs := by
    intro v hv hvP hv1
    have h1 : ι v ∈ OmB k0 k1 B := (hPmap.le ⟨v, hvP, rfl⟩).1
    have h2 : (ι v).2.1 = 0 := by rw [ι_apply]; exact hv1
    exact hinj (by rw [hTor (ι v) hv h1 h2, map_zero])
  -- the theorem for the subfamily
  obtain ⟨Hs, hHsP, hτs, hineqs⟩ := H41 k0 k1 Vs Ws Ys (by rw [hVs, ← hft]; exact hdim)
    (Submodule.comap_mono hWV) hWsrat hYsfg hYsmem hTors (by rw [rk2', hVs]; exact hNR)
  -- the subgroup `G''`
  have hσt_rat : IsRatSub (perAb B) (Hs.t.map σ) := by
    unfold IsRatSub
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : u ∈ Hs.t.restrictScalars ℝ := hu
      rw [Hs.t_rat] at hu'
      have hle : (Submodule.span ℝ {z | z ∈ Hs.t ∧ z ∈ perAb B'}).map (σ.restrictScalars ℝ) ≤
          Submodule.span ℝ {z | z ∈ Hs.t.map σ ∧ z ∈ perAb B} := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨u', ⟨hu't, hu'P⟩, rfl⟩
        obtain ⟨N, hN, hNu⟩ := hfin u' hu'P
        have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        have e1 : σ u' = (N : ℝ)⁻¹ • σ (N • u') := by
          rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN', one_smul]
        change σ u' ∈ _
        rw [e1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨⟨N • u', Hs.t.toAddSubgroup.nsmul_mem hu't N, rfl⟩, hNu⟩)
      exact hle ⟨u, hu', rfl⟩
    · rw [Submodule.span_le]; exact fun z hz => hz.1
  let H : SubgroupDataB k0 k1 B :=
    { h0 := Hs.h0, U := Hs.U, t := Hs.t.map σ, h0_rat := Hs.h0_rat, t_rat := hσt_rat }
  have hTan : Hs.tan.map ι = H.tan := by
    ext ⟨u, v, z⟩
    rw [Submodule.mem_map]
    simp only [H, SubgroupDataB.tan, tanOf, Submodule.mem_prod]
    constructor
    · rintro ⟨⟨a, c, w⟩, ⟨ha, hc, hw⟩, hx⟩
      rw [ι_apply] at hx
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := ⟨congrArg Prod.fst hx,
        congrArg (fun p => p.2.1) hx, congrArg (fun p => p.2.2) hx⟩
      exact ⟨ha, hc, w, hw, rfl⟩
    · rintro ⟨ha, hc, w, hw, rfl⟩
      exact ⟨(u, v, w), ⟨ha, hc, hw⟩, rfl⟩
  have hHt : H.t ≤ t := by rintro _ ⟨w, -, rfl⟩; exact hσt w
  have hHR : H.tan ≤ R := fun x hx => ⟨Submodule.mem_top, Submodule.mem_top, hHt hx.2.2⟩
  have hWinf : finrank ℂ ↥(Ws ⊓ Hs.tan) = finrank ℂ ↥(W ⊓ H.tan) := by
    rw [← finrank_map_inj hinj, Submodule.map_inf _ hinj, hmap W hWR, hTan]
  have hfHt : finrank ℂ H.t = finrank ℂ Hs.t := finrank_map_inj hσinj Hs.t
  have hTq : (Submodule.span ℚ ((Hs.tan.toAddSubgroup : AddSubgroup (MEB.Tan k0 k1 B')) :
      Set (MEB.Tan k0 k1 B'))).map ιq = H.tan.restrictScalars ℚ := by
    rw [K11.span_submodule_coe, ← hTan]; rfl
  have hspanL' : Submodule.span ℚ (PerL k0 k1 B' (latF An') : Set (MEB.Tan k0 k1 B')) = OmB k0 k1 B' :=
    LSG.MEB.span_perL hΛle' hΛ'
  have rk3 : rk (Ys ⊓ (Hs.tan.toAddSubgroup ⊔ PerL k0 k1 B' (latF An'))) =
      rk (Y ⊓ (H.tan.toAddSubgroup ⊔ MEB.Per k0 k1 B)) := by
    rw [rk, rk, K11.span_inf_addSubgroup, K11.span_sup_addSubgroup, hspanL', ← finrank_map_inj hinjq,
      Submodule.map_inf _ hinjq, Submodule.map_sup, hYmap, hTq, hPmap, K11.span_inf_addSubgroup,
      K11.span_sup_addSubgroup, K11.span_submodule_coe]
    have hT''q : H.tan.restrictScalars ℚ ≤ R.restrictScalars ℚ := fun x hx => hHR hx
    rw [← sup_inf_assoc_of_le _ hT''q, inf_comm _ (R.restrictScalars ℚ), ← inf_assoc,
      inf_eq_left.mpr hYR]
  -- numerics
  have hδ2 : Hs.δ2 = finrank ℂ t - finrank ℂ H.t := by
    simp only [SubgroupDataB.δ2]; rw [hfHt, hft]
  have hδ : H.δBt t = Hs.δ := by
    simp only [SubgroupDataB.δBt, SubgroupDataB.δ, SubgroupDataB.δ0, SubgroupDataB.δ1, SubgroupDataB.δ2]
    rw [hfHt, hft]
  refine ⟨H, hHt, ?_, ?_, ?_⟩
  · rw [hδ]; exact hHsP
  · rw [hδ, ← hWs, ← hWinf]; exact hτs
  · rw [rk1, rk3, rk2', hVs, hWs, hWinf, ← hft, hδ2] at hineqs
    rw [hδ]
    exact hineqs

/-! ### The §5d theorem -/

variable {d₀ d₁ : ℕ}

/-- **W88 §5d on toric-injective hyperplanes from Theorem 4.1 for every subfamily** (and `hrat`). -/
theorem hyperplaneKappaB_of_41 (An : ∀ k, AbBlockAn (B k))
    (h41 : ∀ (n : ℕ) (e : Fin n → Fin m), Function.Injective e → Theorem41B (fun i => An (e i)))
    (hrat : ∀ (W : Submodule ℂ (MEB.Tan d₀ d₁ B)) (H : SubgroupDataB d₀ d₁ B),
      RationalOverQbarB W → RationalOverQbarB (W ⊓ H.tan)) :
    HyperplaneKappaOnLsg (gmB d₀ d₁ An) TorInjB :=
  hyperplaneKappaB_of An (fun H' => trans41B An H' (thm41SubAtB_of An h41 _ _ H'.t H'.t_rat)) hrat

/-- **W88 §5d on toric-injective hyperplanes for `G_a^{d₀} × G_m^{d₁} × ∏ B_k` from the multiplicity estimate**, the
analytic and Taylor packages, and `hrat`. -/
theorem hyperplaneKappaB_of_ME (hME : LSG.MEB.MultEstB) (An : ∀ k, AbBlockAn (B k)) (Tay : TayAll B)
    (hrat : ∀ (W : Submodule ℂ (MEB.Tan d₀ d₁ B)) (H : SubgroupDataB d₀ d₁ B),
      RationalOverQbarB W → RationalOverQbarB (W ⊓ H.tan)) :
    HyperplaneKappaOnLsg (gmB d₀ d₁ An) TorInjB :=
  hyperplaneKappaB_of_41 An (fun _ e _ => theorem41B_of hME (fun i => An (e i))
    (fun K _ _ ι i => Tay K ι (e i))) hrat

end LSG.W88
