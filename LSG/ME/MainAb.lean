import Mathlib
import LSG.ME.MainAbAux
import LSG.ME.SliceWustCoset
import LSG.ME.MultEstStmt
import StrongSix.M2.Bezout

/-!
# The multiplicity estimate `MultEstAb` (STAGE2 §11)

**`multEstAb : MultEstAb`**, Roy §8.4.1 (StrongSix `multEstB`) on the multi-cone, with
relevant radicals for the geometry and affine slices `sl α` for the Hilbert functions:

1. chain v2 and the relevant pigeonhole (`exists_flat_rel`); a relevant prime `p` of maximal
   dimension (`exists_relevant_prime`), `V = Z(p)`, `GV = stabG V`, `H⁰ = GV⁰`;
2. Roy's ideal `A`, formal order `> T` on `SG = ⋃_{s ∈ S} (s + GV)` (`hAVO2`), multihomogeneous
   generators (`isHomE_phOp`, `isHomE_transl`), hence `A ≤ VOg Dmix (I(SG)) T` (`mem_VOg_mix`);
3. the component step: `Zs α A ⊆ ⋃_{a ∈ R} (a + GV)` (`Zs_subset_transl`, `component_rel`);
4. chart forms `ℓ_k = V_k + α_k W_k` good for all cosets involved (`exists_good_alpha`);
5. dimensions: `hdim (sl α A) ≤ dim T′` (slice Nullstellensatz `radical_sl`,
   `hdim_vanishP_cosets_le`), `hdim (sl α I(SG)) ≥ dim T′` (coset count `hfun_sum_cosets_P` and
   `hfun_P_coset_ge`), so both are `dim T′ = t₀ + t₁ + t₂`;
6. degrees: coset count (A2), sliced Wüstholz `wustholz_cosets_sl` (A1), Bézout for
   `sl α A = sl α I_G ⊔ (generators)` (A3), `hdata_slIG` (A4); `final_arith_ab`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.W88 (Tan)
open StrongSix.M2 (FLE hfun hdata hdata_le_of_le)

namespace LSG.ME

/-- **The multiplicity estimate on `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` over `ℂ`.** -/
theorem multEstAb : MultEstAb := by
  intro d₀ d₁ m Ls
  refine ⟨CstAb d₀ d₁ m, fun W S P T D₀ D₁ D₂ hS hPh hPD hPI hT hD₀ hD₁ hD₂ hvan => ?_⟩
  classical
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hΔ := discr_g2L Ls
  set n := d₀ + d₁ + m with hn
  set D : Blk m → ℕ := Dfun (4 * D₀) (4 * D₁) (4 * D₂) with hDdef
  have hD : ∀ i, 1 ≤ D i := fun i => by
    cases i <;> simp [D, Dfun] <;> omega
  /- 1. The chain and the relevant pigeonhole. -/
  have hlast : Lr2 (g2L Ls) (g3L Ls) W S P T n ≤
      vanish ({0} : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) :=
    Lr2_le_vanish_zero hΔ hPh hvan
  obtain ⟨r, hr, hflat⟩ := exists_flat_rel hΔ D hD hPh hS hPI hlast
  have hne : relI (g2L Ls) (g3L Ls) (Lr2 (g2L Ls) (g3L Ls) W S P T (r + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top (vanish_ne_top (Set.singleton_nonempty 0))
      ((relI_mono (Lr2_mono' hS (by omega : r + 1 ≤ n))).trans (relI_le_vanish_zero hlast))
  obtain ⟨p, hp, hJp, hpdim, hpv⟩ := exists_relevant_prime D hD hne
  set V : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) := zeros (p : Set _) with hVdef
  have hV : IsZClosed V := isZClosed_zeros _
  have hVp : (vanish V).IsPrime := hpv ▸ hp
  set GV := stabG V with hGVdef
  have hGVs : IsSubgroupG GV := stabG_isSubgroup h2 hΔ hV
  have hGVc : IsZClosed GV := isZClosed_stabG h2 hΔ hV
  have hLp : Lr2 (g2L Ls) (g3L Ls) W S P T (r + 1) ≤ p := (le_relI _).trans hJp
  /- 2. Roy's ideal `A`. -/
  set F₀ : Set (MvPolynomial (Var d₀ d₁ m) ℂ) := {Q' | ∃ Q ∈ gensR2 (g2L Ls) (g3L Ls) W S P T r,
    ∃ v ∈ V, ∃ c, Q' = τ (g2L Ls) (g3L Ls) v c Q} with hF₀
  set A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
    IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔ Ideal.span F₀ with hA
  set SG := ⋃ s ∈ S, gtransl s GV with hSGdef
  have hAVO : A ≤ ordIdeal (g2L Ls) (g3L Ls) W T SG :=
    hAVO2 hΔ W S hPh T r hLp GV fun u hu v hv => hu v hv
  have hAVOg : A ≤ VOg (Dmix Ls) (Wmix W) (vanish SG) T := by
    refine sup_le (IG_le_VOg_mix W T SG) (Ideal.span_le.mpr ?_)
    rintro _ ⟨Q, hQ, v, hv, c, rfl⟩
    obtain ⟨σ, hσ, w, hw, κ, hκ, c₁, c₂, rfl⟩ := hQ
    have hx := isHomE_transl (isHomE_phOp (g₂ := g2L Ls) (g₃ := g3L Ls) σ w c₁ c₂ κ hPh) v c
    exact mem_VOg_mix W hx fun g hg => vanCan_of_ordGt hx
      (hAVO (Ideal.mem_sup_right (Ideal.subset_span ⟨_, ⟨σ, hσ, w, hw, κ, hκ, c₁, c₂, rfl⟩,
        v, hv, c, rfl⟩)) g hg)
  have hAJ : A ≤ vanish SG := hAVOg.trans (VOg_le (Dv := Dmix Ls) (W := Wmix W) (J := vanish SG) T)
  /- 3. Roy's component step. -/
  have hdimV : (hdata blk D ℂ (vanish V)).1 =
      (hdata blk D ℂ (relI (g2L Ls) (g3L Ls) (Lr2 (g2L Ls) (g3L Ls) W S P T r))).1 := by
    rw [hpv, hpdim, hflat]
  obtain ⟨R, hR⟩ := component_rel h2 hΔ D hD hV hVp hdimV
  /- 4. Cosets of `H⁰`. -/
  set H0' := H0 Ls hGVs hGVc with hH0'
  have hH0s : IsSubgroupG H0' := H0_isSubgroup hGVs hGVc
  have hH0c : IsZClosed H0' := isZClosed_H0 hGVs hGVc
  have hH0p : (vanish H0').IsPrime := vanish_H0_isPrime hGVs hGVc
  obtain ⟨Rc, hRcGV, hGVcov⟩ := finite_cosets_H0 hGVs hGVc
  have hcov := biUnion_gtransl_cover hGVs (H0_subset hGVs hGVc) Rc hRcGV hGVcov
  obtain ⟨Rs, -, hRsU, hdist⟩ := exists_reps_G hH0s ((S ×ˢ Rc).image fun p => p.2 + p.1)
  have hSG : SG = ⋃ a ∈ Rs, gtransl a H0' := by rw [hRsU, ← hcov]
  set R' := (R ×ˢ Rc).image fun p => p.2 + p.1 with hR'
  have hRcov : (⋃ a ∈ R, gtransl a GV) = ⋃ b ∈ R', gtransl b H0' := hcov R
  /- 5. The chart forms. -/
  obtain ⟨α, hα⟩ := exists_good_alpha ⟨0, hH0s.zero_mem⟩ (R' ∪ Rs)
  have hαR' : ∀ a ∈ R', ∀ k, lsl α k ∉ vanish (gtransl a H0') := fun a ha =>
    hα a (Finset.mem_union_left _ ha)
  have hαRs : ∀ a ∈ Rs, ∀ k, lsl α k ∉ vanish (gtransl a H0') := fun a ha =>
    hα a (Finset.mem_union_right _ ha)
  /- 6. Nontriviality of the slices. -/
  have h0SG : (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) ∈ SG :=
    Set.mem_biUnion hS ⟨0, hGVs.zero_mem, add_zero 0⟩
  have hl0 : ∀ k, lval α (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) k ≠ 0 := fun k => by
    simp [lval, LSG.Elliptic.rep, LSG.Elliptic.O]
  have hPSG : vanishP Finset.univ α SG ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial (Var d₀ d₁ m) ℂ) ∈ vanishP Finset.univ α SG :=
      htop ▸ Submodule.mem_top
    have := mem_vanishP.mp h1 0 h0SG (fun k _ => hl0 k) 1
    simp at this
  set J := vanish SG with hJdef
  have hslJP : sl α J ≤ vanishP Finset.univ α SG := sl_vanish_le_vanishP α SG
  have hslAJ : sl α A ≤ sl α J := sup_le_sup_right hAJ _
  have hslJ : sl α J ≠ ⊤ := ne_top_of_le_ne_top hPSG hslJP
  have hslA : sl α A ≠ ⊤ := ne_top_of_le_ne_top hslJ hslAJ
  /- 7. The obstruction and its dimensions. -/
  set O : ObstrData d₀ d₁ Ls := ObstrData.ofSubgroup hGVs hGVc with hO
  set e := finrank ℂ (lieAlg Ls hGVs hGVc) with he
  set t₀ := finrank ℂ (StrongSix.M2.linV (ML Ls hGVs hGVc)) with ht₀
  set t₁ := d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hGVs hGVc))) with ht₁
  set t₂ := finrank ℂ ((lieAlg Ls hGVs hGVc).comap (inAbL (d₀ := d₀) (d₁ := d₁))) with ht₂
  have hOh0 : finrank ℂ O.h0 = t₀ := by
    change finrank ℂ ((lieAlg Ls hGVs hGVc).comap (LinearMap.inl ℂ _ _)) = _
    rw [← linV_ML_eq hGVs hGVc]
  have hOt : finrank ℂ O.t = t₂ := rfl
  have hOU : d₁ - finrank ℚ O.U = t₁ := rfl
  have hOtan : O.tan = lieAlg Ls hGVs hGVc := ObstrData.ofSubgroup_tan hGVs hGVc
  have he_sum : e = t₀ + t₁ + t₂ := by
    have h1 := finrank_torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hGVs hGVc)))
    have h2' : e = finrank ℂ O.h0 + (finrank ℂ (LSG.W88.torusLie O.U) + finrank ℂ O.t) := by
      rw [he, ← hOtan, ObstrData.tan, finrank_submodule_prod, finrank_submodule_prod]
    rw [h2', hOh0, hOt]
    have : finrank ℂ (LSG.W88.torusLie O.U) = t₁ := by
      change finrank ℂ (LSG.W88.torusLie (StrongSix.M2.qspan
        (StrongSix.M2.latt (ML Ls hGVs hGVc)))) = _
      omega
    omega
  /- 8. `hdim (sl α A) ≤ e`. -/
  have hdimA_le : (hdata blk D ℂ (sl α A)).1 ≤ e := by
    have hrad := radical_sl h2 hΔ α (le_sup_left : IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤ A)
    have hZs : Zs (g₂ := g2L Ls) (g₃ := g3L Ls) α A ⊆ ⋃ b ∈ R', gtransl b H0' := by
      intro g hg
      rw [← hRcov]
      exact hR (Zs_subset_transl hΔ α W S hPh T r V hg)
    have hPle : vanishP Finset.univ α (⋃ b ∈ R', gtransl b H0') ≤ (sl α A).radical := by
      rw [hrad]
      intro Q hQ
      refine (StrongSix.M2.mem_vanish' _).mpr fun g hg => ?_
      have := mem_vanishP.mp hQ g (hZs hg) (fun k _ => hg.1 k) 1
      rwa [coords_nscal_univ hg.1] at this
    have hradne : (sl α A).radical ≠ ⊤ := fun h => hslA (Ideal.radical_eq_top.mp h)
    have h1 := hdata_le_of_le blk D ℂ hPle hradne
    rw [StrongSix.M2.hdim_radical blk D hD hslA] at h1
    have h2'' := hdim_vanishP_cosets_le h2 hΔ D hD hH0c hH0p R' hαR'
      (ne_top_of_le_ne_top hradne hPle)
    rw [hdim_H0 hGVs hGVc D hD] at h2''
    rcases h1 with h1 | ⟨h1, -⟩ <;> omega
  /- 9. The lower bound through the cosets (A2). -/
  have hRs_ne : Rs.Nonempty := by
    have : (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) ∈ ⋃ a ∈ Rs, gtransl a H0' := hSG ▸ h0SG
    simp only [Set.mem_iUnion] at this
    obtain ⟨a, ha, -⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨c₁, hc₁⟩ := hfun_sum_cosets_P h2 hΔ D hD α hH0c hH0p Rs hαRs
    fun a ha b hb hab => not_gtransl_subset hH0s (hdist a ha b hb hab)
  have hcos : ∀ a ∈ Rs, ∀ t,
      (t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ * (t * (4 * D₂) + 1) ^ t₂ ≤
        4 ^ m * hfun blk D ℂ (vanishP Finset.univ α (gtransl a H0')) (2 * t) := by
    intro a ha t
    obtain ⟨tAb, -, htAb, hb⟩ := hfun_P_coset_ge hGVs hGVc α a (hαRs a ha) (4 * D₀) (4 * D₁)
      (4 * D₂)
    have : finrank ℂ tAb = t₂ := by
      have : tAb = (lieAlg Ls hGVs hGVc).comap (inAbL (d₀ := d₀) (d₁ := d₁)) := by
        ext z; rw [htAb, Submodule.mem_comap, inAbL_apply]
      rw [this]
    rw [← this]
    exact hb t
  set κ := t₀ ^ t₀ * t₁ ^ t₁ with hκ
  have hκ0 : 0 < κ := by
    have hpow : ∀ x : ℕ, 0 < x ^ x := fun x => by
      rcases Nat.eq_zero_or_pos x with h | h
      · rw [h]; simp
      · exact Nat.pow_pos h
    exact Nat.mul_pos (hpow t₀) (hpow t₁)
  have hlowJ : ∀ t : ℕ, (lin3 Rs.card (4 * D₀) (4 * D₁) (4 * D₂) t₀ t₁ t₂).eval (t : ℤ) ≤
      ((κ * 4 ^ m : ℕ) : ℤ) * (hfun blk D ℂ (sl α J) (2 * t + c₁) : ℤ) := by
    intro t
    rw [lin3_eval]
    have hsum : Rs.card * ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ *
        (t * (4 * D₂) + 1) ^ t₂) ≤ 4 ^ m * hfun blk D ℂ (sl α J) (2 * t + c₁) := by
      calc Rs.card * ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ *
            (t * (4 * D₂) + 1) ^ t₂)
          = ∑ _a ∈ Rs, ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ *
            (t * (4 * D₂) + 1) ^ t₂) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ a ∈ Rs, 4 ^ m * hfun blk D ℂ (vanishP Finset.univ α (gtransl a H0')) (2 * t) :=
            Finset.sum_le_sum fun a ha => hcos a ha t
        _ = 4 ^ m * ∑ a ∈ Rs, hfun blk D ℂ (vanishP Finset.univ α (gtransl a H0')) (2 * t) := by
            rw [Finset.mul_sum]
        _ ≤ 4 ^ m * hfun blk D ℂ (vanishP Finset.univ α (⋃ a ∈ Rs, gtransl a H0'))
              (2 * t + c₁) := Nat.mul_le_mul_left _ (hc₁ (2 * t))
        _ ≤ 4 ^ m * hfun blk D ℂ (sl α J) (2 * t + c₁) := by
            refine Nat.mul_le_mul_left _ (StrongSix.M2.hfun_mono blk D ℂ ?_ _)
            rw [← hSG]; exact hslJP
    have hpb : (4 * D₀ * t + 1) ^ t₀ * (4 * D₁ * t + 1) ^ t₁ ≤
        κ * ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁) := by
      have e1 := StrongSix.M2.pow_div_bound (t * (4 * D₀)) t₀
      have e2 := StrongSix.M2.pow_div_bound (t * (4 * D₁)) t₁
      rw [mul_pow] at e1 e2
      calc (4 * D₀ * t + 1) ^ t₀ * (4 * D₁ * t + 1) ^ t₁
          = (t * (4 * D₀) + 1) ^ t₀ * (t * (4 * D₁) + 1) ^ t₁ := by ring
        _ ≤ (t₀ ^ t₀ * (t * (4 * D₀) / t₀ + 1) ^ t₀) * (t₁ ^ t₁ * (t * (4 * D₁) / t₁ + 1) ^ t₁) :=
            Nat.mul_le_mul e1 e2
        _ = _ := by ring
    have : Rs.card * (4 * D₀ * t + 1) ^ t₀ * (4 * D₁ * t + 1) ^ t₁ * (4 * D₂ * t + 1) ^ t₂ ≤
        κ * 4 ^ m * hfun blk D ℂ (sl α J) (2 * t + c₁) := by
      calc Rs.card * (4 * D₀ * t + 1) ^ t₀ * (4 * D₁ * t + 1) ^ t₁ * (4 * D₂ * t + 1) ^ t₂
          = Rs.card * ((4 * D₀ * t + 1) ^ t₀ * (4 * D₁ * t + 1) ^ t₁) *
            (t * (4 * D₂) + 1) ^ t₂ := by ring
        _ ≤ Rs.card * (κ * ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁)) *
            (t * (4 * D₂) + 1) ^ t₂ := by gcongr
        _ = κ * (Rs.card * ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ *
            (t * (4 * D₂) + 1) ^ t₂)) := by ring
        _ ≤ κ * (4 ^ m * hfun blk D ℂ (sl α J) (2 * t + c₁)) := Nat.mul_le_mul_left _ hsum
        _ = _ := by ring
    exact_mod_cast this
  obtain ⟨hl0', hl1, hl2⟩ := lin3_data (N := Rs.card) (a := 4 * D₀) (b := 4 * D₁) (c := 4 * D₂)
    (Finset.card_pos.mpr hRs_ne) (by omega) (by omega) (by omega) t₀ t₁ t₂
  obtain ⟨hdJ, hdegJ⟩ := lower_deg (StrongSix.M2.hdata_spec blk D ℂ hslJ) hl0'
    (C := ((κ * 4 ^ m : ℕ) : ℤ))
    (by exact_mod_cast Nat.mul_pos hκ0 (Nat.pow_pos (n := m) (by norm_num : 0 < 4)))
    hlowJ (fun t => by rw [lin3_eval]; exact Int.natCast_nonneg _)
  rw [hl1] at hdJ hdegJ
  /- 10. The dimensions agree. -/
  have hdimJA : (hdata blk D ℂ (sl α A)).1 = (hdata blk D ℂ (sl α J)).1 ∧
      (hdata blk D ℂ (sl α J)).1 = e := by
    have h1 := hdata_le_of_le blk D ℂ hslAJ hslJ
    rcases h1 with h1 | ⟨h1, -⟩ <;> omega
  /- 11. Wüstholz (A1). -/
  set ℓ := finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hGVs hGVc) with hℓdef
  obtain ⟨c0, hW⟩ := wustholz_cosets_sl hGVs hGVc W Rs hdist D hD α hαRs
  have hAV : A ≤ VOg (Dmix Ls) (Wmix W) (vanish (⋃ a ∈ Rs, gtransl a H0')) T := by
    rw [← hSG]; exact hAVOg
  have hWt := hW A T (T / ℓ) (Nat.mul_div_le T ℓ) hAV
  rw [← hSG] at hWt
  have A1 := deg_le_of_hfun' blk D hslJ hslA hdimJA.1 (Nat.one_le_pow _ _ (Nat.succ_pos _)) hWt
  /- 12. Bézout (A3) and the degree of `sl α I_G` (A4). -/
  have hslA_eq : sl α A = Ideal.ofList (lGs (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) α) ⊔
      Ideal.span F₀ := by
    rw [← slIG_eq_ofList, sl, sl, hA, sup_right_comm]
  have hFD : F₀ ⊆ ((FLE ℂ blk D : Submodule ℂ (MvPolynomial (Var d₀ d₁ m) ℂ)) :
      Set (MvPolynomial (Var d₀ d₁ m) ℂ)) := by
    rintro _ ⟨Q, hQ, v, -, c, rfl⟩
    refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_) (transl_gensR2_mem_FLE hPD r hQ v c)
    have := dblE_dblE_le (Dfun (m := m) D₀ D₁ D₂) b
    refine this.trans (le_of_eq ?_)
    cases b <;> simp [D, Dfun]
  have A3 : (hdata blk D ℂ (sl α A)).2 ≤
      (hdata blk D ℂ (Ideal.ofList (lGs (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) α))).2 := by
    rw [hslA_eq]
    exact StrongSix.M2.bezout blk D hD (height_slIG (g2L Ls) (g3L Ls) h2 α) hFD
      (hslA_eq ▸ hslA)
  have A4 := (hdata_slIG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) h2 α hD).2
  rw [slIG_eq_ofList] at A4
  have A4' : (hdata blk D ℂ (Ideal.ofList (lGs (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) α))).2 ≤
      (((d₀ + d₁ + m).factorial * (4 * D₀) ^ d₀ * (2 * (4 * D₁)) ^ d₁ * (12 * D₂) ^ m :
        ℕ) : ℤ) := by
    refine A4.trans (le_of_eq ?_)
    congr 2
    simp only [D, Dfun, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  /- 13. Counting `F` and the final arithmetic. -/
  refine ⟨O, ObstrData.ofSubgroup_proper hGVs hGVc fun huniv => ?_, fun F hFS hFd => ?_⟩
  · obtain ⟨v₀, hv₀⟩ : V.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro he'
      exact hp.ne_top (by rw [← hpv, he']; exact vanish_empty')
    have hVu : V = Set.univ := Set.eq_univ_of_forall fun g => by
      have hmem : g - v₀ ∈ GV := huniv ▸ Set.mem_univ _
      simpa using hmem v₀ hv₀
    have hpIG : p = IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
      rw [← hpv, hVu, vanish_univ hΔ h2]
    have hL0 : Lr2 (g2L Ls) (g3L Ls) W S P T 0 ≤ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) :=
      hpIG ▸ (Lr2_mono' hS (Nat.zero_le _)).trans hLp
    have hIGne : IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≠ ⊤ :=
      (IG_isPrime (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) h2).ne_top
    have hlt := hdim_Lr2_zero_lt hΔ D hD hPh hPI (ne_top_of_le_ne_top hIGne hL0)
    have hge := hdata_le_of_le blk D ℂ hL0 hIGne
    rw [hdim_IG D hD h2] at hge
    rcases hge with h | ⟨h, -⟩ <;> omega
  have hcardF : F.card ≤ Rs.card := by
    have hmem : ∀ f ∈ F, ∃ a ∈ Rs, f ∈ gtransl a H0' := by
      intro f hf
      have : f ∈ ⋃ a ∈ Rs, gtransl a H0' := by
        rw [← hSG]; exact Set.mem_biUnion (hFS hf) ⟨0, hGVs.zero_mem, zero_add f⟩
      simpa only [Set.mem_iUnion, exists_prop] using this
    choose! φ hφR hφf using hmem
    refine Finset.card_le_card_of_injOn φ (fun f hf => hφR f hf) (fun f hf f' hf' heq => ?_)
    apply hFd f hf f' hf'
    have h1 := mem_gtransl.mp (hφf f hf)
    have h2' := mem_gtransl.mp (hφf f' hf')
    rw [heq] at h1
    have := hH0s.add_mem _ h1 _ (hH0s.neg_mem _ h2')
    rwa [show f - φ f' + -(f' - φ f') = f - f' by abel] at this
  have hℓle : ℓ ≤ n := by
    have h1 : finrank ℂ (Tan d₀ d₁ m) = d₀ + d₁ + m := by
      simp [Tan, Module.finrank_prod]; ring
    have := Submodule.finrank_le W
    omega
  have hele : e ≤ n := by
    have h1 : finrank ℂ (Tan d₀ d₁ m) = d₀ + d₁ + m := by
      simp [Tan, Module.finrank_prod]; ring
    have := Submodule.finrank_le (lieAlg Ls hGVs hGVc)
    omega
  have hκle : κ ≤ d₀ ^ d₀ * d₁ ^ d₁ := by
    have h1 : t₀ ≤ d₀ := by
      have := Submodule.finrank_le (StrongSix.M2.linV (ML Ls hGVs hGVc))
      rwa [Module.finrank_fin_fun] at this
    exact Nat.mul_le_mul (pow_self_mono h1) (pow_self_mono (Nat.sub_le _ _))
  have hTl : T ^ ℓ ≤ ℓ ^ ℓ * (T / ℓ + 1) ^ ℓ := by
    rw [← mul_pow]
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · rw [h0]; simp
    · exact Nat.pow_le_pow_left (Nat.lt_mul_div_succ T hpos).le ℓ
  have h0deg : 0 ≤ (hdata blk D ℂ (sl α J)).2 := (StrongSix.M2.hdata_pos blk D ℂ hslJ).le
  have hA1 := hdegJ (by rw [hdimJA.2, he_sum])
  rw [hl2, hdimJA.2, ← he_sum] at hA1
  have A1' : ((Rs.card * (4 * D₀) ^ t₀ * (4 * D₁) ^ t₁ * (4 * D₂) ^ t₂ * e.factorial : ℕ) : ℤ) ≤
      ((κ * 4 ^ m : ℕ) : ℤ) * (2 ^ e * (hdata blk D ℂ (sl α J)).2) := by
    push_cast at hA1 ⊢
    exact hA1
  rw [hOtan, hOh0, hOU, hOt]
  exact final_arith_ab hℓle hele hκle hTl hcardF h0deg A1' A1 A3 A4'

end LSG.ME
