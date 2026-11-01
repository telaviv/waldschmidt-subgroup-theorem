/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.MainHyp
import LSG.MEB.WustCosetB

/-!
# The multiplicity estimate `MultEstB` from its inputs (A4.5, α; template `LSG.ME.MainAb`)

**`multEstB_of : MEBInputs → MultEstB`.** Roy §8.4.1 on the multi-cone, with relevant radicals for the geometry and
affine slices `sl α` for the Hilbert functions; `n = dim G = d₀ + d₁ + Σ_k g_k` (CR1). The steps are those of
`ME.multEstAb`:

1. chain v2 and the relevant pigeonhole (`exists_flat_rel`); a relevant prime `p` of maximal dimension, `V = Z(p)`,
   `GV = stabG V`, `H⁰ = O.grp` from `MEBInputs`;
2. Roy's ideal `A = IGexp + (τ_v^c Q)`; order `> T` on `SG = ⋃_{s ∈ S} (s + GV)` (`hAVO2`, β's analytic layer);
3. the component step (`component_rel`, `Zs_subset_transl`); 4. cosets of `H⁰`; 5. chart forms (`exists_good_alpha`);
6.–8. `hdim (sl α A) ≤ dim T′` (`radical_sl`, `hdim_vanishP_cosets_le`, `SubgroupData.hdim`);
9. the coset lower bound (`hfun_sum_cosets_P`, `SubgroupData.coset_ge`);
11. Wüstholz (`wust_of_tz` from `SubgroupData.tz`);
12. **B7**: `sl α A = sl α IGexp ⊔ (F₀)` with `sl α IGexp` in block form; StrongSix's `bezout_blocks` with B5
    (`AbBlock.locGen_slB`), and `hdata_slIGexp` (B6) for its dimension and degree;
13. properness, the count of `F`, `final_arith_B`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata hdata_le_of_le)

namespace LSG.MEB

theorem finrank_Tan {m d₀ d₁ : ℕ} (B : Fin m → AbBlock) :
    finrank ℂ (Tan d₀ d₁ B) = d₀ + d₁ + ∑ k, (B k).g := by
  simp [Tan, Module.finrank_prod, Module.finrank_pi_fintype]
  ring

theorem four_smul_DfunB {m : ℕ} (D₀ D₁ D₂ : ℕ) :
    (4 • DfunB D₀ D₁ D₂ : Blk m → ℕ) = DfunB (4 * D₀) (4 * D₁) (4 * D₂) := by
  funext b; cases b <;> simp [DfunB]

/-- **The multiplicity estimate on `G_a^{d₀} × G_m^{d₁} × B₁ × ⋯ × B_m`, from its inputs.** -/
theorem multEstB_of (hin : MEBInputs) : MultEstB := by
  intro d₀ d₁ m B
  obtain ⟨cL, hcL, hdataH⟩ := hin d₀ d₁ m B
  set n := d₀ + d₁ + ∑ k, (B k).g with hn
  refine ⟨CstB n d₀ d₁ cL (cB B d₁),
    fun W S P T D₀ D₁ D₂ hS hPh hPD hPI hT hD₀ hD₁ hD₂ hvan => ?_⟩
  classical
  set D : Blk m → ℕ := DfunB (4 * D₀) (4 * D₁) (4 * D₂) with hDdef
  have hD : ∀ i, 1 ≤ D i := fun i => by
    cases i <;> simp [D, DfunB] <;> omega
  /- 1. The chain and the relevant pigeonhole. -/
  have hlast : Lr2 W S P T n ≤ vanish ({0} : Set (GPt d₀ d₁ B)) :=
    Lr2_le_vanish_zero hPh hvan
  obtain ⟨r, hr, hflat⟩ := exists_flat_rel D hD hPh hS hPI hlast
  have hne : relI d₀ d₁ B (Lr2 W S P T (r + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top (vanish_ne_top (Set.singleton_nonempty 0))
      ((relI_mono (Lr2_mono' hS (by omega : r + 1 ≤ n))).trans (relI_le_vanish_zero hlast))
  obtain ⟨p, hp, hJp, hpdim, hpv⟩ := exists_relevant_prime D hD hne
  set V : Set (GPt d₀ d₁ B) := zeros (p : Set _) with hVdef
  have hV : IsZClosed V := isZClosed_zeros _
  have hVp : (vanish V).IsPrime := hpv ▸ hp
  set GV := stabG V with hGVdef
  have hGVs : IsSubgroupG GV := stabG_isSubgroup hV
  have hGVc : IsZClosed GV := isZClosed_stabG hV
  have hLp : Lr2 W S P T (r + 1) ≤ p := (le_relI _).trans hJp
  /- 2. Roy's ideal `A`. -/
  set F₀ : Set (MvPolynomial (Var d₀ d₁ B) ℂ) := {Q' | ∃ Q ∈ gensR2 W S P T r,
    ∃ v ∈ V, ∃ c, Q' = τ v c Q} with hF₀
  set A : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) := IGexp d₀ d₁ B ⊔ Ideal.span F₀ with hA
  set SG := ⋃ s ∈ S, gtransl s GV with hSGdef
  have hAVO : A ≤ ordIdealB W T SG := hAVO2 W S hPh T r hLp GV fun u hu v hv => hu v hv
  have hAJ : A ≤ vanish SG := hAVO.trans (ordIdealB_le_vanish T SG)
  /- 3. Roy's component step. -/
  have hdimV : (hdata blk D ℂ (vanish V)).1 =
      (hdata blk D ℂ (relI d₀ d₁ B (Lr2 W S P T r))).1 := by
    rw [hpv, hpdim, hflat]
  obtain ⟨R, hR⟩ := component_rel D hD hV hVp hdimV
  /- 4. Cosets of `H⁰`. -/
  obtain ⟨SD⟩ := hdataH GV hGVs hGVc
  set O := SD.O with hO
  set H0' := O.grp with hH0'
  have hH0s : IsSubgroupG H0' := O.grp_sub
  have hH0c : IsZClosed H0' := O.grp_closed
  have hH0p : (vanish H0').IsPrime := vanish_grp_isPrime O
  obtain ⟨Rc, hRcGV, hGVcov⟩ := SD.cosets
  have hcov := biUnion_gtransl_cover hGVs SD.grp_le Rc hRcGV hGVcov
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
  have h0SG : (0 : GPt d₀ d₁ B) ∈ SG :=
    Set.mem_biUnion hS ⟨0, hGVs.zero_mem, add_zero 0⟩
  have hRs_ne : Rs.Nonempty := by
    have : (0 : GPt d₀ d₁ B) ∈ ⋃ a ∈ Rs, gtransl a H0' := hSG ▸ h0SG
    simp only [Set.mem_iUnion] at this
    obtain ⟨a, ha, -⟩ := this
    exact ⟨a, ha⟩
  have hPSG : vanishP Finset.univ α SG ≠ ⊤ := by
    obtain ⟨a, ha⟩ := hRs_ne
    obtain ⟨g₀, hg₀, hs₀⟩ := point_of_lsl_notMem (vanish_gtransl_isPrime hH0p a) (hαRs a ha)
    have hg₀SG : g₀ ∈ SG := by
      rw [hSG]; exact Set.mem_biUnion ha hg₀
    intro htop
    have h1 : (1 : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ vanishP Finset.univ α SG :=
      htop ▸ Submodule.mem_top
    have := mem_vanishP.mp h1 g₀ hg₀SG (fun k _ => hs₀ k) 1
    simp at this
  set J := vanish SG with hJdef
  have hslJP : sl α J ≤ vanishP Finset.univ α SG := sl_vanish_le_vanishP α SG
  have hslAJ : sl α A ≤ sl α J := sup_le_sup_right hAJ _
  have hslJ : sl α J ≠ ⊤ := ne_top_of_le_ne_top hPSG hslJP
  have hslA : sl α A ≠ ⊤ := ne_top_of_le_ne_top hslJ hslAJ
  /- 7. The obstruction and its dimensions. -/
  set e := finrank ℂ O.tan with he
  set t₀ := finrank ℂ O.h0 with ht₀
  set t₁ := d₁ - finrank ℚ O.U with ht₁
  set t₂ := finrank ℂ O.t with ht₂
  have he_sum : e = t₀ + t₁ + t₂ := by
    have h1 := finrank_tanOf (B := B) O.h0 O.U O.t
    have h2 : finrank ℚ O.U ≤ d₁ := by
      have := Submodule.finrank_le O.U
      rwa [Module.finrank_fin_fun] at this
    change finrank ℂ (tanOf O.h0 O.U O.t) = _
    omega
  /- 8. `hdim (sl α A) ≤ e`. -/
  have hdimA_le : (hdata blk D ℂ (sl α A)).1 ≤ e := by
    have hrad := radical_sl α (le_sup_left : IGexp d₀ d₁ B ≤ A)
    have hZs : Zs (d₀ := d₀) (d₁ := d₁) α A ⊆ ⋃ b ∈ R', gtransl b H0' := by
      intro g hg
      rw [← hRcov]
      exact hR (Zs_subset_transl α W S hPh T r V hg)
    have hPle : vanishP Finset.univ α (⋃ b ∈ R', gtransl b H0') ≤ (sl α A).radical := by
      rw [hrad]
      intro Q hQ
      refine (StrongSix.M2.mem_vanish' _).mpr fun g hg => ?_
      have := mem_vanishP.mp hQ g (hZs hg) (fun k _ => hg.1 k) 1
      rwa [coords_nscal_univ hg.1] at this
    have hradne : (sl α A).radical ≠ ⊤ := fun h => hslA (Ideal.radical_eq_top.mp h)
    have h1 := hdata_le_of_le blk D ℂ hPle hradne
    rw [StrongSix.M2.hdim_radical blk D hD hslA] at h1
    have h2'' := hdim_vanishP_cosets_le D hD hH0c hH0p R' hαR'
      (ne_top_of_le_ne_top hradne hPle)
    rw [SD.hdim D hD, ← hO] at h2''
    rcases h1 with h1 | ⟨h1, -⟩ <;> omega
  /- 9. The lower bound through the cosets. -/
  obtain ⟨c₁, hc₁⟩ := hfun_sum_cosets_P D hD α hH0c hH0p Rs hαRs
    fun a ha b hb hab => not_gtransl_subset hH0s (hdist a ha b hb hab)
  have hcos : ∀ a ∈ Rs, ∀ t,
      (t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ * (t * (4 * D₂) + 1) ^ t₂ ≤
        cL * hfun blk D ℂ (vanishP Finset.univ α (gtransl a H0')) (2 * t) :=
    fun a ha t => SD.coset_ge α a (hαRs a ha) (4 * D₀) (4 * D₁) (4 * D₂) t
  set κ := t₀ ^ t₀ * t₁ ^ t₁ with hκ
  have hκ0 : 0 < κ := by
    have hpow : ∀ x : ℕ, 0 < x ^ x := fun x => by
      rcases Nat.eq_zero_or_pos x with h | h
      · rw [h]; simp
      · exact Nat.pow_pos h
    exact Nat.mul_pos (hpow t₀) (hpow t₁)
  have hlowJ : ∀ t : ℕ, (lin3 Rs.card (4 * D₀) (4 * D₁) (4 * D₂) t₀ t₁ t₂).eval (t : ℤ) ≤
      ((κ * cL : ℕ) : ℤ) * (hfun blk D ℂ (sl α J) (2 * t + c₁) : ℤ) := by
    intro t
    rw [lin3_eval]
    have hsum : Rs.card * ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ *
        (t * (4 * D₂) + 1) ^ t₂) ≤ cL * hfun blk D ℂ (sl α J) (2 * t + c₁) := by
      calc Rs.card * ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ *
            (t * (4 * D₂) + 1) ^ t₂)
          = ∑ _a ∈ Rs, ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ *
            (t * (4 * D₂) + 1) ^ t₂) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ a ∈ Rs, cL * hfun blk D ℂ (vanishP Finset.univ α (gtransl a H0')) (2 * t) :=
            Finset.sum_le_sum fun a ha => hcos a ha t
        _ = cL * ∑ a ∈ Rs, hfun blk D ℂ (vanishP Finset.univ α (gtransl a H0')) (2 * t) := by
            rw [Finset.mul_sum]
        _ ≤ cL * hfun blk D ℂ (vanishP Finset.univ α (⋃ a ∈ Rs, gtransl a H0'))
              (2 * t + c₁) := Nat.mul_le_mul_left _ (hc₁ (2 * t))
        _ ≤ cL * hfun blk D ℂ (sl α J) (2 * t + c₁) := by
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
        κ * cL * hfun blk D ℂ (sl α J) (2 * t + c₁) := by
      calc Rs.card * (4 * D₀ * t + 1) ^ t₀ * (4 * D₁ * t + 1) ^ t₁ * (4 * D₂ * t + 1) ^ t₂
          = Rs.card * ((4 * D₀ * t + 1) ^ t₀ * (4 * D₁ * t + 1) ^ t₁) *
            (t * (4 * D₂) + 1) ^ t₂ := by ring
        _ ≤ Rs.card * (κ * ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁)) *
            (t * (4 * D₂) + 1) ^ t₂ := by gcongr
        _ = κ * (Rs.card * ((t * (4 * D₀) / t₀ + 1) ^ t₀ * (t * (4 * D₁) / t₁ + 1) ^ t₁ *
            (t * (4 * D₂) + 1) ^ t₂)) := by ring
        _ ≤ κ * (cL * hfun blk D ℂ (sl α J) (2 * t + c₁)) := Nat.mul_le_mul_left _ hsum
        _ = _ := by ring
    exact_mod_cast this
  obtain ⟨hl0', hl1, hl2⟩ := lin3_data (N := Rs.card) (a := 4 * D₀) (b := 4 * D₁) (c := 4 * D₂)
    (Finset.card_pos.mpr hRs_ne) (by omega) (by omega) (by omega) t₀ t₁ t₂
  obtain ⟨hdJ, hdegJ⟩ := lower_deg (StrongSix.M2.hdata_spec blk D ℂ hslJ) hl0'
    (C := ((κ * cL : ℕ) : ℤ)) (by exact_mod_cast Nat.mul_pos hκ0 hcL)
    hlowJ (fun t => by rw [lin3_eval]; exact Int.natCast_nonneg _)
  rw [hl1] at hdJ hdegJ
  /- 10. The dimensions agree. -/
  have hdimJA : (hdata blk D ℂ (sl α A)).1 = (hdata blk D ℂ (sl α J)).1 ∧
      (hdata blk D ℂ (sl α J)).1 = e := by
    have h1 := hdata_le_of_le blk D ℂ hslAJ hslJ
    rcases h1 with h1 | ⟨h1, -⟩ <;> omega
  /- 11. Wüstholz. -/
  set ℓ := finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan) with hℓdef
  obtain ⟨c0, hW⟩ := wust_of_tz SD.tz W Rs hdist D hD α hαRs
  have hAH : A ≤ homOrd W T SG := by
    refine sup_le (IGexp_le_IGsem.trans (IGsem_le_homOrd W T SG)) (Ideal.span_le.mpr ?_)
    rintro _ ⟨Q, hQ, v, hv, c, rfl⟩
    exact mem_homOrd_of (isHomB_transl v c (isHomB_gensR2 hPh Q hQ))
      (hAVO (Ideal.mem_sup_right (Ideal.subset_span ⟨Q, hQ, v, hv, c, rfl⟩)))
  have hAV : A ≤ homOrd W T (⋃ a ∈ Rs, gtransl a H0') := by rw [← hSG]; exact hAH
  have hWt := hW A T (T / ℓ) (Nat.mul_div_le T ℓ) hAV
  rw [← hSG] at hWt
  have A1 := deg_le_of_hfun' blk D hslJ hslA hdimJA.1 (Nat.one_le_pow _ _ (Nat.succ_pos _)) hWt
  /- 12. Bézout for the block ideal (B7) and the degree of `sl α IGexp`. -/
  have hslA_eq : sl α A = sl α (IGexp d₀ d₁ B) ⊔ Ideal.span F₀ := by
    rw [sl, sl, hA, sup_right_comm]
  have hslG : sl α (IGexp d₀ d₁ B) ≠ ⊤ :=
    ne_top_of_le_ne_top hslA (sup_le_sup_right (le_sup_left : IGexp d₀ d₁ B ≤ A) _)
  have hFD : F₀ ⊆ ((FLE ℂ blk D : Submodule ℂ (MvPolynomial (Var d₀ d₁ B) ℂ)) :
      Set (MvPolynomial (Var d₀ d₁ B) ℂ)) := by
    rintro _ ⟨Q, hQ, v, -, c, rfl⟩
    refine StrongSix.M2.FLE_mono ℂ blk ?_ (transl_gensR2_mem_FLE hPD r hQ v c)
    rw [hDdef, ← four_smul_DfunB]
    exact dblB_dblB_le _
  obtain ⟨hGdim, hGdeg⟩ := hdata_slIGexp (d₀ := d₀) (d₁ := d₁) α hD hslG
  have hsumN : ∑ k, ((B k).N - (B k).g) + ∑ k, (B k).g = ∑ k, (B k).N := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (B k).g_lt_N.le
  have hdimB : (hdata blk D ℂ (Ideal.ofList (lYZ d₀ d₁ B) ⊔
      ⨆ k ∈ (Finset.univ : Finset (Fin m)),
        ((B k).slB (α k)).map (rename (Var.e (d₀ := d₀) (d₁ := d₁) k)))).1 +
      ((lYZ d₀ d₁ B).length + ∑ k ∈ Finset.univ, ((B k).N - (B k).g)) ≤
        Fintype.card (Var d₀ d₁ B) := by
    rw [← slIGexp_eq_blocks, hGdim, lYZ_length, card_Var]
    omega
  have A3 : (hdata blk D ℂ (sl α A)).2 ≤ (hdata blk D ℂ (sl α (IGexp d₀ d₁ B))).2 := by
    rw [hslA_eq, slIGexp_eq_blocks]
    refine StrongSix.M2.bezout_blocks blk D hD Finset.univ
      (fun k => (Var.e (d₀ := d₀) (d₁ := d₁) (B := B) k)) (J := fun k => (B k).slB (α k))
      (r := fun k => (B k).N - (B k).g) (fun k _ => (B k).locGen_slB (α k)) (lYZ d₀ d₁ B)
      hdimB hFD ?_
    rw [← slIGexp_eq_blocks, ← hslA_eq]
    exact hslA
  have A4 : (hdata blk D ℂ (sl α (IGexp d₀ d₁ B))).2 ≤
      ((n.factorial * cB B d₁ * (4 * D₀) ^ d₀ * (4 * D₁) ^ d₁ * (4 * D₂) ^ (∑ k, (B k).g) :
        ℕ) : ℤ) := by
    refine hGdeg.trans (le_of_eq ?_)
    congr 1
    simp only [D, DfunB, Finset.prod_pow_eq_pow_sum]
    rfl
  /- 13. Properness, counting `F` and the final arithmetic. -/
  refine ⟨O, fun htop => ?_, fun F hFS hFd => ?_⟩
  · have huniv : GV = Set.univ := Set.eq_univ_of_forall fun g => by
      obtain ⟨u, rfl⟩ := expG_surjective (d₀ := d₀) (d₁ := d₁) (B := B) g
      exact SD.grp_le (O.expG_mem (htop ▸ Submodule.mem_top))
    obtain ⟨v₀, hv₀⟩ : V.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro he'
      exact hp.ne_top (by rw [← hpv, he']; exact vanish_empty)
    have hVu : V = Set.univ := Set.eq_univ_of_forall fun g => by
      have hmem : g - v₀ ∈ GV := huniv ▸ Set.mem_univ _
      simpa using hmem v₀ hv₀
    have hpIG : p = IGsem d₀ d₁ B := by rw [← hpv, hVu]; rfl
    have hL0 : Lr2 W S P T 0 ≤ IGsem d₀ d₁ B :=
      hpIG ▸ (Lr2_mono' hS (Nat.zero_le _)).trans hLp
    have hIGne : IGsem d₀ d₁ B ≠ ⊤ := IGsem_ne_top
    have hlt := hdim_Lr2_zero_lt_IGsem D hD hPh hPI (ne_top_of_le_ne_top hIGne hL0)
    have hge := hdata_le_of_le blk D ℂ hL0 hIGne
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
    have := Submodule.finrank_le W
    rw [finrank_Tan] at this
    omega
  have hele : e ≤ n := by
    have := Submodule.finrank_le O.tan
    rw [finrank_Tan] at this
    omega
  have hκle : κ ≤ d₀ ^ d₀ * d₁ ^ d₁ := by
    have h1 : t₀ ≤ d₀ := by
      have := Submodule.finrank_le O.h0
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
      ((κ * cL : ℕ) : ℤ) * (2 ^ e * (hdata blk D ℂ (sl α J)).2) := by
    push_cast at hA1 ⊢
    exact hA1
  exact final_arith_B hn hℓle hele hκle hTl hcardF h0deg A1' A1 A3 A4

end LSG.MEB
