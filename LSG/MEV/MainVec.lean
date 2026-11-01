import Mathlib
import LSG.MEV.MainVecAux
import StrongSix.M2.Bezout

/-!
# The multiplicity estimate on `G̃ = G_a^{d₀} × G_m^{d₁} × E₁^♮ × ⋯ × E_m^♮` (STAGE5_MEV §10)

**`multEstG`**: Roy §8.4.1 on the `E^♮` multi-cone, mirroring `LSG.ME.multEstAb`, with an extra
subspace `Kv ⊆ Lie G̃` of symmetries of the formal-order hypothesis (used for the push-out):

1. chain v2 and the relevant pigeonhole (`exists_flat_rel`); a relevant prime `p` of maximal
   dimension (`exists_relevant_prime`), `V = Z(p)`, `GV = stabG V`, `H⁰ = GV⁰`; `Kv ⊆ lieAlg GV`
   (`le_lieAlg_stabG`, `zeros_Lr2_add`);
2. Roy's ideal `A`, `A ≤ VOg DmixV (I(SG)) T` (`hAVO2`, `isHomV_phOp`, `isHomV_transl`,
   `mem_VOg_mixV`);
3. the component step (`Zs_subset_translV`, `component_rel`);
4. chart forms `ℓ_k = V_k + α_k W_k` good for all cosets (`exists_good_alpha`);
5. dimensions: `hdim (sl α A) ≤ dim T′` (`radical_sl`, `hdim_vanishP_cosets_le`, `hdim_H0`) and the
   coset lower bound (`hfun_H0_geV`, `hfun_cosets_ge_c`, `lower_deg3`), so both are `dim T′`;
6. degrees: sliced Wüstholz `wustholz_cosets_slV`, Bézout for
   `sl α A = sl α I_G̃ ⊔ (generators)` (`height_slIGV`, StrongSix `bezout`), `hdata_slIGV`;
   `final_arith_v`.

The exponents are W88's projection exponents of `T′ = lieAlg GV` (`ex0`, `ex1`, `ex2`), the right
side is `D₀^{d₀} D₁^{d₁} D₂^{2m}` (all `d₀` additive coordinates in degree `D₀`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk Dfun VOg)
open LSG.W88.Vec (vecIncl torIncl)
open StrongSix.M2 (FLE hfun hdata hdata_le_of_le)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ}

/-- `t₀ = dim pr_{G_a}(T′)` (`= dim pr_{G_a}(T′ ∩ vector group)`, `map_prA_tan`). -/
def ex0 (T : Submodule ℂ (TanG d₀ d₁ m)) : ℕ :=
  finrank ℂ ((T.comap vecIncl).map (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin m → ℂ)))

/-- `t₁ = dim (T′ ∩ torus)`. -/
def ex1 (T : Submodule ℂ (TanG d₀ d₁ m)) : ℕ :=
  finrank ℂ (T.comap (torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] TanG d₀ d₁ m))

/-- `t₂ = dim (T′ ∩ ker pr_{G_a} ∩ ker pr_{G_m})`. -/
def ex2 (T : Submodule ℂ (TanG d₀ d₁ m)) : ℕ :=
  finrank ℂ ↥(T ⊓ (LinearMap.ker (prA : TanG d₀ d₁ m →ₗ[ℂ] (Fin d₀ → ℂ)) ⊓ LinearMap.ker prB))

theorem finrank_TanG : finrank ℂ (TanG d₀ d₁ m) = d₀ + d₁ + 2 * m := by
  show finrank ℂ ((Fin d₀ → ℂ) × (Fin d₁ → ℂ) × (Fin m → ℂ) × (Fin m → ℂ)) = _
  simp [Module.finrank_prod]; ring

theorem finrank_LieV : finrank ℂ (LieV ℂ d₀ d₁ m) = d₀ + d₁ + 2 * m := by
  simp [LieV, Module.finrank_prod, Module.finrank_pi_fintype]; ring

/-- **The multiplicity estimate on `G̃`** (with a subspace `Kv` of symmetries). -/
theorem multEstG (Ls : Fin m → PeriodPair) (W : Submodule ℂ (LieV ℂ d₀ d₁ m))
    (S : Finset (GPtV d₀ d₁ Ls)) (P : MvPolynomial (Var d₀ d₁ m) ℂ) (T D₀ D₁ D₂ : ℕ)
    (Kv : Submodule ℂ (TanG d₀ d₁ m)) (hS : (0 : GPtV d₀ d₁ Ls) ∈ S)
    (hPh : IsHomV P (fun _ => D₂)) (hPD : P ∈ FLE ℂ blk (Dfun D₀ D₁ D₂))
    (hPI : P ∉ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) (_hT : 1 ≤ T) (hD₀ : 1 ≤ D₀)
    (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hvan : ∀ σ ∈ sig S (d₀ + d₁ + 2 * m), OrdGt Ls W P ((d₀ + d₁ + 2 * m) * T) σ)
    (hK : ∀ v ∈ Kv, ∀ y n, OrdGt Ls W P n y → OrdGt Ls W P n (y + expGV Ls v)) :
    ∃ (H : Set (GPtV d₀ d₁ Ls)) (hH : IsSubgroupG H), IsZClosed H ∧ Kv ≤ lieAlg Ls hH ∧
      lieAlg Ls hH ≠ ⊤ ∧
      ∀ F : Finset (GPtV d₀ d₁ Ls), F ⊆ S → (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ H0 Ls hH → g = g') →
        T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) * F.card * D₀ ^ ex0 (lieAlg Ls hH) *
            D₁ ^ ex1 (lieAlg Ls hH) * D₂ ^ ex2 (lieAlg Ls hH) ≤
          CstV d₀ d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m) := by
  classical
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  set n := d₀ + d₁ + 2 * m with hn
  set D : Blk m → ℕ := Dfun (9 * D₀) (9 * D₁) (9 * D₂) with hDdef
  have hD : ∀ i, 1 ≤ D i := fun i => by
    cases i <;> simp [D, Dfun] <;> omega
  /- 1. The chain and the relevant pigeonhole. -/
  have hlast : Lr2 Ls W S P T n ≤ vanish ({0} : Set (GPtV d₀ d₁ Ls)) :=
    Lr2_le_vanish_zero hPh hvan
  obtain ⟨r, hr, hflat⟩ := exists_flat_rel D hD hPh hS hPI hlast
  have hne : relI Ls (Lr2 Ls W S P T (r + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top (vanish_ne_top (Set.singleton_nonempty 0))
      ((relI_mono (Lr2_mono' hS (by omega : r + 1 ≤ n))).trans (relI_le_vanish_zero hlast))
  obtain ⟨p, hp, hJp, hpdim, hpv⟩ := exists_relevant_prime D hD hne
  set V : Set (GPtV d₀ d₁ Ls) := zeros (p : Set _) with hVdef
  have hV : IsZClosed V := isZClosed_zeros _
  have hVp : (vanish V).IsPrime := hpv ▸ hp
  set GV := stabG V with hGVdef
  have hGVs : IsSubgroupG GV := stabG_isSubgroup hV
  have hGVc : IsZClosed GV := isZClosed_stabG hV
  have hLp : Lr2 Ls W S P T (r + 1) ≤ p := (le_relI _).trans hJp
  /- 1′. The symmetries. -/
  have hKs : Kv ≤ lieAlg Ls hGVs := by
    refine le_lieAlg_stabG D hD (L := Lr2 Ls W S P T (r + 1)) hV hVp (by rw [hpv, hpdim])
      (fun g hg Q hQ lam => hg Q (hLp hQ) lam) Kv fun v hv h hh => ?_
    exact zeros_Lr2_add hPh (fun y n' hy => hK v hv y n' hy) (r + 1) hh
  /- 2. Roy's ideal `A`. -/
  set F₀ : Set (MvPolynomial (Var d₀ d₁ m) ℂ) := {Q' | ∃ Q ∈ gensR2 Ls W S P T r,
    ∃ v ∈ V, ∃ c, Q' = τ Ls v c Q} with hF₀
  set A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
    IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔ Ideal.span F₀ with hA
  set SG := ⋃ s ∈ S, gtransl s GV with hSGdef
  have hAVO : A ≤ ordIdeal Ls W T SG := hAVO2 W S hPh T r hLp GV fun u hu v hv => hu v hv
  have hAVOg : A ≤ VOg (DmixV Ls) (WmixV W) (vanish SG) T := by
    refine sup_le (IG_le_VOg_mixV W T SG) (Ideal.span_le.mpr ?_)
    rintro _ ⟨Q, hQ, v, hv, c, rfl⟩
    obtain ⟨σ, hσ, w, hw, κ, hκ, c₁, c₂, rfl⟩ := hQ
    have hx := isHomV_transl (isHomV_phOp σ w c₁ c₂ κ hPh) v c
    exact mem_VOg_mixV W hx fun g hg => hAVO (Ideal.mem_sup_right (Ideal.subset_span
      ⟨_, ⟨σ, hσ, w, hw, κ, hκ, c₁, c₂, rfl⟩, v, hv, c, rfl⟩)) g hg
  have hAJ : A ≤ vanish SG :=
    hAVOg.trans (LSG.ME.VOg_le (Dv := DmixV Ls) (W := WmixV W) (J := vanish SG) T)
  /- 3. Roy's component step. -/
  have hdimV : (hdata blk D ℂ (vanish V)).1 =
      (hdata blk D ℂ (relI Ls (Lr2 Ls W S P T r))).1 := by
    rw [hpv, hpdim, hflat]
  obtain ⟨R, hR⟩ := component_rel D hD hV hVp hdimV
  /- 4. Cosets of `H⁰`. -/
  set H0' := H0 Ls hGVs with hH0'
  have hH0s : IsSubgroupG H0' := H0_isSubgroup hGVs
  have hH0c : IsZClosed H0' := isZClosed_H0 hGVs
  have hH0p : (vanish H0').IsPrime := vanish_H0_isPrime hGVs
  obtain ⟨Rc, hRcGV, hGVcov⟩ := finite_cosets_H0 hGVs hGVc
  have hcov := biUnion_gtransl_coverV hGVs (H0_subset hGVs hGVc) Rc hRcGV hGVcov
  obtain ⟨Rs, -, hRsU, hdist⟩ := exists_reps_GV hH0s ((S ×ˢ Rc).image fun p => p.2 + p.1)
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
  have h0SG : (0 : GPtV d₀ d₁ Ls) ∈ SG :=
    Set.mem_biUnion hS ⟨0, hGVs.zero_mem, add_zero 0⟩
  have hl0 : ∀ k, lval α (0 : GPtV d₀ d₁ Ls) k ≠ 0 := fun k => by
    have := repV_one_two (Ls k) (0 : EVL (Ls k))
    simp [lval, this, rep, LSG.Elliptic.O]
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
  /- 7. The exponents. -/
  set T' := lieAlg Ls hGVs with hT'
  set e := finrank ℂ T' with he
  set t₀ := ex0 T' with ht₀
  set t₁ := ex1 T' with ht₁
  set t₂ := ex2 T' with ht₂
  have he_sum : e = t₀ + t₁ + t₂ := (t0_add_t1_add_t2 hGVs hGVc).symm
  /- 8. `hdim (sl α A) ≤ e`. -/
  have hdimA_le : (hdata blk D ℂ (sl α A)).1 ≤ e := by
    have hrad := radical_sl α (le_sup_left : IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤ A)
    have hZs : Zs (Ls := Ls) α A ⊆ ⋃ b ∈ R', gtransl b H0' := by
      intro g hg
      rw [← hRcov]
      exact hR (Zs_subset_translV α W S hPh T r V hg)
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
    rw [hdim_H0 hGVs hGVc D hD, ← hT', ← he] at h2''
    rcases h1 with h1 | ⟨h1, -⟩ <;> omega
  /- 9. The lower bound through the cosets. -/
  have hRs_ne : Rs.Nonempty := by
    have : (0 : GPtV d₀ d₁ Ls) ∈ ⋃ a ∈ Rs, gtransl a H0' := hSG ▸ h0SG
    simp only [Set.mem_iUnion] at this
    obtain ⟨a, ha, -⟩ := this
    exact ⟨a, ha⟩
  set L : ℕ → ℕ := fun t => (t * (9 * D₀) / t₀ + 1) ^ t₀ * (t * (9 * D₁) / t₁ + 1) ^ t₁ *
    (t * (9 * D₂) / 2 + 1) ^ t₂ with hLdef
  have hDe : ∀ k : Fin m, D (.e k) = 9 * D₂ := fun k => rfl
  have hL : ∀ t, L t * ∏ k : Fin m, (t * D (.e k) + 1) ≤ 2 ^ m * hfun blk D ℂ (vanish H0') t := by
    intro t
    have hge := hfun_H0_geV hGVs hGVc (9 * D₀) (9 * D₁) (9 * D₂) t
    have hx : t * (9 * D₂) + 1 ≤ 2 * (t * (9 * D₂) / 2 + 1) := by
      have : ∀ x : ℕ, x + 1 ≤ 2 * (x / 2 + 1) := fun x => by omega
      exact this _
    have hprod : ∏ k : Fin m, (t * D (.e k) + 1) ≤ 2 ^ m * (t * (9 * D₂) / 2 + 1) ^ m := by
      simp only [hDe, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← mul_pow]
      exact Nat.pow_le_pow_left hx m
    calc L t * ∏ k : Fin m, (t * D (.e k) + 1)
        ≤ L t * (2 ^ m * (t * (9 * D₂) / 2 + 1) ^ m) := Nat.mul_le_mul_left _ hprod
      _ = 2 ^ m * ((t * (9 * D₀) / t₀ + 1) ^ t₀ * (t * (9 * D₁) / t₁ + 1) ^ t₁ *
            (t * (9 * D₂) / 2 + 1) ^ (t₂ + m)) := by rw [hLdef, pow_add]; ring
      _ ≤ 2 ^ m * hfun blk D ℂ (vanish H0') t := Nat.mul_le_mul_left _ hge
  obtain ⟨c₁, hc₁⟩ := hfun_cosets_ge_c D hD α hH0c hH0p Rs hαRs
    (fun a ha b hb hab => not_gtransl_subset_of_sub_notMem hH0s (hdist a ha b hb hab)) L (2 ^ m) hL
  set κ := t₀ ^ t₀ * t₁ ^ t₁ with hκ
  have hpow : ∀ x : ℕ, 0 < x ^ x := fun x => by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h]; simp
    · exact Nat.pow_pos h
  have hκ0 : 0 < κ := Nat.mul_pos (hpow t₀) (hpow t₁)
  have hlowJ : ∀ t : ℕ, (LSG.ME.lin3 Rs.card (9 * D₀) (9 * D₁) (9 * D₂) t₀ t₁ t₂).eval (t : ℤ) ≤
      ((κ * 2 ^ t₂ * 48 ^ m : ℕ) : ℤ) * (hfun blk D ℂ (sl α J) (3 * t + c₁) : ℤ) := by
    intro t
    rw [LSG.ME.lin3_eval]
    have hsum : Rs.card * L t ≤ 48 ^ m * hfun blk D ℂ (sl α J) (3 * t + c₁) := by
      calc Rs.card * L t ≤ 2 ^ m * 24 ^ m *
            hfun blk D ℂ (vanishP Finset.univ α (⋃ a ∈ Rs, gtransl a H0')) (3 * t + c₁) := hc₁ t
        _ ≤ 2 ^ m * 24 ^ m * hfun blk D ℂ (sl α J) (3 * t + c₁) := by
            refine Nat.mul_le_mul_left _ (StrongSix.M2.hfun_mono blk D ℂ ?_ _)
            rw [← hSG]; exact hslJP
        _ = 48 ^ m * hfun blk D ℂ (sl α J) (3 * t + c₁) := by
            rw [← mul_pow]; norm_num
    have hpb : (9 * D₀ * t + 1) ^ t₀ * (9 * D₁ * t + 1) ^ t₁ * (9 * D₂ * t + 1) ^ t₂ ≤
        κ * 2 ^ t₂ * L t := by
      have e1 := StrongSix.M2.pow_div_bound (t * (9 * D₀)) t₀
      have e2 := StrongSix.M2.pow_div_bound (t * (9 * D₁)) t₁
      rw [mul_pow] at e1 e2
      have e3 : (t * (9 * D₂) + 1) ^ t₂ ≤ 2 ^ t₂ * (t * (9 * D₂) / 2 + 1) ^ t₂ := by
        rw [← mul_pow]
        have : ∀ x : ℕ, x + 1 ≤ 2 * (x / 2 + 1) := fun x => by omega
        exact Nat.pow_le_pow_left (this _) t₂
      calc (9 * D₀ * t + 1) ^ t₀ * (9 * D₁ * t + 1) ^ t₁ * (9 * D₂ * t + 1) ^ t₂
          = (t * (9 * D₀) + 1) ^ t₀ * (t * (9 * D₁) + 1) ^ t₁ * (t * (9 * D₂) + 1) ^ t₂ := by
            ring
        _ ≤ (t₀ ^ t₀ * (t * (9 * D₀) / t₀ + 1) ^ t₀) * (t₁ ^ t₁ * (t * (9 * D₁) / t₁ + 1) ^ t₁) *
            (2 ^ t₂ * (t * (9 * D₂) / 2 + 1) ^ t₂) := Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
        _ = _ := by rw [hLdef]; ring
    have : Rs.card * (9 * D₀ * t + 1) ^ t₀ * (9 * D₁ * t + 1) ^ t₁ * (9 * D₂ * t + 1) ^ t₂ ≤
        κ * 2 ^ t₂ * 48 ^ m * hfun blk D ℂ (sl α J) (3 * t + c₁) := by
      calc Rs.card * (9 * D₀ * t + 1) ^ t₀ * (9 * D₁ * t + 1) ^ t₁ * (9 * D₂ * t + 1) ^ t₂
          = Rs.card * ((9 * D₀ * t + 1) ^ t₀ * (9 * D₁ * t + 1) ^ t₁ *
            (9 * D₂ * t + 1) ^ t₂) := by ring
        _ ≤ Rs.card * (κ * 2 ^ t₂ * L t) := Nat.mul_le_mul_left _ hpb
        _ = κ * 2 ^ t₂ * (Rs.card * L t) := by ring
        _ ≤ κ * 2 ^ t₂ * (48 ^ m * hfun blk D ℂ (sl α J) (3 * t + c₁)) :=
            Nat.mul_le_mul_left _ hsum
        _ = _ := by ring
    exact_mod_cast this
  obtain ⟨hl0', hl1, hl2⟩ := LSG.ME.lin3_data (N := Rs.card) (a := 9 * D₀) (b := 9 * D₁)
    (c := 9 * D₂) (Finset.card_pos.mpr hRs_ne) (by omega) (by omega) (by omega) t₀ t₁ t₂
  have hCpos : (0 : ℤ) < ((κ * 2 ^ t₂ * 48 ^ m : ℕ) : ℤ) := by
    have : 0 < κ * 2 ^ t₂ * 48 ^ m :=
      Nat.mul_pos (Nat.mul_pos hκ0 (pow_pos two_pos _)) (pow_pos (by norm_num) _)
    exact_mod_cast this
  obtain ⟨hdJ, hdegJ⟩ := lower_deg3 (StrongSix.M2.hdata_spec blk D ℂ hslJ) hl0'
    (C := ((κ * 2 ^ t₂ * 48 ^ m : ℕ) : ℤ)) hCpos hlowJ (fun t => by rw [LSG.ME.lin3_eval]; exact Int.natCast_nonneg _)
  rw [hl1] at hdJ hdegJ
  /- 10. The dimensions agree. -/
  have hdimJA : (hdata blk D ℂ (sl α A)).1 = (hdata blk D ℂ (sl α J)).1 ∧
      (hdata blk D ℂ (sl α J)).1 = e := by
    have h1 := hdata_le_of_le blk D ℂ hslAJ hslJ
    rcases h1 with h1 | ⟨h1, -⟩ <;> omega
  /- 11. Wüstholz. -/
  set ℓ := finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hGVs) with hℓdef
  obtain ⟨c0, hW⟩ := wustholz_cosets_slV hGVs hGVc W Rs hdist D hD α hαRs
  have hAV : A ≤ VOg (DmixV Ls) (WmixV W) (vanish (⋃ a ∈ Rs, gtransl a H0')) T := by
    rw [← hSG]; exact hAVOg
  have hWt := hW A T (T / ℓ) (Nat.mul_div_le T ℓ) hAV
  rw [← hSG] at hWt
  have A1 := LSG.ME.deg_le_of_hfun' blk D hslJ hslA hdimJA.1
    (Nat.one_le_pow _ _ (Nat.succ_pos _)) hWt
  /- 12. Bézout and the degree of `sl α I_G̃`. -/
  have hslA_eq : sl α A = Ideal.ofList (lGsV (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) α) ⊔
      Ideal.span F₀ := by
    rw [← slIGV_eq_ofList, sl, sl, hA, sup_right_comm]
  have hFD : F₀ ⊆ ((FLE ℂ blk D : Submodule ℂ (MvPolynomial (Var d₀ d₁ m) ℂ)) :
      Set (MvPolynomial (Var d₀ d₁ m) ℂ)) := by
    rintro _ ⟨Q, hQ, v, -, c, rfl⟩
    refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_) (transl_gensR2_mem_FLE hPD r hQ v c)
    cases b <;> simp [D, Dfun]
  have A3 : (hdata blk D ℂ (sl α A)).2 ≤
      (hdata blk D ℂ (Ideal.ofList (lGsV (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) α))).2 := by
    rw [hslA_eq]
    exact StrongSix.M2.bezout blk D hD (height_slIGV (g2L Ls) (g3L Ls) h2 α) hFD
      (hslA_eq ▸ hslA)
  have A4 := (hdata_slIGV (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) h2 α hD).2
  rw [slIGV_eq_ofList] at A4
  /- 13. Counting `F` and the final arithmetic. -/
  refine ⟨GV, hGVs, hGVc, hKs, fun htop => ?_, fun F hFS hFd => ?_⟩
  · obtain ⟨v₀, hv₀⟩ : V.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro he'
      exact hp.ne_top (by rw [← hpv, he']; exact vanish_empty')
    have huniv : ∀ g, g ∈ GV := fun g => by
      obtain ⟨u, rfl⟩ := expGV_surjective (d₀ := d₀) (d₁ := d₁) Ls g
      have hu : u ∈ lieAlg Ls hGVs := by rw [htop]; trivial
      exact H0_subset hGVs hGVc (expGV_mem_H0 hGVs hu)
    have hVu : V = Set.univ := Set.eq_univ_of_forall fun g => by
      have hmem : g - v₀ ∈ GV := huniv _
      simpa using hmem v₀ hv₀
    have hpIG : p = IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
      rw [← hpv, hVu, vanish_univ]
    have hL0 : Lr2 Ls W S P T 0 ≤ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) :=
      hpIG ▸ (Lr2_mono' hS (Nat.zero_le _)).trans hLp
    have hIGne : IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≠ ⊤ :=
      (IG_isPrime (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) h2).ne_top
    have hlt := hdim_Lr2_zero_lt D hD hPh hPI (ne_top_of_le_ne_top hIGne hL0)
    have hge := hdata_le_of_le blk D ℂ hL0 hIGne
    rw [hdim_IG D hD _ _ h2] at hge
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
    rw [finrank_LieV] at this
    omega
  have hele : e ≤ n := by
    have := Submodule.finrank_le T'
    rw [finrank_TanG] at this
    omega
  have hκle : κ ≤ d₀ ^ d₀ * d₁ ^ d₁ := by
    have h1 : t₀ ≤ d₀ := by
      have := Submodule.finrank_le (((lieAlg Ls hGVs).comap vecIncl).map
        (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin m → ℂ)))
      rwa [Module.finrank_fin_fun] at this
    have h1' : t₁ ≤ d₁ := by
      have := Submodule.finrank_le ((lieAlg Ls hGVs).comap
        (torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] TanG d₀ d₁ m))
      rwa [Module.finrank_fin_fun] at this
    exact Nat.mul_le_mul (LSG.ME.pow_self_mono h1) (LSG.ME.pow_self_mono h1')
  have hTl : T ^ ℓ ≤ ℓ ^ ℓ * (T / ℓ + 1) ^ ℓ := by
    rw [← mul_pow]
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · rw [h0]; simp
    · exact Nat.pow_le_pow_left (Nat.lt_mul_div_succ T hpos).le ℓ
  have h0deg : 0 ≤ (hdata blk D ℂ (sl α J)).2 := (StrongSix.M2.hdata_pos blk D ℂ hslJ).le
  have hA1 := hdegJ (by rw [hdimJA.2, he_sum])
  rw [hl2, hdimJA.2, ← he_sum] at hA1
  have A1' : ((Rs.card * (9 * D₀) ^ t₀ * (9 * D₁) ^ t₁ * (9 * D₂) ^ t₂ * e.factorial : ℕ) : ℤ) ≤
      ((κ * 2 ^ t₂ * 48 ^ m : ℕ) : ℤ) * (3 ^ e * (hdata blk D ℂ (sl α J)).2) := by
    push_cast at hA1 ⊢
    exact hA1
  have ht₂le : t₂ ≤ n := by omega
  exact final_arith_v hℓle hele ht₂le hκle hTl hcardF h0deg A1' A1 A3 A4

end

end LSG.MEV
