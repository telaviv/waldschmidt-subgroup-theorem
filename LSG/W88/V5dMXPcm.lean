/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dMXP
import LSG.W88.V5d2Main

/-!
# The CM inputs for `gmXP` and the bridge `thm11KappaMXP_of : Theorem41Vec2 → Thm11KappaMXP`

For the curves `mxLs r = (E_i)^n ++ (E_ρ)^n` and `M = mxpM b`:
* `lamGenP_mem`: `ι⁻¹(lamGenP) ⊆ Λ(G)` (as `lamGen_mem` for MXG; `s₁` collects the `E_ρ`
  quasi-periods, `s₂` the `E_i` ones);
* `perXP_le`: the period generators `GP1, …, HP2` are periods of `G`;
* `sub_mxp`: for a nonzero member `H`, `ι(T_H)` contains an algebraic `x` with `Ψ''(x) ≠ 0`
  (a nonzero algebraic fibre vector `(0, 0, a, b)` has `Ψ'' = (a, b)`; a lattice point of one
  block gives `(a, 0)`, `(0, θᵀā)` as for MXG, with the roles of `Ψ''₁`, `Ψ''₂` swapped on the
  `E_ρ` block);
* `LiftAlg`, `PerTanRat`: `liftAlg_mx`, `perTanRat_mx` (same curves as MXG).

**`thm11KappaMXP_of : Theorem41Vec2 → MStarCopy.Thm11KappaMXP`** (via `hyperplaneKappa_of_iso2`
and `hyperplaneKappaVec2_of`).
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy

variable {r : ℕ} (b : Fin r → ℂ)

/-! ### `Λ` -/

/-- **`ι⁻¹(lamGenP) ⊆ Λ(G)`.** -/
theorem lamGenP_mem (hb : IsAdaptedFieldBasis I b) :
    ∀ g ∈ lamGenP b, (mxpIota r).symm g ∈ LamV (mxLs r) (mxpM b) := by
  rintro g ((⟨h, z, w, hzw, rfl⟩ | ⟨h, z, w, hzw, rfl⟩) | ⟨h, a, c, ha, hc, rfl⟩)
  · obtain ⟨hz, hw⟩ := zeta_lem_of_logNat hzw
    rw [mxpIota_symm_apply]
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [gPI, mxLs, Fin.append_left]
        by_cases hj : (mxE r).symm j = h
        · rw [hj, Pi.single_eq_same]; exact hz
        · rw [Pi.single_eq_of_ne hj]; exact Or.inl lemniscatic.lattice.zero_mem
      · simp only [gPI, mxLs, Fin.append_right, Pi.zero_apply]
        exact Or.inl equianharmonic.lattice.zero_mem
    · fin_cases i
      · simp only [Fin.zero_eta, Pi.sub_apply, gPI, mxpM_mulVec0, zetaV, mxLs, Fin.append_right,
          Equiv.symm_apply_apply, Pi.zero_apply, zeta_zero, mul_zero, Finset.sum_const_zero,
          Matrix.cons_val_zero, sub_zero]
        exact isAlgebraic_zero
      · simp only [Fin.mk_one, Pi.sub_apply, gPI, mxpM_mulVec1, zetaV, mxLs, Fin.append_left,
          Equiv.symm_apply_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [sum_single_mul _ _ (zeta_zero _), ← mul_sub]
        exact (theta_alg' b hb h).mul hw
  · obtain ⟨hz, hw⟩ := zeta_rho_of_logNat hzw
    rw [mxpIota_symm_apply]
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [gPR, mxLs, Fin.append_left, Pi.zero_apply]
        exact Or.inl lemniscatic.lattice.zero_mem
      · simp only [gPR, mxLs, Fin.append_right]
        by_cases hj : (mxE r).symm j = h
        · rw [hj, Pi.single_eq_same]; exact hz
        · rw [Pi.single_eq_of_ne hj]; exact Or.inl equianharmonic.lattice.zero_mem
    · fin_cases i
      · simp only [Fin.zero_eta, Pi.sub_apply, gPR, mxpM_mulVec0, zetaV, mxLs, Fin.append_right,
          Equiv.symm_apply_apply, Matrix.cons_val_zero]
        rw [sum_single_mul _ _ (zeta_zero _), ← mul_sub]
        exact (theta_alg' b hb h).mul hw
      · simp only [Fin.mk_one, Pi.sub_apply, gPR, mxpM_mulVec1, zetaV, mxLs, Fin.append_left,
          Equiv.symm_apply_apply, Pi.zero_apply, zeta_zero, mul_zero, Finset.sum_const_zero,
          Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero]
        exact isAlgebraic_zero
  · rw [mxpIota_symm_apply]
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [gPA, mxLs, Fin.append_left, Pi.zero_apply]
        exact Or.inl lemniscatic.lattice.zero_mem
      · simp only [gPA, mxLs, Fin.append_right, Pi.zero_apply]
        exact Or.inl equianharmonic.lattice.zero_mem
    · fin_cases i
      · simp only [Fin.zero_eta, Pi.sub_apply, gPA, mxpM_mulVec0, zetaV, mxLs, Fin.append_right,
          Pi.zero_apply, zeta_zero, mul_zero, Finset.sum_const_zero, Matrix.cons_val_zero,
          sub_zero]
        exact (theta_alg' b hb h).mul ha
      · simp only [Fin.mk_one, Pi.sub_apply, gPA, mxpM_mulVec1, zetaV, mxLs, Fin.append_left,
          Pi.zero_apply, zeta_zero, mul_zero, Finset.sum_const_zero, Matrix.cons_val_one,
          Matrix.cons_val_zero, sub_zero]
        exact (theta_alg' b hb h).mul hc

/-! ### Periods -/

lemma gPI_mem {h : Fin r × Fin 2} {z : ℂ} (hz : z ∈ lemniscatic.lattice) :
    (mxpIota r).symm (gPI b h z (eta lemniscatic z)) ∈
      PerV (d0 := 0) (d1 := 0) (mxLs r) (mxpM b) := by
  rw [mxpIota_symm_apply]
  refine ⟨funext fun i => i.elim0, fun i => i.elim0, fun i => ?_, funext fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [gPI, mxLs, Fin.append_left]
      by_cases hj : (mxE r).symm j = h
      · rw [hj, Pi.single_eq_same]; exact hz
      · rw [Pi.single_eq_of_ne hj]; exact lemniscatic.lattice.zero_mem
    · simp only [gPI, mxLs, Fin.append_right, Pi.zero_apply]
      exact equianharmonic.lattice.zero_mem
  · fin_cases i
    · simp only [gPI, Fin.zero_eta, mxpM_mulVec0, etaV, mxLs, Fin.append_right,
        Equiv.symm_apply_apply, Pi.zero_apply, eta_zero, mul_zero, Finset.sum_const_zero,
        Matrix.cons_val_zero]
    · simp only [gPI, Fin.mk_one, mxpM_mulVec1, etaV, mxLs, Fin.append_left,
        Equiv.symm_apply_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_single_mul _ _ (eta_zero _)]

lemma gPR_mem {h : Fin r × Fin 2} {z : ℂ} (hz : z ∈ equianharmonic.lattice) :
    (mxpIota r).symm (gPR b h z (eta equianharmonic z)) ∈
      PerV (d0 := 0) (d1 := 0) (mxLs r) (mxpM b) := by
  rw [mxpIota_symm_apply]
  refine ⟨funext fun i => i.elim0, fun i => i.elim0, fun i => ?_, funext fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [gPR, mxLs, Fin.append_left, Pi.zero_apply]
      exact lemniscatic.lattice.zero_mem
    · simp only [gPR, mxLs, Fin.append_right]
      by_cases hj : (mxE r).symm j = h
      · rw [hj, Pi.single_eq_same]; exact hz
      · rw [Pi.single_eq_of_ne hj]; exact equianharmonic.lattice.zero_mem
  · fin_cases i
    · simp only [gPR, Fin.zero_eta, mxpM_mulVec0, etaV, mxLs, Fin.append_right,
        Equiv.symm_apply_apply, Matrix.cons_val_zero]
      rw [sum_single_mul _ _ (eta_zero _)]
    · simp only [gPR, Fin.mk_one, mxpM_mulVec1, etaV, mxLs, Fin.append_left,
        Equiv.symm_apply_apply, Pi.zero_apply, eta_zero, mul_zero, Finset.sum_const_zero,
        Matrix.cons_val_one, Matrix.cons_val_zero]

/-- **The period generators are periods of `G`.** -/
theorem perXP_le :
    perXP b ≤ (OmV 0 0 (mxLs r) (mxpM b)).map ((mxpIota r).toLinearMap.restrictScalars ℚ) := by
  have key : ∀ x, (mxpIota r).symm x ∈ PerV (d0 := 0) (d1 := 0) (mxLs r) (mxpM b) →
      x ∈ (OmV 0 0 (mxLs r) (mxpM b)).map ((mxpIota r).toLinearMap.restrictScalars ℚ) := by
    intro x hx
    refine ⟨(mxpIota r).symm x, Submodule.subset_span hx, ?_⟩
    simp
  rw [perXP, Submodule.span_le]
  rintro _ (((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩) <;> apply key
  · have := gPI_mem b (h := j) lemniscatic.ω₁_mem_lattice
    rw [eta_varpi] at this; push_cast at this; exact this
  · have h2 := gPI_mem b (h := j) lemniscatic.ω₂_mem_lattice
    have : eta lemniscatic lemniscatic.ω₂ = -I * ((Real.pi : ℂ) / varpi) := by
      have := eta_lem 0 1
      simp only [Int.cast_zero, zero_mul, Int.cast_one, one_mul, zero_add] at this
      rw [this, etaLem]; push_cast; ring
    rw [this] at h2
    exact h2
  · have := gPR_mem b (h := j) equianharmonic.ω₁_mem_lattice
    rw [eta_omegaRho] at this; exact this
  · have h2 := gPR_mem b (h := j) equianharmonic.ω₂_mem_lattice
    have : eta equianharmonic equianharmonic.ω₂ = rhoBar * etaRho := by
      have := eta_rho 0 1
      simp only [Int.cast_zero, zero_mul, Int.cast_one, one_mul, zero_add] at this
      rw [this, etaR]; push_cast; ring
    rw [this] at h2
    exact h2

/-! ### Members -/

section Sub

lemma tan_eq_bot_ofP (H : SubgroupDataV (d0 := 0) (d1 := 0) (mxLs r) (mxpM b))
    (hΓ : H.gam = ⊥) (hP : perTan (mxLs r) (mxpM b) H.t = ⊥) : H.tan = ⊥ := by
  have hT : (torusLie H.U).map (torIncl (d0 := 0) (m := mxN r + mxN r) (r := 2)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨x, -, rfl⟩
    have : x = 0 := Subsingleton.elim _ _
    rw [this, map_zero]
  rw [SubgroupDataV.tan, hΓ, hP, hT]; simp

lemma iotaP_g2 (z : Fin (mxN r + mxN r) → ℂ) (s : Fin 2 → ℂ) : mxpIota r (g2Incl (z, s)) =
    (fun h => z (Fin.castAdd _ (mxE r h)), fun h => z (Fin.natAdd _ (mxE r h)), s 0, s 1) := rfl

lemma algXP_iota_g2 {z : Fin (mxN r + mxN r) → ℂ} {s : Fin 2 → ℂ} (hz : AlgVec z)
    (hs : AlgVec s) : algXP (mxpIota r (g2Incl (z, s))) :=
  ⟨fun _ => hz _, fun _ => hz _, hs 0, hs 1⟩

/-- A nonzero lattice point of one block gives `x ∈ ι(T_H)` with `ψ_A(x) ≠ 0` or `ψ_B(x) ≠ 0`,
where `ψ_A` reads the block's base coordinates and `ψ_B` the block's fibre coordinate. -/
lemma block_caseP (hb : IsAdaptedFieldBasis I b)
    (H : SubgroupDataV (d0 := 0) (d1 := 0) (mxLs r) (mxpM b)) {L : PeriodPair} {α : ℂ}
    (hd : CMData L α) (E : (Fin (mxN r) → ℂ) →ₗ[ℂ] (Fin (mxN r + mxN r) → ℂ))
    (ψA ψB : TXP r →ₗ[ℂ] ℂ)
    (hA : ∀ v, ψA (mxpIota r (g2Incl (E v, (mxpM b).mulVec 0))) =
      ∑ h, theta I b h * v (mxE r h))
    (hB : ∀ v, ψB (mxpIota r (g2Incl (0, (mxpM b).mulVec (E v)))) =
      ∑ h, theta I b h * v (mxE r h))
    (hEalg : ∀ v, AlgVec v → AlgVec (E v)) {l : Fin (mxN r) → ℂ} (hl : ∀ j, l j ∈ L.lattice)
    (hl0 : l ≠ 0) (h1 : (E l, 0) ∈ perTanId (mxLs r) H.t)
    (h2 : (0, E (etaV (fun _ => L) l)) ∈ perTanId (mxLs r) H.t) :
    ∃ x ∈ H.tan.map (mxpIota r).toLinearMap, algXP x ∧ (ψA x ≠ 0 ∨ ψB x ≠ 0) := by
  have hg2 : ∀ x ∈ perTanId (mxLs r) H.t, mxpIota r (g2Incl (x.1, (mxpM b).mulVec x.2)) ∈
      H.tan.map (mxpIota r).toLinearMap := fun x hx =>
    ⟨g2Incl (x.1, (mxpM b).mulVec x.2), Submodule.mem_sup_right (Submodule.mem_map_of_mem
      (Submodule.mem_map_of_mem (f := LinearMap.prodMap LinearMap.id (Matrix.mulVecLin (mxpM b)))
        hx)), rfl⟩
  set a : Fin (mxN r) → ℂ := fun j => l j / L.ω₁
  set ac : Fin (mxN r) → ℂ := fun j => starRingEnd ℂ (a j)
  have hω := hd.ω₁_ne
  have hη := hd.eta_one_ne
  have ha1 : (E a, (0 : Fin (mxN r + mxN r) → ℂ)) ∈ perTanId (mxLs r) H.t := by
    have : (E a, (0 : Fin (mxN r + mxN r) → ℂ)) = L.ω₁⁻¹ • (E l, 0) := by
      have : a = L.ω₁⁻¹ • l := funext fun j => by simp [a, div_eq_inv_mul]
      rw [this, map_smul]; simp
    rw [this]; exact Submodule.smul_mem _ _ h1
  have ha2 : ((0 : Fin (mxN r + mxN r) → ℂ), E ac) ∈ perTanId (mxLs r) H.t := by
    have : ((0 : Fin (mxN r + mxN r) → ℂ), E ac) =
        (eta L L.ω₁)⁻¹ • (0, E (etaV (fun _ => L) l)) := by
      have : ac = (eta L L.ω₁)⁻¹ • etaV (fun _ => L) l := funext fun j => by
        simp only [ac, a, Pi.smul_apply, smul_eq_mul, etaV_eq hd hl j]
        field_simp
      rw [this, map_smul]; simp
    rw [this]; exact Submodule.smul_mem _ _ h2
  have hA' : AlgVec a := fun j => hd.isAlgebraic_div (hl j)
  have hAc : AlgVec ac := fun j => isAlgebraic_conj (hA' j)
  by_contra hcon
  push Not at hcon
  have e1 := (hcon _ (hg2 _ ha1) (algXP_iota_g2 (hEalg a hA')
    (algVec_mulVec (mxpM_alg b hb) fun _ => isAlgebraic_zero))).1
  have e2 := (hcon _ (hg2 _ ha2) (algXP_iota_g2 (fun _ => isAlgebraic_zero)
    (algVec_mulVec (mxpM_alg b hb) (hEalg ac hAc)))).2
  rw [hA] at e1
  rw [hB] at e2
  choose m n hmn using fun j => hd.div_eq (hl j)
  have hαc : α ≠ starRingEnd ℂ α := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith [hd.im_pos]
  have hK := lemmaK hb.indep hαc (fun h => m (mxE r h)) (fun h => n (mxE r h))
    (by rw [← e1]; exact Finset.sum_congr rfl fun h _ => by rw [← hmn])
    (by rw [← e2]; exact Finset.sum_congr rfl fun h _ => by simp only [ac, a]; rw [← hmn])
  apply hl0
  funext j
  obtain ⟨hm, hn⟩ := hK ((mxE r).symm j)
  simp only [Equiv.apply_symm_apply] at hm hn
  have : l j / L.ω₁ = 0 := by rw [hmn, hm, hn]; simp
  rwa [div_eq_zero_iff, or_iff_left hω] at this

/-- **`hsub`**: `ι(T_H) ∈ gmXP.sub` for every nonzero member. -/
theorem sub_mxp (hb : IsAdaptedFieldBasis I b)
    (H : SubgroupDataV (d0 := 0) (d1 := 0) (mxLs r) (mxpM b)) (hH : H.tan ≠ ⊥) :
    (gmXP b).sub (H.tan.map (mxpIota r).toLinearMap) := by
  right
  by_cases hΓ : H.gam = ⊥
  · -- the abelian part is nonzero
    have hP : perTan (mxLs r) (mxpM b) H.t ≠ ⊥ := fun hP => hH (tan_eq_bot_ofP b H hΓ hP)
    have ht : H.t ≠ ⊥ := by
      rintro ht
      apply hP
      rw [perTan, perTanId, ht, Submodule.map_span, Submodule.span_eq_bot]
      rintro _ ⟨⟨l, e⟩, ⟨hl, -, he⟩, rfl⟩
      simp only [Submodule.mem_bot] at hl he
      subst hl; subst he
      have : etaV (mxLs r) 0 = 0 := funext fun j => eta_zero _
      simp [this]
    obtain ⟨l, ⟨hlt, hl⟩, hl0⟩ : ∃ l ∈ {z | z ∈ H.t ∧ ∀ j, z j ∈ (mxLs r j).lattice}, l ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply ht
      rw [← span_lat_eq H.t_ab, Submodule.span_eq_bot]
      exact hcon
    have hs := splits_mx r H.t H.t_ab
    rw [mxLs_eq] at hl
    by_cases h1 : pr₁ l = 0
    · -- the `E_ρ` block
      have h2 : pr₂ l ≠ 0 := by
        intro h2; apply hl0; rw [decomp l, h1, h2, map_zero, map_zero, add_zero]
      have hl₂t : pr₂ l ∈ H.t.comap inr₂ := splits_right hs hlt hl
      have hP1 := map_right_le (Ls₁ := fun _ : Fin (mxN r) => lemniscatic)
        (Submodule.mem_map_of_mem (fst_mem cmRho hl₂t (lat_right hl)))
      have hP2 := map_right_le (Ls₁ := fun _ : Fin (mxN r) => lemniscatic)
        (Submodule.mem_map_of_mem (snd_mem cmRho hl₂t (lat_right hl)))
      obtain ⟨x, hx, hxa, hx0⟩ := block_caseP b hb H cmRho inr₂ (psiP2 b) (psiP1 b)
        (fun v => by
          rw [iotaP_g2, psiP2_apply']
          simp only [inr₂_right, Matrix.mulVec_zero, Pi.zero_apply, add_zero])
        (fun v => by
          rw [iotaP_g2, psiP1_apply', mxpM_mulVec0]
          simp only [inr₂_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add])
        (fun v hv => algVec_inr hv) (l := pr₂ l) (lat_right hl) h2 (by
          have e : (inr₂ (pr₂ l), (0 : Fin (mxN r + mxN r) → ℂ)) = E₂ (pr₂ l, 0) := by
            rw [LinearMap.prodMap_apply, map_zero]
          rw [e]; exact hP1) (by
          have e : ((0 : Fin (mxN r + mxN r) → ℂ),
              inr₂ (etaV (fun _ => equianharmonic) (pr₂ l))) =
              E₂ (0, etaV (fun _ => equianharmonic) (pr₂ l)) := by
            rw [LinearMap.prodMap_apply, map_zero]
          rw [e]; exact hP2)
      exact ⟨x, hx, hxa, hx0.symm⟩
    · -- the `E_i` block
      have hl₁t : pr₁ l ∈ H.t.comap inl₁ := hs l hlt hl
      have hP1 := map_left_le (Ls₂ := fun _ : Fin (mxN r) => equianharmonic)
        (Submodule.mem_map_of_mem (fst_mem cmLem hl₁t (lat_left hl)))
      have hP2 := map_left_le (Ls₂ := fun _ : Fin (mxN r) => equianharmonic)
        (Submodule.mem_map_of_mem (snd_mem cmLem hl₁t (lat_left hl)))
      refine block_caseP b hb H cmLem inl₁ (psiP1 b) (psiP2 b)
        (fun v => by
          rw [iotaP_g2, psiP1_apply']
          simp only [inl₁_left, Matrix.mulVec_zero, Pi.zero_apply, add_zero])
        (fun v => by
          rw [iotaP_g2, psiP2_apply', mxpM_mulVec1]
          simp only [inl₁_left, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add])
        (fun v hv => algVec_inl hv) (l := pr₁ l) (lat_left hl) h1 ?_ ?_
      · have e : (inl₁ (pr₁ l), (0 : Fin (mxN r + mxN r) → ℂ)) = E₁ (pr₁ l, 0) := by
          rw [LinearMap.prodMap_apply, map_zero]
        rw [e]; exact hP1
      · have e : ((0 : Fin (mxN r + mxN r) → ℂ), inl₁ (etaV (fun _ => lemniscatic) (pr₁ l))) =
            E₁ (0, etaV (fun _ => lemniscatic) (pr₁ l)) := by
          rw [LinearMap.prodMap_apply, map_zero]
        rw [e]; exact hP2
  · -- the vector part is nonzero
    obtain ⟨w, hwΓ, hwa, hw0⟩ : ∃ w ∈ H.gam, AlgPair w ∧ w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hΓ
      rw [H.gam_rat, Submodule.span_eq_bot]
      exact fun w hw => hcon w hw.1 hw.2
    refine ⟨mxpIota r (vecIncl w), ⟨vecIncl w, Submodule.mem_sup_left
      (Submodule.mem_sup_left (Submodule.mem_map_of_mem hwΓ)), rfl⟩, ?_, ?_⟩
    · exact ⟨fun _ => isAlgebraic_zero, fun _ => isAlgebraic_zero, hwa.2 0, hwa.2 1⟩
    · have : w.2 0 ≠ 0 ∨ w.2 1 ≠ 0 := by
        by_contra hcon; push Not at hcon
        apply hw0
        exact Prod.ext (funext fun i => i.elim0)
          (funext fun i => by fin_cases i; exacts [hcon.1, hcon.2])
      rcases this with h | h
      · left; simpa [psiP1_apply', mxpIota, vecIncl] using h
      · right; simpa [psiP2_apply', mxpIota, vecIncl] using h

end Sub

/-! ### The bridge -/

/-- **Theorem MX′'s hypothesis `Thm11KappaMXP` from `Theorem41Vec2`.** -/
theorem thm11KappaMXP_of (h : Theorem41Vec2) : MStarCopy.Thm11KappaMXP := by
  intro hg₂ hg₃ hg₂' hg₃' r b hb
  have hLs : ∀ j, IsAlgebraic ℚ (mxLs r j).g₂ ∧ IsAlgebraic ℚ (mxLs r j).g₃ := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [mxLs, Fin.append_left]; exact ⟨hg₂, hg₃⟩
    · simp only [mxLs, Fin.append_right]; exact ⟨hg₂', hg₃'⟩
  have hM := mxpM_alg b hb
  refine hyperplaneKappa_of_iso2 (hyperplaneKappaVec2_of h) hLs hM rfl le_rfl
    (liftAlg_mx hg₂ hg₃ hg₂' hg₃' r) (perTanRat_mx r) (gmXP b) (mxpIota r) ?_
    (lamVSub (d0 := 0) (d1 := 0) (mxLs r) (mxpM b) hLs hM) (fun _ hx => hx) ?_ (perXP_le b) rfl
    ?_ (sub_mxp b hb)
  · -- (i) algebraic vectors
    intro v hv
    rw [mxpIota_symm_apply]
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun k => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · change IsAlgebraic ℚ (Fin.append (fun i => v.1 ((mxE r).symm i))
          (fun i => v.2.1 ((mxE r).symm i)) (Fin.castAdd (mxN r) i))
        rw [Fin.append_left]; exact hv.1 _
      · change IsAlgebraic ℚ (Fin.append (fun i => v.1 ((mxE r).symm i))
          (fun i => v.2.1 ((mxE r).symm i)) (Fin.natAdd (mxN r) i))
        rw [Fin.append_right]; exact hv.2.1 _
    · fin_cases i
      · exact hv.2.2.1
      · exact hv.2.2.2
  · -- (ii) common denominators
    intro y hy
    have hcl : y ∈ Submodule.span ℚ ((AddSubgroup.closure (lamGenP b) : AddSubgroup (TXP r)) :
        Set (TXP r)) := by
      rw [K11.span_closure_eq]; exact hy
    obtain ⟨N, hN, hNy⟩ := K11.exists_nsmul_mem_of_mem_span _ hcl
    refine ⟨N, hN, ?_⟩
    rw [← map_nsmul]
    have hle : AddSubgroup.closure (lamGenP b) ≤
        (lamVSub (d0 := 0) (d1 := 0) (mxLs r) (mxpM b) hLs hM).comap
          (mxpIota r).symm.toLinearMap.toAddMonoidHom :=
      (AddSubgroup.closure_le _).mpr fun g hg => lamGenP_mem b hb g hg
    exact hle hNy
  · -- `d₂ = 2n + 2 = m + r`
    change 2 * Fintype.card (Fin r × Fin 2) + 2 =
      Fintype.card (Fin r × Fin 2) + Fintype.card (Fin r × Fin 2) + 2
    omega

end LSG.W88.V5d
