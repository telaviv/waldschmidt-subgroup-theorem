/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dMXG
import LSG.CM.Inst
import LSG.CM.Append

/-!
# The CM inputs of `thm11KappaMXG_of_cm`, and the unconditional bridge `thm11KappaMXG_of`

For the curves `mxLs r = (E_i)^n ++ (E_ρ)^n` (`E_i = ϖℤ[i]`, `E_ρ = Ω_ρℤ[ρ]`, lean_mstar's period
pairs) and `M = (θᵀ, θᵀ)`:
* `splits_mx`: abelian subvarieties of `E_i^n × E_ρ^n` split (`√3 i Λ_ρ ⊆ Λ_ρ`, `√3 ∉ ℚ`);
* `liftAlg_mx`, `perTanRat_mx`: `LiftAlg`, `PerTanRat` (blocks: `LSG.CM.Block`);
* `lamGen_mem`: `ι⁻¹(lamGenX) ⊆ Λ(G)` (quasi-periods `etaLem`, `etaR` are LSG's `η`,
  `Ext.zeta = ζ`), so `lamVSub` (the `ζ` addition theorem) is the subgroup `hΛ`;
* `perXG_le`: the period generators `GX1, …, HX2` are periods of `G` (`η(ϖ) = π/ϖ`, …);
* `sub_mx`: for a nonzero member `H`, `ι(T_H)` contains an algebraic `x` with `ψ''(x) ≠ 0`
  (a vector-group vector, or `(a, 0)`/`(0, θᵀā)` from a block lattice point, and
  `θᵀa = θᵀā = 0 ⇒ a = 0` for `a ∈ ℤ[α]^n` by `ℚ`-independence of `θ`).

**`thm11KappaMXG_of : Theorem41VecLA → MStarCopy.Thm11KappaMXG`**.
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy

variable {r : ℕ}

lemma mxLs_eq (r : ℕ) : mxLs r = Fin.append (fun _ : Fin (mxN r) => lemniscatic)
    (fun _ : Fin (mxN r) => equianharmonic) := rfl

/-! ### Splitting, `LiftAlg`, `PerTanRat` -/

theorem splits_mx (r : ℕ) (t : Submodule ℂ (Fin (mxN r + mxN r) → ℂ))
    (hab : IsAbelianTangent (mxLs r) t) :
    Splits (fun _ : Fin (mxN r) => lemniscatic) (fun _ : Fin (mxN r) => equianharmonic) t :=
  splits_of_irrational (c := Real.sqrt 3) (by simpa using Nat.prime_three.irrational_sqrt)
    (fun _ _ hx => I_mul_mem_lem hx) (fun _ _ hx => sqrt3_I_mul_mem hx) hab

theorem perTanRat_mx (r : ℕ) : PerTanRat (mxLs r) :=
  perTanRat_append (perTanRat_block cmLem) (perTanRat_block cmRho) (splits_mx r)

theorem liftAlg_mx (hg₂ : IsAlgebraic ℚ lemniscatic.g₂) (hg₃ : IsAlgebraic ℚ lemniscatic.g₃)
    (hg₂' : IsAlgebraic ℚ equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ equianharmonic.g₃) (r : ℕ) :
    LiftAlg (mxLs r) :=
  liftAlg_append (liftAlg_block hg₂ hg₃ cmLem) (liftAlg_block hg₂' hg₃' cmRho) (splits_mx r)

/-! ### Coordinates -/

variable (b : Fin r → ℂ)

lemma sum_mxE (F : Fin (mxN r) → ℂ) : ∑ i, F i = ∑ h, F (mxE r h) :=
  ((mxE r).sum_comp F).symm

lemma mxM_mulVec (x : Fin (mxN r + mxN r) → ℂ) : (mxM b).mulVec x 0 =
    ∑ h, theta I b h * x (Fin.castAdd _ (mxE r h)) +
      ∑ h, theta I b h * x (Fin.natAdd _ (mxE r h)) := by
  simp only [Matrix.mulVec, dotProduct, mxM, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  rw [sum_mxE, sum_mxE]
  simp

lemma psiX1_apply (v : TXG r) : psiX1 b v = v.1 + ∑ h, theta I b h * v.2.1 h +
    ∑ h, theta I b h * v.2.2.1 h := rfl

lemma psiX2_apply (v : TXG r) : psiX2 (r := r) v = v.2.2.2 := rfl

lemma theta_alg' (hb : IsAdaptedFieldBasis I b) (h : Fin r × Fin 2) : IsAlgebraic ℚ (theta I b h) :=
  theta_alg hb.alg h

lemma mxM_alg (hb : IsAdaptedFieldBasis I b) : AlgMat (mxM b) := by
  intro i j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp only [mxM, Fin.append_left]; exact theta_alg hb.alg _
  · simp only [mxM, Fin.append_right]; exact theta_alg hb.alg _

lemma sum_single_mul (θ : Fin r × Fin 2 → ℂ) (f : ℂ → ℂ) (hf : f 0 = 0) (h₀ : Fin r × Fin 2)
    (z : ℂ) : ∑ h, θ h * f ((Pi.single h₀ z : Fin r × Fin 2 → ℂ) h) = θ h₀ * f z := by
  rw [Finset.sum_eq_single h₀]
  · simp
  · intro h _ hh; simp [hh, hf]
  · simp

/-! ### `hΛ` -/

section Lam

lemma zeta_lem_of_logNat {z w : ℂ} (h : LogNat lemniscatic etaLem z w) :
    (z ∈ lemniscatic.lattice ∨ IsAlgebraic ℚ (lemniscatic.weierstrassP z)) ∧
      IsAlgebraic ℚ (w - zeta lemniscatic z) := by
  rcases h with ⟨m, n, rfl, hw⟩ | ⟨hz, hp, -, hw⟩
  · have hl : (m : ℂ) * lemniscatic.ω₁ + n * lemniscatic.ω₂ ∈ lemniscatic.lattice :=
      PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩
    refine ⟨Or.inl hl, ?_⟩
    rwa [zeta_of_mem_lattice _ hl, eta_lem]
  · exact ⟨Or.inr hp, by rwa [← ext_zeta]⟩

lemma zeta_rho_of_logNat {z w : ℂ} (h : LogNat equianharmonic etaR z w) :
    (z ∈ equianharmonic.lattice ∨ IsAlgebraic ℚ (equianharmonic.weierstrassP z)) ∧
      IsAlgebraic ℚ (w - zeta equianharmonic z) := by
  rcases h with ⟨m, n, rfl, hw⟩ | ⟨hz, hp, -, hw⟩
  · have hl : (m : ℂ) * equianharmonic.ω₁ + n * equianharmonic.ω₂ ∈ equianharmonic.lattice :=
      PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩
    refine ⟨Or.inl hl, ?_⟩
    rwa [zeta_of_mem_lattice _ hl, eta_rho]
  · exact ⟨Or.inr hp, by rwa [← ext_zeta]⟩

/-- **`ι⁻¹(lamGenX) ⊆ Λ(G)`.** -/
theorem lamGen_mem (hb : IsAdaptedFieldBasis I b) :
    ∀ g ∈ lamGenX b, (mxIota r).symm g ∈ LamV (mxLs r) (mxM b) := by
  rintro g ((⟨h, z, w, hzw, rfl⟩ | ⟨h, z, w, hzw, rfl⟩) | ⟨h, a, t, ha, ht, rfl⟩)
  · obtain ⟨hz, hw⟩ := zeta_lem_of_logNat hzw
    rw [mxIota_symm_apply]
    refine ⟨fun _ => isAlgebraic_zero, fun i => i.elim0, fun i => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [gXI, mxLs, Fin.append_left]
        by_cases hj : (mxE r).symm j = h
        · rw [hj, Pi.single_eq_same]; exact hz
        · rw [Pi.single_eq_of_ne hj]; exact Or.inl lemniscatic.lattice.zero_mem
      · simp only [gXI, mxLs, Fin.append_right, Pi.zero_apply]
        exact Or.inl equianharmonic.lattice.zero_mem
    · rw [Subsingleton.elim i 0]
      simp only [Pi.sub_apply, gXI, mxM_mulVec, zetaV, mxLs, Fin.append_left, Fin.append_right,
        Equiv.symm_apply_apply, Pi.zero_apply, zeta_zero, mul_zero, Finset.sum_const_zero, add_zero]
      rw [sum_single_mul _ _ (zeta_zero _)]
      rw [← mul_sub]
      exact (theta_alg' b hb h).mul hw
  · obtain ⟨hz, hw⟩ := zeta_rho_of_logNat hzw
    rw [mxIota_symm_apply]
    refine ⟨fun _ => isAlgebraic_zero, fun i => i.elim0, fun i => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [gXR, mxLs, Fin.append_left, Pi.zero_apply]
        exact Or.inl lemniscatic.lattice.zero_mem
      · simp only [gXR, mxLs, Fin.append_right]
        by_cases hj : (mxE r).symm j = h
        · rw [hj, Pi.single_eq_same]; exact hz
        · rw [Pi.single_eq_of_ne hj]; exact Or.inl equianharmonic.lattice.zero_mem
    · rw [Subsingleton.elim i 0]
      simp only [Pi.sub_apply, gXR, mxM_mulVec, zetaV, mxLs, Fin.append_left, Fin.append_right,
        Equiv.symm_apply_apply, Pi.zero_apply, zeta_zero, mul_zero, Finset.sum_const_zero, zero_add]
      rw [sum_single_mul _ _ (zeta_zero _)]
      rw [← mul_sub]
      exact (theta_alg' b hb h).mul hw
  · rw [mxIota_symm_apply]
    refine ⟨fun _ => (theta_alg' b hb h).mul ha, fun i => i.elim0, fun i => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [gXA, mxLs, Fin.append_left, Pi.zero_apply]
        exact Or.inl lemniscatic.lattice.zero_mem
      · simp only [gXA, mxLs, Fin.append_right, Pi.zero_apply]
        exact Or.inl equianharmonic.lattice.zero_mem
    · rw [Subsingleton.elim i 0]
      simp only [Pi.sub_apply, gXA, mxM_mulVec, zetaV, mxLs, Fin.append_left, Fin.append_right,
        Pi.zero_apply, zeta_zero, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
      exact (theta_alg' b hb h).mul ht

end Lam

/-! ### `hper` -/

section Per

lemma gXI_mem {h : Fin r × Fin 2} {z : ℂ} (hz : z ∈ lemniscatic.lattice) :
    (mxIota r).symm (gXI b h z (eta lemniscatic z)) ∈
      PerV (d0 := 1) (d1 := 0) (mxLs r) (mxM b) := by
  rw [mxIota_symm_apply]
  refine ⟨funext fun _ => rfl, fun i => i.elim0, fun i => ?_, funext fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [gXI, mxLs, Fin.append_left]
      by_cases hj : (mxE r).symm j = h
      · rw [hj, Pi.single_eq_same]; exact hz
      · rw [Pi.single_eq_of_ne hj]; exact lemniscatic.lattice.zero_mem
    · simp only [gXI, mxLs, Fin.append_right, Pi.zero_apply]
      exact equianharmonic.lattice.zero_mem
  · fin_cases i
    simp only [gXI, Fin.zero_eta, mxM_mulVec, etaV, mxLs, Fin.append_left, Fin.append_right,
      Equiv.symm_apply_apply, Pi.zero_apply, eta_zero, mul_zero, Finset.sum_const_zero, add_zero]
    rw [sum_single_mul _ _ (eta_zero _)]

lemma gXR_mem {h : Fin r × Fin 2} {z : ℂ} (hz : z ∈ equianharmonic.lattice) :
    (mxIota r).symm (gXR b h z (eta equianharmonic z)) ∈
      PerV (d0 := 1) (d1 := 0) (mxLs r) (mxM b) := by
  rw [mxIota_symm_apply]
  refine ⟨funext fun _ => rfl, fun i => i.elim0, fun i => ?_, funext fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [gXR, mxLs, Fin.append_left, Pi.zero_apply]
      exact lemniscatic.lattice.zero_mem
    · simp only [gXR, mxLs, Fin.append_right]
      by_cases hj : (mxE r).symm j = h
      · rw [hj, Pi.single_eq_same]; exact hz
      · rw [Pi.single_eq_of_ne hj]; exact equianharmonic.lattice.zero_mem
  · fin_cases i
    simp only [gXR, Fin.zero_eta, mxM_mulVec, etaV, mxLs, Fin.append_left, Fin.append_right,
      Equiv.symm_apply_apply, Pi.zero_apply, eta_zero, mul_zero, Finset.sum_const_zero, zero_add]
    rw [sum_single_mul _ _ (eta_zero _)]

/-- **The period generators are periods of `G`.** -/
theorem perXG_le :
    perXG b ≤ (OmV 1 0 (mxLs r) (mxM b)).map ((mxIota r).toLinearMap.restrictScalars ℚ) := by
  have key : ∀ x, (mxIota r).symm x ∈ PerV (d0 := 1) (d1 := 0) (mxLs r) (mxM b) →
      x ∈ (OmV 1 0 (mxLs r) (mxM b)).map ((mxIota r).toLinearMap.restrictScalars ℚ) := by
    intro x hx
    refine ⟨(mxIota r).symm x, Submodule.subset_span hx, ?_⟩
    simp
  rw [perXG, Submodule.span_le]
  rintro _ (((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩) <;> apply key
  · have := gXI_mem b (h := j) lemniscatic.ω₁_mem_lattice
    rw [eta_varpi] at this; push_cast at this; exact this
  · have h2 := gXI_mem b (h := j) lemniscatic.ω₂_mem_lattice
    have : eta lemniscatic lemniscatic.ω₂ = -I * ((Real.pi : ℂ) / varpi) := by
      have := eta_lem 0 1
      simp only [Int.cast_zero, zero_mul, Int.cast_one, one_mul, zero_add] at this
      rw [this, etaLem]; push_cast; ring
    rw [this] at h2
    exact h2
  · have := gXR_mem b (h := j) equianharmonic.ω₁_mem_lattice
    rw [eta_omegaRho] at this; exact this
  · have h2 := gXR_mem b (h := j) equianharmonic.ω₂_mem_lattice
    have : eta equianharmonic equianharmonic.ω₂ = rhoBar * etaRho := by
      have := eta_rho 0 1
      simp only [Int.cast_zero, zero_mul, Int.cast_one, one_mul, zero_add] at this
      rw [this, etaR]; push_cast; ring
    rw [this] at h2
    exact h2

end Per

/-! ### `hsub` -/

section Sub

/-- **Lemma K, the part used**: `θᵀa = θᵀā = 0` with `a ∈ ℤ[α]^n`, `α ∉ ℝ`, forces `a = 0`. -/
lemma lemmaK {ι : Type*} [Fintype ι] {θ : ι → ℂ} (hθ : LinearIndependent ℚ θ) {α : ℂ}
    (hα : α ≠ starRingEnd ℂ α) (m n : ι → ℤ)
    (h1 : ∑ i, θ i * ((m i : ℂ) + n i * α) = 0)
    (h2 : ∑ i, θ i * starRingEnd ℂ ((m i : ℂ) + n i * α) = 0) : ∀ i, m i = 0 ∧ n i = 0 := by
  have hz : ∀ k : ι → ℤ, ∑ i, θ i * (k i : ℂ) = 0 → ∀ i, k i = 0 := by
    intro k hk i
    have := Fintype.linearIndependent_iff.mp hθ (fun i => (k i : ℚ)) (by
      rw [← hk]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Rat.smul_def]; push_cast; ring)
    exact_mod_cast this i
  have hn : ∑ i, θ i * (n i : ℂ) = 0 := by
    have h3 : (α - starRingEnd ℂ α) * ∑ i, θ i * (n i : ℂ) =
        (∑ i, θ i * ((m i : ℂ) + n i * α)) - ∑ i, θ i * starRingEnd ℂ ((m i : ℂ) + n i * α) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_add, map_mul, map_intCast]; ring
    rw [h1, h2, sub_zero] at h3
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hα)
  have hm : ∑ i, θ i * (m i : ℂ) = 0 := by
    have : ∑ i, θ i * ((m i : ℂ) + n i * α) = ∑ i, θ i * (m i : ℂ) + α * ∑ i, θ i * (n i : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hn, mul_zero, add_zero] at h1; exact h1
  exact fun i => ⟨hz m hm i, hz n hn i⟩

lemma tan_eq_bot_of (H : SubgroupDataV (d0 := 1) (d1 := 0) (mxLs r) (mxM b))
    (hΓ : H.gam = ⊥) (hP : perTan (mxLs r) (mxM b) H.t = ⊥) : H.tan = ⊥ := by
  have hT : (torusLie H.U).map (torIncl (d0 := 1) (m := mxN r + mxN r) (r := 1)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨x, -, rfl⟩
    have : x = 0 := Subsingleton.elim _ _
    rw [this, map_zero]
  rw [SubgroupDataV.tan, hΓ, hP, hT]; simp

lemma iota_g2 (z : Fin (mxN r + mxN r) → ℂ) (s : Fin 1 → ℂ) : mxIota r (g2Incl (z, s)) =
    (0, fun h => z (Fin.castAdd _ (mxE r h)), fun h => z (Fin.natAdd _ (mxE r h)), s 0) := rfl

lemma algXG_iota_g2 {z : Fin (mxN r + mxN r) → ℂ} {s : Fin 1 → ℂ} (hz : AlgVec z) (hs : AlgVec s) :
    algXG (mxIota r (g2Incl (z, s))) :=
  ⟨isAlgebraic_zero, fun _ => hz _, fun _ => hz _, hs 0⟩

/-- A nonzero lattice point of one block gives `x ∈ ι(T_H)` with `ψ''(x) ≠ 0`. -/
lemma block_case (hb : IsAdaptedFieldBasis I b)
    (H : SubgroupDataV (d0 := 1) (d1 := 0) (mxLs r) (mxM b)) {L : PeriodPair} {α : ℂ}
    (hd : CMData L α) (E : (Fin (mxN r) → ℂ) →ₗ[ℂ] (Fin (mxN r + mxN r) → ℂ))
    (hE : ∀ v, ∑ h, theta I b h * E v (Fin.castAdd _ (mxE r h)) +
      ∑ h, theta I b h * E v (Fin.natAdd _ (mxE r h)) = ∑ h, theta I b h * v (mxE r h))
    (hEalg : ∀ v, AlgVec v → AlgVec (E v)) {l : Fin (mxN r) → ℂ} (hl : ∀ j, l j ∈ L.lattice)
    (hl0 : l ≠ 0) (h1 : (E l, 0) ∈ perTanId (mxLs r) H.t)
    (h2 : (0, E (etaV (fun _ => L) l)) ∈ perTanId (mxLs r) H.t) :
    ∃ x ∈ H.tan.map (mxIota r).toLinearMap, algXG x ∧ (psiX1 b x ≠ 0 ∨ psiX2 (r := r) x ≠ 0) := by
  have hg2 : ∀ x ∈ perTanId (mxLs r) H.t, mxIota r (g2Incl (x.1, (mxM b).mulVec x.2)) ∈
      H.tan.map (mxIota r).toLinearMap := fun x hx =>
    ⟨g2Incl (x.1, (mxM b).mulVec x.2), Submodule.mem_sup_right (Submodule.mem_map_of_mem
      (Submodule.mem_map_of_mem (f := LinearMap.prodMap LinearMap.id (Matrix.mulVecLin (mxM b)))
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
  have hA : AlgVec a := fun j => hd.isAlgebraic_div (hl j)
  have hAc : AlgVec ac := fun j => isAlgebraic_conj (hA j)
  by_contra hcon
  push Not at hcon
  have e1 := (hcon _ (hg2 _ ha1) (algXG_iota_g2 (hEalg a hA)
    (algVec_mulVec (r := 1) (mxM_alg b hb) fun _ => isAlgebraic_zero))).1
  have e2 := (hcon _ (hg2 _ ha2) (algXG_iota_g2 (fun _ => isAlgebraic_zero)
    (algVec_mulVec (mxM_alg b hb) (hEalg ac hAc)))).2
  simp only [iota_g2, psiX1_apply, zero_add] at e1
  rw [hE] at e1
  simp only [iota_g2, psiX2_apply] at e2
  rw [mxM_mulVec, hE] at e2
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

/-- **`hsub`**: `ι(T_H) ∈ gmXG.sub` for every nonzero member. -/
theorem sub_mx (hb : IsAdaptedFieldBasis I b)
    (H : SubgroupDataV (d0 := 1) (d1 := 0) (mxLs r) (mxM b)) (hH : H.tan ≠ ⊥) :
    (gmXG b).sub (H.tan.map (mxIota r).toLinearMap) := by
  right
  by_cases hΓ : H.gam = ⊥
  · -- the abelian part is nonzero
    have hP : perTan (mxLs r) (mxM b) H.t ≠ ⊥ := fun hP => hH (tan_eq_bot_of b H hΓ hP)
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
      refine block_case b hb H cmRho inr₂ (fun v => by
          simp only [inr₂_left, inr₂_right, mul_zero, Finset.sum_const_zero, zero_add])
        (fun v hv => algVec_inr hv) (l := pr₂ l) (lat_right hl) h2 ?_ ?_
      · have e : (inr₂ (pr₂ l), (0 : Fin (mxN r + mxN r) → ℂ)) = E₂ (pr₂ l, 0) := by
          rw [LinearMap.prodMap_apply, map_zero]
        rw [e]; exact hP1
      · have e : ((0 : Fin (mxN r + mxN r) → ℂ), inr₂ (etaV (fun _ => equianharmonic) (pr₂ l))) =
            E₂ (0, etaV (fun _ => equianharmonic) (pr₂ l)) := by
          rw [LinearMap.prodMap_apply, map_zero]
        rw [e]; exact hP2
    · -- the `E_i` block
      have hl₁t : pr₁ l ∈ H.t.comap inl₁ := hs l hlt hl
      have hP1 := map_left_le (Ls₂ := fun _ : Fin (mxN r) => equianharmonic)
        (Submodule.mem_map_of_mem (fst_mem cmLem hl₁t (lat_left hl)))
      have hP2 := map_left_le (Ls₂ := fun _ : Fin (mxN r) => equianharmonic)
        (Submodule.mem_map_of_mem (snd_mem cmLem hl₁t (lat_left hl)))
      refine block_case b hb H cmLem inl₁ (fun v => by
          simp only [inl₁_left, inl₁_right, mul_zero, Finset.sum_const_zero, add_zero])
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
    refine ⟨mxIota r (vecIncl w), ⟨vecIncl w, Submodule.mem_sup_left
      (Submodule.mem_sup_left (Submodule.mem_map_of_mem hwΓ)), rfl⟩, ?_, ?_⟩
    · exact ⟨hwa.1 0, fun _ => isAlgebraic_zero, fun _ => isAlgebraic_zero, hwa.2 0⟩
    · have : w.1 0 ≠ 0 ∨ w.2 0 ≠ 0 := by
        by_contra hcon; push Not at hcon
        apply hw0
        exact Prod.ext (funext fun i => by fin_cases i; exact hcon.1)
          (funext fun i => by fin_cases i; exact hcon.2)
      rcases this with h | h
      · left; simpa [psiX1_apply, mxIota, vecIncl] using h
      · right; simpa [psiX2_apply, mxIota, vecIncl] using h

end Sub

/-! ### The bridge -/

/-- **Theorem MX's hypothesis `Thm11KappaMXG` from `Theorem41VecLA`**, with the five CM inputs of
`thm11KappaMXG_of_cm` discharged. -/
theorem thm11KappaMXG_of (h : Theorem41VecLA) : MStarCopy.Thm11KappaMXG := by
  intro hg₂ hg₃ hg₂' hg₃'
  have hLs : ∀ r, ∀ j, IsAlgebraic ℚ (mxLs r j).g₂ ∧ IsAlgebraic ℚ (mxLs r j).g₃ := by
    intro r j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [mxLs, Fin.append_left]; exact ⟨hg₂, hg₃⟩
    · simp only [mxLs, Fin.append_right]; exact ⟨hg₂', hg₃'⟩
  exact thm11KappaMXG_of_cm h (liftAlg_mx hg₂ hg₃ hg₂' hg₃') perTanRat_mx
    (fun r b hb => ⟨lamVSub (mxLs r) (mxM b) (hLs r) (mxM_alg b hb), fun _ hx => hx,
      lamGen_mem b hb⟩)
    (fun _ b _ => perXG_le b) (fun _ b hb H hH => sub_mx b hb H hH) hg₂ hg₃ hg₂' hg₃'

end LSG.W88.V5d
