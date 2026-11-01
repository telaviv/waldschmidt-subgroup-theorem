/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dMGnIso

/-!
# `gmMGn`, `gmMGnK`: generators, algebraicity, and the subgroup tangent spaces under `ι = mgIota`

* `mg_alg`: `ι⁻¹` maps algebraic vectors (`algF algQn`) to algebraic vectors;
* `perV_le_lamV`: periods are logarithms; `qv_single_mem`, `perQn_mem`: the period generators
  `perQn` are periods of the class-`𝒞` group (`η((m + nα)ω) = (m + nᾱ) η₀`); `tor_mem_lam`,
  `tor_mem_per`: toric generators;
* `iota_tan`: `ι(T_H) = torL(U^⊥) × (Γ-part + B̃-part)`, `torus_eq`: the toric part is `torSub (annQ
  U)`;
* `gam_ne`, `abel_ne`, `torus_ne`, `dot_ne`: nonzero parts produce vectors on which the linear forms
  of the models do not vanish (`abel_ne`: `Σ_k b_k ā_k ≠ 0` for `0 ≠ a ∈ ℤ[α]^r`, by
  `ℚ`-independence of `θ`).
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy

variable {r : ℕ} (L : CMLattice) (b : Fin r → ℂ) (hb : IsAdaptedFieldBasis L.α b)

/-- Periods are logarithms of algebraic points. -/
lemma perV_le_lamV {d0 d1 m r' : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r') (Fin m) ℂ}
    {x : TanV d0 d1 m r'} (hx : x ∈ PerV Ls M) : x ∈ LamV Ls M := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  refine ⟨fun i => by rw [h1]; exact isAlgebraic_zero, fun i => ?_, fun j => Or.inl (h3 j), ?_⟩
  · obtain ⟨k, hk⟩ := h2 i
    rw [hk, show 2 * (Real.pi : ℂ) * I * k = k * (2 * Real.pi * I) by ring,
      Complex.exp_int_mul_two_pi_mul_I]
    exact isAlgebraic_one
  · have : zetaV Ls x.2.2.1 = etaV Ls x.2.2.1 :=
      funext fun j => zeta_of_mem_lattice _ (h3 j)
    rw [h4, this, sub_self]
    exact fun _ => isAlgebraic_zero

include hb in
/-- `ι⁻¹` preserves algebraic vectors. -/
lemma mg_alg (v : TF (Fin r × Fin 2) (Qn L b)) (hv : algF (algQn L b) v) :
    AlgVecV ((mgIota L b hb).symm v) := by
  rw [mgIota_symm_apply]
  refine ⟨fun i => i.elim0, fun i => ?_, fun k => ?_, fun _ => hv.2.2.2⟩
  · change IsAlgebraic ℚ (Sum.elim v.1.1 v.1.2 (tE r i))
    rcases tE r i with j | j
    · exact hv.1 j
    · exact hv.2.1 j
  · obtain ⟨w, hw, hwq⟩ := hv.2.2.1
    change IsAlgebraic ℚ (qPi L b hb v.2.1 k)
    rw [← hwq, qPi_mk, piB_apply]
    exact (hw _).add ((isAlgebraic_conj (CMLat.isAlgebraic_α L)).mul (hw _))

lemma sum_single_fin (f : ℂ → ℂ) (hf : f 0 = 0) (k₀ : Fin r) (z : ℂ) :
    ∑ k, b k * f ((Pi.single k₀ z : Fin r → ℂ) k) = b k₀ * f z := by
  rw [Finset.sum_eq_single k₀]
  · simp
  · intro k _ hk; simp [hk, hf]
  · simp

/-- `γ_j = 1` or `ᾱ`. -/
lemma gam_mem_lattice (hκ : KappaOneZero L) (j : Fin r × Fin 2) {c : ℂ} (hc : c ∈ L.pp.lattice) :
    (if j.2 = 0 then 1 else starRingEnd ℂ L.α) * c ∈ L.pp.lattice := by
  have hd := CMLat.cmD L hκ
  split_ifs
  · simpa using hc
  · rw [hd.conj_eq]; exact hd.unit.inv_mul_mem _ hc

include hb in
/-- The generator `([c e_j], θ_j conj(c/ω) η₀)` is a period of the class-`𝒞` group. -/
lemma qv_single_mem (hκ : KappaOneZero L) (j : Fin r × Fin 2) {c : ℂ} (hc : c ∈ L.pp.lattice) :
    (mgIota L b hb).symm (qv ((Submodule.Quotient.mk (Pi.single j c) :
      (Fin r × Fin 2 → ℂ) ⧸ Wphi L b),
      theta L.α b j * (starRingEnd ℂ (c / L.ω) * L.η₀))) ∈
      PerV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b) := by
  have hd := CMLat.cmD L hκ
  have hγ := gam_mem_lattice L hκ j hc
  rw [mgIota_symm_apply]
  simp only [qv, qPi_mk, piB_single]
  refine ⟨rfl, fun i => ⟨0, ?_⟩, fun k => ?_, funext fun i => ?_⟩
  · change Sum.elim (0 : Fin r × Fin 2 → ℂ) 0 (tE r i) = _
    rcases tE r i with _ | _ <;> simp
  · by_cases hk : k = j.1
    · subst hk; simpa using hγ
    · simp [hk, L.pp.lattice.zero_mem]
  · rw [Subsingleton.elim i 0, mgM_mulVec]
    simp only [etaV]
    rw [sum_single_fin b (eta L.pp) (eta_zero _), hd.eta_eq_conj hγ, CMLat.eta_one_eq L hκ,
      theta_eq, L.hω₁]
    simp only [map_mul, map_div₀]
    ring

include hb in
/-- **The period generators `perQn` are periods.** -/
lemma perQn_mem (hκ : KappaOneZero L) {q : Qn L b} (hq : q ∈ perQn L b) :
    (mgIota L b hb).symm (qv q) ∈ PerV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b) := by
  have hω : L.ω ≠ 0 := by rw [← L.hω₁]; exact ω₁_ne_zero _
  rcases hq with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hc : L.ω ∈ L.pp.lattice := L.hω₁ ▸ L.pp.ω₁_mem_lattice
    have := qv_single_mem L b hb hκ j hc
    rwa [div_self hω, map_one, one_mul] at this
  · have hc : L.α * L.ω ∈ L.pp.lattice := L.hω₂ ▸ L.pp.ω₂_mem_lattice
    have := qv_single_mem L b hb hκ j hc
    rwa [mul_div_cancel_right₀ _ hω] at this

lemma torL_symm_single1 (j : Fin r × Fin 2) (x : ℂ) (i : Fin (2 * nI r)) :
    (torL r).symm ((Pi.single j x, 0) : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ)) i = 0 ∨
      (torL r).symm ((Pi.single j x, 0) : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ)) i = x := by
  rw [torL_symm_apply]
  rcases tE r i with j' | j'
  · by_cases h : j' = j
    · subst h; simp
    · simp [h]
  · simp

lemma torL_symm_single2 (j : Fin r × Fin 2) (x : ℂ) (i : Fin (2 * nI r)) :
    (torL r).symm ((0, Pi.single j x) : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ)) i = 0 ∨
      (torL r).symm ((0, Pi.single j x) : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ)) i = x := by
  rw [torL_symm_apply]
  rcases tE r i with j' | j'
  · simp
  · by_cases h : j' = j
    · subst h; simp
    · simp [h]

/-- The shape of `ι⁻¹` of a toric generator. -/
lemma symm_tor (p : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ)) :
    (mgIota L b hb).symm ((p, 0) : TF (Fin r × Fin 2) (Qn L b)) =
      (0, (torL r).symm p, 0, 0) := by
  rw [mgIota_symm_apply]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext (map_zero _) rfl))

/-- Toric generators are logarithms. -/
lemma tor_mem_lam {p : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ)} {x : ℂ}
    (hx : IsAlgebraic ℚ (Complex.exp x)) (hp : ∀ i, (torL r).symm p i = 0 ∨ (torL r).symm p i = x) :
    (mgIota L b hb).symm ((p, 0) : TF (Fin r × Fin 2) (Qn L b)) ∈
      LamV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b) := by
  rw [symm_tor]
  refine ⟨fun i => i.elim0, fun i => ?_, fun _ => Or.inl (zero_mem _), fun _ => ?_⟩
  · change IsAlgebraic ℚ (Complex.exp ((torL r).symm p i))
    rcases hp i with h | h <;> rw [h]
    · rw [Complex.exp_zero]; exact isAlgebraic_one
    · exact hx
  · have : zetaV (mgLs L r) (0 : Fin r → ℂ) = 0 := funext fun _ => zeta_zero _
    simp only [this, Matrix.mulVec_zero, sub_zero]
    exact isAlgebraic_zero

/-- Toric period generators are periods. -/
lemma tor_mem_per {p : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ)}
    (hp : ∀ i, (torL r).symm p i = 0 ∨ (torL r).symm p i = 2 * Real.pi * I) :
    (mgIota L b hb).symm ((p, 0) : TF (Fin r × Fin 2) (Qn L b)) ∈
      PerV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b) := by
  rw [symm_tor]
  refine ⟨rfl, fun i => ?_, fun _ => zero_mem _, ?_⟩
  · change ∃ k : ℤ, (torL r).symm p i = _
    rcases hp i with h | h
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨1, by rw [h]; simp⟩
  · have : etaV (mgLs L r) (0 : Fin r → ℂ) = 0 := funext fun _ => eta_zero _
    simp only [this, Matrix.mulVec_zero]

/-! ### Subgroup tangent spaces -/

/-- `(a, s) ↦ (0, s)`: the vector part. -/
noncomputable def gG : (Fin 0 → ℂ) × (Fin 1 → ℂ) →ₗ[ℂ] Qn L b :=
  LinearMap.inr ℂ _ ℂ ∘ₗ (LinearMap.proj 0 ∘ₗ LinearMap.snd ℂ _ _)

/-- `(z, s) ↦ ([incl z], s)`: the `(E^r)^♮` part. -/
noncomputable def gA : (Fin r → ℂ) × (Fin 1 → ℂ) →ₗ[ℂ] Qn L b :=
  LinearMap.prod ((Wphi L b).mkQ ∘ₗ inclB ∘ₗ LinearMap.fst ℂ _ _)
    (LinearMap.proj 0 ∘ₗ LinearMap.snd ℂ _ _)

/-- **`ι(T_H) = torL(U^⊥) × (Γ-part + B̃-part)`.** -/
theorem iota_tan (H : SubgroupDataV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b)) :
    H.tan.map (mgIota L b hb).toLinearMap = ((torusLie H.U).map (torL r).toLinearMap).prod
      (H.gam.map (gG L b) ⊔ (perTan (mgLs L r) (mgM b) H.t).map (gA L b)) := by
  have hq0 : (Submodule.Quotient.mk (inclB (0 : Fin r → ℂ)) :
      (Fin r × Fin 2 → ℂ) ⧸ Wphi L b) = 0 := by
    rw [map_zero]; rfl
  have e1 : (mgIota L b hb).toLinearMap ∘ₗ vecIncl = LinearMap.inr ℂ _ _ ∘ₗ gG L b := by
    refine LinearMap.ext fun x => Prod.ext ?_ (Prod.ext ?_ rfl)
    · exact (show (torL r) 0 = 0 from map_zero _)
    · exact hq0
  have e2 : (mgIota L b hb).toLinearMap ∘ₗ torIncl =
      LinearMap.inl ℂ _ _ ∘ₗ (torL r).toLinearMap := by
    refine LinearMap.ext fun x => Prod.ext rfl (Prod.ext ?_ rfl)
    exact hq0
  have e3 : (mgIota L b hb).toLinearMap ∘ₗ g2Incl = LinearMap.inr ℂ _ _ ∘ₗ gA L b := by
    refine LinearMap.ext fun x => Prod.ext ?_ rfl
    exact (show (torL r) 0 = 0 from map_zero _)
  rw [SubgroupDataV.tan, Submodule.map_sup, Submodule.map_sup, ← Submodule.map_comp,
    ← Submodule.map_comp, ← Submodule.map_comp, e1, e2, e3, Submodule.map_comp, Submodule.map_comp,
    Submodule.map_comp, Submodule.map_inl, Submodule.map_inr, Submodule.map_inr,
    Submodule.prod_sup_prod, Submodule.prod_sup_prod]
  simp only [bot_sup_eq, sup_bot_eq]

/-- The toric part is `torSub` of the rational annihilator. -/
lemma torus_eq (U : Submodule ℚ (Fin (2 * nI r) → ℚ)) :
    (torusLie U).map (torL r).toLinearMap = torSub ((K11.annQ U).map (torLQ r)) := by
  have h1 : torusLie U = K11.annC U := rfl
  rw [h1, K11.annC_eq_cspan, K11.cspan_eq, Submodule.map_span, torSub, Submodule.map_coe,
    Set.image_image, Set.image_image]
  rfl

/-- A nonzero vector part contains `(0, s)`, `s ≠ 0` algebraic. -/
lemma gam_ne (H : SubgroupDataV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b)) (hΓ : H.gam ≠ ⊥) :
    ∃ s : ℂ, s ≠ 0 ∧ IsAlgebraic ℚ s ∧
      ((0 : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), s) ∈ H.gam.map (gG L b) := by
  obtain ⟨w, hwΓ, hwa, hw0⟩ : ∃ w ∈ H.gam, AlgPair w ∧ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hΓ
    rw [H.gam_rat, Submodule.span_eq_bot]
    exact fun w hw => hcon w hw.1 hw.2
  refine ⟨w.2 0, fun h => hw0 (Prod.ext (funext fun i => i.elim0) (funext fun i => ?_)), hwa.2 0,
    ⟨w, hwΓ, rfl⟩⟩
  rw [Subsingleton.elim i 0, h]; rfl

include hb in
/-- **A nonzero abelian part gives `(0, c)`, `c = Σ_k b_k ā_k ≠ 0` algebraic.** -/
lemma abel_ne (hκ : KappaOneZero L)
    (H : SubgroupDataV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b)) (ht : H.t ≠ ⊥) :
    ∃ c : ℂ, c ≠ 0 ∧ IsAlgebraic ℚ c ∧
      ((0 : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), c) ∈ (perTan (mgLs L r) (mgM b) H.t).map (gA L b) := by
  have hd := CMLat.cmD L hκ
  obtain ⟨l, ⟨hlt, hl⟩, hl0⟩ : ∃ l ∈ {z | z ∈ H.t ∧ ∀ j, z j ∈ (mgLs L r j).lattice}, l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply ht
    rw [← span_lat_eq H.t_ab, Submodule.span_eq_bot]
    exact hcon
  set a : Fin r → ℂ := fun k => l k / L.pp.ω₁
  set ac : Fin r → ℂ := fun k => starRingEnd ℂ (a k)
  have hη := hd.eta_one_ne
  have hac : ((0 : Fin r → ℂ), ac) ∈ perTanId (mgLs L r) H.t := by
    have h := Submodule.smul_mem _ (eta L.pp L.pp.ω₁)⁻¹ (snd_mem hd hlt hl)
    have e : ac = (eta L.pp L.pp.ω₁)⁻¹ • etaV (fun _ => L.pp) l := funext fun k => by
      simp only [ac, a, Pi.smul_apply, smul_eq_mul, etaV_eq hd hl k]
      field_simp
    rw [e]; simpa using h
  have hmem : ((0 : Fin r → ℂ), (mgM b).mulVec ac) ∈ perTan (mgLs L r) (mgM b) H.t :=
    ⟨_, hac, by simp⟩
  refine ⟨∑ k, b k * ac k, ?_, ?_, ⟨_, hmem, ?_⟩⟩
  · intro h0
    choose m n hmn using fun k => hd.div_eq (hl k)
    let co : Fin r × Fin 2 → ℚ := fun j =>
      if j.2 = 0 then (m j.1 : ℚ) + n j.1 * L.q else -(n j.1 : ℚ)
    have hsum : ∑ j, co j • theta L.α b j = 0 := by
      rw [← h0, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Fin.sum_univ_two, co, theta, ac, a, hmn k, Rat.smul_def, map_add, map_mul,
        map_intCast, CMLat.conj_α]
      simp; ring
    have h0' := Fintype.linearIndependent_iff.mp hb.indep co hsum
    apply hl0
    funext k
    have hn : n k = 0 := by
      have := h0' (k, 1); simp only [co] at this
      exact_mod_cast neg_eq_zero.mp (by simpa using this)
    have hm : m k = 0 := by
      have := h0' (k, 0); simp only [co, hn] at this; exact_mod_cast (by simpa using this)
    have : l k / L.pp.ω₁ = 0 := by rw [hmn k, hm, hn]; simp
    rwa [div_eq_zero_iff, or_iff_left (ω₁_ne_zero _)] at this
  · exact mem_Qbar.mp (Qbar.sum_mem fun k _ => mem_Qbar.mpr
      ((hb.alg k).mul (isAlgebraic_conj (hd.isAlgebraic_div (hl k)))))
  · refine Prod.ext ?_ rfl
    change Submodule.Quotient.mk (inclB (0 : Fin r → ℂ)) = 0
    rw [map_zero]; rfl

/-- A nonzero toric part contains a nonzero rational vector. -/
lemma torus_ne (U : Submodule ℚ (Fin (2 * nI r) → ℚ)) (hT : torusLie U ≠ ⊥) :
    ∃ q : Fin (2 * nI r) → ℚ, q ≠ 0 ∧ K11.castL _ q ∈ torusLie U := by
  by_contra hcon
  push Not at hcon
  apply hT
  have h1 : torusLie U = K11.annC U := rfl
  have hmem : ∀ q ∈ K11.annQ U, K11.castL _ q ∈ torusLie U := fun q hq => by
    rw [h1, K11.annC_eq_cspan]; exact K11.castL_mem_cspan hq
  rw [h1, K11.annC_eq_cspan, K11.cspan_eq, Submodule.span_eq_bot]
  rintro _ ⟨q, hq, rfl⟩
  by_cases h0 : q = 0
  · rw [h0, map_zero]
  · exact absurd (hmem q hq) (hcon q h0)

include hb in
/-- `Ψ''` does not vanish on a nonzero rational toric vector. -/
lemma dot_ne {q : Fin (2 * nI r) → ℚ} (hq : q ≠ 0) :
    dotL (theta L.α b) (torL r (K11.castL _ q)).1 ≠ 0 ∨
      dotL (theta L.α b) (torL r (K11.castL _ q)).2 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hq
  have key : ∀ x : Fin r × Fin 2 → ℚ, dotL (theta L.α b) (fun j => (x j : ℂ)) = 0 → x = 0 := by
    intro x hx
    funext j
    refine Fintype.linearIndependent_iff.mp hb.indep x ?_ j
    rw [← hx]
    simp only [dotL, LinearMap.coe_mk, AddHom.coe_mk, Rat.smul_def]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h1 := key (fun j => q ((tE r).symm (Sum.inl j))) hcon.1
  have h2 := key (fun j => q ((tE r).symm (Sum.inr j))) hcon.2
  funext i
  rcases h : tE r i with j | j
  · have := congrFun h1 j
    simp only [← h, Equiv.symm_apply_apply] at this
    exact this
  · have := congrFun h2 j
    simp only [← h, Equiv.symm_apply_apply] at this
    exact this

end LSG.W88.V5d
