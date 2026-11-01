/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopy
import LSG.W88.K11Lin
import LSG.Weierstrass.Dictionary

/-!
# Periods, algebraic points and `ℚ̄`-rational subspaces of `G_m^{d₁} × E` (for `Thm11Kappa`)

All in the coordinates `T d₁ = ℂ^{d₁} × ℂ` of `lean_mstar` (`MStarCopy`).
* `PhiL`: `(q, p₁, p₂) ↦ (2πi q, p₁ω₁ + p₂ω₂)`, injective, with range `OmegaQ L d₁`; so
  `dim_ℚ Ω_ℚ = d₁ + 2`, and `Ω_ℚ ∩ (tangentSub ℒ b)` is the image of `ℒ × (ℚ² or 0)`
  (`omegaQ_inf_tangent`), of dimension `dim ℒ + 2b`.
* `goodSub`: the logarithms of algebraic points form an additive subgroup (via the group law of
  `E`, `LSG.Weierstrass.ratPoints`); `GoodPt` is the weaker property used by `LSG.W88.Lam`.
* `isAlg_exp_ratComb`: `e^{Σ cⱼ vⱼ}` is algebraic for rational `cⱼ` if every `e^{vⱼ}` is.
* `ratSub_inf_tangent`: `W ∩ tangentSub ℒ b` is `ℚ̄`-rational if `W` is.
-/

open Complex Module Matrix

namespace LSG.W88.K11

open MStarCopy

variable (L : PeriodPair) {d₁ : ℕ}

/-! ### The period space `Ω_ℚ` -/

/-- `(q, p₁, p₂) ↦ (2πi q, p₁ω₁ + p₂ω₂)`. -/
noncomputable def PhiL (L : PeriodPair) (d₁ : ℕ) : ((Fin d₁ → ℚ) × ℚ × ℚ) →ₗ[ℚ] T d₁ where
  toFun x := ((2 * Real.pi * I : ℂ) • castL d₁ x.1, (x.2.1 : ℂ) * L.ω₁ + (x.2.2 : ℂ) * L.ω₂)
  map_add' x y := by
    ext j
    · simp; ring
    · simp only [Prod.snd_add, Prod.fst_add, Rat.cast_add]; ring
  map_smul' c x := by
    ext j
    · simp [Rat.smul_def]; ring
    · simp [Rat.smul_def]; ring

lemma phiL_apply (x : (Fin d₁ → ℚ) × ℚ × ℚ) :
    PhiL L d₁ x = ((2 * Real.pi * I : ℂ) • castL d₁ x.1,
      (x.2.1 : ℂ) * L.ω₁ + (x.2.2 : ℂ) * L.ω₂) := rfl

lemma two_pi_I_ne_zero : (2 * Real.pi * I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, I_ne_zero]

lemma rat_indep {p₁ p₂ : ℚ} (h : (p₁ : ℂ) * L.ω₁ + (p₂ : ℂ) * L.ω₂ = 0) : p₁ = 0 ∧ p₂ = 0 := by
  have := LinearIndependent.pair_iff.mp L.indep (p₁ : ℝ) (p₂ : ℝ) (by
    simpa [Complex.real_smul] using h)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

lemma phiL_injective : Function.Injective (PhiL L d₁) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨q, p₁, p₂⟩ h
  rw [phiL_apply] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_zero, Prod.snd_zero, smul_eq_zero, two_pi_I_ne_zero, false_or] at h1 h2
  have hq : q = 0 := castL_injective d₁ (by rw [h1, map_zero])
  obtain ⟨rfl, rfl⟩ := rat_indep L h2
  simp [hq]

lemma omegaQ_eq_range : OmegaQ L d₁ = LinearMap.range (PhiL L d₁) := by
  classical
  apply le_antisymm
  · rw [OmegaQ, Submodule.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨ω, hω, rfl⟩)
    · refine ⟨(Pi.single j 1, 0, 0), ?_⟩
      rw [phiL_apply]; ext i
      · by_cases h : i = j
        · subst h; simp
        · simp [h]
      · simp
    · obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hω
      exact ⟨(0, m, n), by rw [phiL_apply]; simp⟩
  · rintro _ ⟨⟨q, p₁, p₂⟩, rfl⟩
    have hdec : ((q, p₁, p₂) : (Fin d₁ → ℚ) × ℚ × ℚ) =
        ∑ j, q j • ((Pi.single j 1 : Fin d₁ → ℚ), (0 : ℚ), (0 : ℚ)) + p₁ • (0, 1, 0) +
          p₂ • (0, 0, 1) := by
      ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hdec, map_add, map_add, map_sum]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => ?_) ?_) ?_
    · rw [map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨j, ?_⟩))
      rw [phiL_apply]; ext i
      · by_cases h : i = j
        · subst h; simp
        · simp [h]
      · simp
    · rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨L.ω₁, L.ω₁_mem_lattice,
        by rw [phiL_apply]; simp⟩))
    · rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨L.ω₂, L.ω₂_mem_lattice,
        by rw [phiL_apply]; simp⟩))

instance : FiniteDimensional ℚ (OmegaQ L d₁) := by
  rw [omegaQ_eq_range]; infer_instance

lemma finrank_omegaQ : finrank ℚ (OmegaQ L d₁) = d₁ + 2 := by
  rw [omegaQ_eq_range, LinearMap.finrank_range_of_inj (phiL_injective L)]
  simp

lemma mem_omegaQ {x : T d₁} : x ∈ OmegaQ L d₁ ↔ ∃ q p₁ p₂, x = PhiL L d₁ (q, p₁, p₂) := by
  rw [omegaQ_eq_range]
  exact ⟨fun ⟨⟨q, p₁, p₂⟩, h⟩ => ⟨q, p₁, p₂, h.symm⟩, fun ⟨q, p₁, p₂, h⟩ => ⟨_, h.symm⟩⟩

/-! ### `Ω_ℚ ∩ T_{G'}` -/

/-- `tangentSub ℒ b` as a `ℚ`-subspace. -/
noncomputable abbrev Tq (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) : Submodule ℚ (T d₁) :=
  (tangentSub ℒ b).restrictScalars ℚ

lemma tangentSub_eq (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) :
    tangentSub ℒ b = (cspan ℒ).prod (if b then ⊤ else ⊥) := rfl

lemma mem_tangentSub {ℒ : Submodule ℚ (Fin d₁ → ℚ)} {b : Bool} {x : T d₁} :
    x ∈ tangentSub ℒ b ↔ x.1 ∈ cspan ℒ ∧ (b = true ∨ x.2 = 0) := by
  rw [tangentSub_eq, Submodule.mem_prod]
  cases b <;> simp

/-- The image of `ℒ × ℚ²` (if `b`) or `ℒ` (if not) under `PhiL`. -/
noncomputable def omSub (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) : Submodule ℚ (T d₁) :=
  if b then LinearMap.range ((PhiL L d₁).comp (LinearMap.prodMap ℒ.subtype LinearMap.id))
  else LinearMap.range ((PhiL L d₁).comp ((LinearMap.inl ℚ _ (ℚ × ℚ)).comp ℒ.subtype))

lemma finrank_omSub (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) :
    finrank ℚ (omSub L ℒ b) = finrank ℚ ℒ + 2 * b.toNat := by
  cases b
  · rw [show omSub L ℒ false = LinearMap.range ((PhiL L d₁).comp
      ((LinearMap.inl ℚ _ (ℚ × ℚ)).comp ℒ.subtype)) from rfl, LinearMap.finrank_range_of_inj]
    · simp
    exact (phiL_injective L).comp (LinearMap.inl_injective.comp Subtype.val_injective)
  · rw [show omSub L ℒ true = LinearMap.range ((PhiL L d₁).comp
      (LinearMap.prodMap ℒ.subtype LinearMap.id)) from rfl, LinearMap.finrank_range_of_inj]
    · simp
    · refine (phiL_injective L).comp ?_
      rintro ⟨a, p⟩ ⟨a', p'⟩ h
      simp only [LinearMap.prodMap_apply, Submodule.subtype_apply, LinearMap.id_coe, id_eq,
        Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) h.2

lemma omegaQ_inf_tangent (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) :
    OmegaQ L d₁ ⊓ Tq ℒ b = omSub L ℒ b := by
  apply le_antisymm
  · rintro x ⟨hxΩ, hxT⟩
    obtain ⟨q, p₁, p₂, rfl⟩ := (mem_omegaQ L).mp hxΩ
    replace hxT : PhiL L d₁ (q, p₁, p₂) ∈ tangentSub ℒ b := hxT
    rw [mem_tangentSub, phiL_apply] at hxT
    obtain ⟨h1, h2⟩ := hxT
    have hq : q ∈ ℒ := by
      apply mem_of_castL_mem_cspan
      have := Submodule.smul_mem _ (2 * Real.pi * I : ℂ)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul] at this
    cases b
    · obtain ⟨rfl, rfl⟩ := rat_indep L (h2.resolve_left (by simp))
      exact ⟨⟨q, hq⟩, rfl⟩
    · exact ⟨(⟨q, hq⟩, p₁, p₂), rfl⟩
  · intro x hx
    have key : ∀ q p₁ p₂, q ∈ ℒ → (b = true ∨ (p₁ = 0 ∧ p₂ = 0)) →
        PhiL L d₁ (q, p₁, p₂) ∈ OmegaQ L d₁ ⊓ Tq ℒ b := by
      intro q p₁ p₂ hq hb
      refine ⟨(mem_omegaQ L).mpr ⟨q, p₁, p₂, rfl⟩, ?_⟩
      change PhiL L d₁ (q, p₁, p₂) ∈ tangentSub ℒ b
      rw [mem_tangentSub, phiL_apply]
      refine ⟨Submodule.smul_mem _ _ (castL_mem_cspan hq), ?_⟩
      rcases hb with hb | ⟨rfl, rfl⟩
      · exact Or.inl hb
      · right; simp
    cases b
    · obtain ⟨⟨q, hq⟩, rfl⟩ := hx
      exact key q 0 0 hq (Or.inr ⟨rfl, rfl⟩)
    · obtain ⟨⟨⟨q, hq⟩, p₁, p₂⟩, rfl⟩ := hx
      exact key q p₁ p₂ hq (Or.inl rfl)

lemma finrank_omegaQ_inf_tangent (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) :
    finrank ℚ ↥(OmegaQ L d₁ ⊓ Tq ℒ b) = finrank ℚ ℒ + 2 * b.toNat := by
  rw [omegaQ_inf_tangent, finrank_omSub]

/-- In `Ω_ℚ ∩ T_{G'}` with `b = true`, the first coordinates span a space of dimension `≤ dim ℒ`. -/
lemma finrank_map_fst_le (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) :
    finrank ℚ ↥((OmegaQ L d₁ ⊓ Tq ℒ b).map (LinearMap.fst ℚ (Fin d₁ → ℂ) ℂ)) ≤ finrank ℚ ℒ := by
  let g : ℒ →ₗ[ℚ] (Fin d₁ → ℂ) :=
    ((2 * Real.pi * I : ℂ) • (castL d₁).restrictScalars ℚ |>.comp ℒ.subtype)
  have hle : (OmegaQ L d₁ ⊓ Tq ℒ b).map (LinearMap.fst ℚ (Fin d₁ → ℂ) ℂ) ≤ LinearMap.range g := by
    rintro _ ⟨x, ⟨hxΩ, hxT⟩, rfl⟩
    obtain ⟨q, p₁, p₂, rfl⟩ := (mem_omegaQ L).mp hxΩ
    replace hxT : PhiL L d₁ (q, p₁, p₂) ∈ tangentSub ℒ b := hxT
    rw [mem_tangentSub, phiL_apply] at hxT
    have hq : q ∈ ℒ := by
      apply mem_of_castL_mem_cspan
      have := Submodule.smul_mem _ (2 * Real.pi * I : ℂ)⁻¹ hxT.1
      rwa [smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul] at this
    exact ⟨⟨q, hq⟩, by simp [g, phiL_apply]⟩
  exact (Submodule.finrank_mono hle).trans (LinearMap.finrank_range_le g)

/-! ### Algebraic numbers and exponentials -/

/-- The algebraic numbers, as a subfield of `ℂ`. -/
noncomputable abbrev Kq : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

lemma mem_Kq {x : ℂ} : x ∈ Kq ↔ IsAlgebraic ℚ x := mem_algebraicClosure_iff

lemma isAlg_exp_ratMul (q : ℚ) {u : ℂ} (hu : IsAlgebraic ℚ (exp u)) :
    IsAlgebraic ℚ (exp ((q : ℂ) * u)) := by
  refine IsAlgebraic.of_pow q.den_pos ?_
  rw [← Complex.exp_nat_mul, ← mul_assoc]
  have : ((q.den : ℕ) : ℂ) * (q : ℂ) = (q.num : ℂ) := by
    have := Rat.den_mul_eq_num q
    exact_mod_cast this
  rw [this, Complex.exp_int_mul, ← mem_Kq]
  exact Kq.zpow_mem (mem_Kq.mpr hu) _

lemma isAlg_exp_ratComb {n : ℕ} (c : Fin n → ℚ) (v : Fin n → ℂ)
    (hv : ∀ j, IsAlgebraic ℚ (exp (v j))) : IsAlgebraic ℚ (exp (∑ j, (c j : ℂ) * v j)) := by
  rw [Complex.exp_sum, ← mem_Kq]
  exact Kq.prod_mem fun j _ => mem_Kq.mpr (isAlg_exp_ratMul (c j) (hv j))

lemma isAlg_ratComb {n : ℕ} (c : Fin n → ℚ) (v : Fin n → ℂ) (hv : ∀ j, IsAlgebraic ℚ (v j)) :
    IsAlgebraic ℚ (∑ j, (c j : ℂ) * v j) := by
  rw [← mem_Kq]
  exact Kq.sum_mem fun j _ => Kq.mul_mem (SubfieldClass.ratCast_mem Kq _) (mem_Kq.mpr (hv j))

/-! ### Logarithms of algebraic points -/

/-- The property of `y ∈ T d₁` used by `LSG.W88.Lam`: `e^{y_j}` algebraic, `y₂ ∈ Λ` or `℘(y₂)`
algebraic. -/
def GoodPt (L : PeriodPair) (y : T d₁) : Prop :=
  (∀ j, IsAlgebraic ℚ (Complex.exp (y.1 j))) ∧
    (y.2 ∈ L.lattice ∨ IsAlgebraic ℚ (L.weierstrassP y.2))

section Good

variable (hg₂ : IsAlgebraic ℚ L.g₂)
include hg₂

/-- The logarithms of algebraic points of `G_m^{d₁} × E`, an additive subgroup. -/
noncomputable def goodSub (d₁ : ℕ) : AddSubgroup (T d₁) where
  carrier := {y | (∀ j, IsAlgebraic ℚ (Complex.exp (y.1 j))) ∧
    LSG.Weierstrass.expE L y.2 ∈ LSG.Weierstrass.ratPoints L Kq (mem_Kq.mpr hg₂)}
  add_mem' {a b} ha hb := by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, Complex.exp_add, ← mem_Kq]
      exact Kq.mul_mem (mem_Kq.mpr (ha.1 j)) (mem_Kq.mpr (hb.1 j))
    · simp only [Prod.snd_add, LSG.Weierstrass.expE_add]
      exact AddSubgroup.add_mem _ ha.2 hb.2
  zero_mem' := by
    refine ⟨fun j => by simpa using isAlgebraic_one, ?_⟩
    simp only [Prod.snd_zero, LSG.Weierstrass.expE_zero]
    exact AddSubgroup.zero_mem _
  neg_mem' {a} ha := by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [Prod.fst_neg, Pi.neg_apply, Complex.exp_neg, ← mem_Kq]
      exact Kq.inv_mem (mem_Kq.mpr (ha.1 j))
    · simp only [Prod.snd_neg, LSG.Weierstrass.expE_neg]
      exact AddSubgroup.neg_mem _ ha.2

lemma mem_goodSub_of_expAlg {y : T d₁} (hy : ExpAlg L y) : y ∈ goodSub L hg₂ d₁ := by
  refine ⟨hy.1, ?_⟩
  rcases hy.2 with h | ⟨hx, hy'⟩
  · rw [LSG.Weierstrass.expE_of_mem L h]; exact AddSubgroup.zero_mem _
  · by_cases hz : y.2 ∈ L.lattice
    · rw [LSG.Weierstrass.expE_of_mem L hz]; exact AddSubgroup.zero_mem _
    intro x y' h hP
    rw [LSG.Weierstrass.expE_of_notMem L hz] at hP
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    exact ⟨mem_Kq.mpr hx, Kq.div_mem (mem_Kq.mpr hy') (by simp)⟩

lemma goodPt_of_mem {y : T d₁} (hy : y ∈ goodSub L hg₂ d₁) : GoodPt L y := by
  refine ⟨hy.1, ?_⟩
  by_cases hz : y.2 ∈ L.lattice
  · exact Or.inl hz
  · right
    have h := hy.2
    exact mem_Kq.mp (h _ _ _ (LSG.Weierstrass.expE_of_notMem L hz)).1

end Good

/-! ### `ℚ̄`-rational subspaces -/

/-- `W` is spanned by vectors with algebraic coordinates (`= (gmE L d₁).Rational W`). -/
def RatSub (W : Submodule ℂ (T d₁)) : Prop :=
  ∃ S : Set (T d₁), (∀ v ∈ S, AlgVec v) ∧ W = Submodule.span ℂ S

/-- A linear form taking algebraic values on algebraic vectors. -/
def AlgForm (f : T d₁ →ₗ[ℂ] ℂ) : Prop := ∀ v, AlgVec v → IsAlgebraic ℚ (f v)

lemma algVec_sub_smul {v w : T d₁} (hv : AlgVec v) (hw : AlgVec w) {c : ℂ}
    (hc : IsAlgebraic ℚ c) : AlgVec (v - c • w) := by
  refine ⟨fun j => ?_, ?_⟩
  · simp only [Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← mem_Kq]
    exact Kq.sub_mem (mem_Kq.mpr (hv.1 j)) (Kq.mul_mem (mem_Kq.mpr hc) (mem_Kq.mpr (hw.1 j)))
  · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul, ← mem_Kq]
    exact Kq.sub_mem (mem_Kq.mpr hv.2) (Kq.mul_mem (mem_Kq.mpr hc) (mem_Kq.mpr hw.2))

lemma ratSub_inf_ker {W : Submodule ℂ (T d₁)} (hW : RatSub W) {f : T d₁ →ₗ[ℂ] ℂ}
    (hf : AlgForm f) : RatSub (W ⊓ LinearMap.ker f) := by
  classical
  obtain ⟨S, hSalg, rfl⟩ := hW
  by_cases h : ∀ s ∈ S, f s = 0
  · refine ⟨S, hSalg, ?_⟩
    refine inf_eq_left.mpr (Submodule.span_le.mpr fun s hs => ?_)
    exact LinearMap.mem_ker.mpr (h s hs)
  push Not at h
  obtain ⟨s₀, hs₀, hfs₀⟩ := h
  let g : T d₁ → T d₁ := fun s => s - (f s / f s₀) • s₀
  refine ⟨g '' S, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine algVec_sub_smul (hSalg s hs) (hSalg s₀ hs₀) ?_
    rw [← mem_Kq]
    exact Kq.div_mem (mem_Kq.mpr (hf s (hSalg s hs))) (mem_Kq.mpr (hf s₀ (hSalg s₀ hs₀)))
  apply le_antisymm
  · rintro w ⟨hw, hwk⟩
    have key : ∀ w ∈ Submodule.span ℂ S, g w ∈ Submodule.span ℂ (g '' S) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp [g]
      | add x y _ _ hx hy =>
        have : g (x + y) = g x + g y := by
          simp only [g, map_add, add_div, add_smul]; abel
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        have : g (c • x) = c • g x := by
          simp only [g, map_smul, smul_eq_mul, smul_sub, smul_smul, mul_div_assoc]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have := key w hw
    rwa [show g w = w by simp [g, LinearMap.mem_ker.mp hwk]] at this
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hs)
      (Submodule.smul_mem _ _ (Submodule.subset_span hs₀)), ?_⟩
    change g s ∈ LinearMap.ker f
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfs₀, sub_self]

lemma ratSub_inf_finsetInf {W : Submodule ℂ (T d₁)} (hW : RatSub W) {ι : Type*}
    (f : ι → T d₁ →ₗ[ℂ] ℂ) (hf : ∀ i, AlgForm (f i)) (s : Finset ι) :
    RatSub (W ⊓ s.inf fun i => LinearMap.ker (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hW
  | insert a s _ ih =>
    rw [Finset.inf_insert, inf_comm (LinearMap.ker (f a)), ← inf_assoc]
    exact ratSub_inf_ker ih (hf a)

lemma ratSub_inf_tangent {W : Submodule ℂ (T d₁)} (hW : RatSub W)
    (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) : RatSub (W ⊓ tangentSub ℒ b) := by
  classical
  obtain ⟨C, D, hDC, hC⟩ := exists_frame (annQ ℒ)
  have hcs : cspan ℒ = LinearMap.ker (cm C)ᵀ.mulVecLin := by
    rw [cspan_eq_annC, annC_eq_ker hC]
  let f : Fin (finrank ℚ (annQ ℒ)) → T d₁ →ₗ[ℂ] ℂ := fun i =>
    (LinearMap.proj i).comp ((cm C)ᵀ.mulVecLin.comp (LinearMap.fst ℂ (Fin d₁ → ℂ) ℂ))
  have hf : ∀ i, AlgForm (f i) := by
    intro i v hv
    have : f i v = ∑ j, ((C j i : ℚ) : ℂ) * v.1 j := by
      simp [f, cm, Matrix.vecMul, dotProduct, mul_comm]
    rw [this]; exact isAlg_ratComb _ _ hv.1
  have hg : AlgForm (LinearMap.snd ℂ (Fin d₁ → ℂ) ℂ) := fun v hv => hv.2
  have h1 := ratSub_inf_finsetInf hW f hf Finset.univ
  have hcut : ∀ x : T d₁, x ∈ (Finset.univ.inf fun i => LinearMap.ker (f i)) ↔ x.1 ∈ cspan ℒ := by
    intro x
    rw [Submodule.mem_finsetInf, hcs, LinearMap.mem_ker]
    simp only [Finset.mem_univ, true_implies, LinearMap.mem_ker]
    constructor
    · intro h; ext i; exact h i
    · intro h i; simpa [f] using congrFun h i
  cases b
  · have h2 := ratSub_inf_ker h1 hg
    convert h2 using 1
    ext x
    simp only [Submodule.mem_inf, mem_tangentSub, hcut, LinearMap.mem_ker, LinearMap.snd_apply]
    simp [and_assoc]
  · convert h1 using 1
    ext x
    simp only [Submodule.mem_inf, mem_tangentSub, hcut]
    simp

end LSG.W88.K11
