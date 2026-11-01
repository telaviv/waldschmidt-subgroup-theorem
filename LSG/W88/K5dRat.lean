/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.K5dModel
import LSG.CM.Coord

/-!
# `ℚ̄`-rationality of the tangent spaces `T_H` (for the §5d deduction)

* `ratT_inf_tan`: if every abelian tangent space of `E₁ × ⋯ × E_m` is `ℚ̄`-rational, then `W ∩ T_H`
  is `ℚ̄`-rational for every `ℚ̄`-rational `W` and every `SubgroupData H` (`T_H = h₀ × U^⊥ × t`).
* `abTan_rat_const`: for a power `E^r` of one curve, abelian tangent spaces are `ℚ̄`-rational:
  in a chart, the coordinates `x` of the lift of a basis vector satisfy `n ω₁ x, n' ω₂ x ∈ Λ`, hence
  the quadratic equation `n n' x² − (a n' + d n) x − (b c − a d) = 0` over `ℚ`.
-/

open Complex Module

namespace LSG.W88.K5d

variable {d0 d1 m : ℕ}

/-- Algebraic vectors of `Tan d₀ d₁ m`. -/
def algT (v : Tan d0 d1 m) : Prop := AlgVec v.1 ∧ AlgVec v.2.1 ∧ AlgVec v.2.2

/-- `W` is spanned by algebraic vectors. -/
def RatT (W : Submodule ℂ (Tan d0 d1 m)) : Prop :=
  ∃ S : Set (Tan d0 d1 m), (∀ v ∈ S, algT v) ∧ W = Submodule.span ℂ S

lemma ratT_iff (W : Submodule ℂ (Tan d0 d1 m)) : RatT W ↔ RationalOverQbarTan W := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    apply le_antisymm
    · refine Submodule.span_mono fun v hv => ⟨Submodule.subset_span hv, hS v hv⟩
    · exact Submodule.span_le.mpr fun _ hw => hw.1
  · intro h; exact ⟨_, fun v hv => hv.2, h⟩

/-- A linear form taking algebraic values on algebraic vectors. -/
def AlgFormT (f : Tan d0 d1 m →ₗ[ℂ] ℂ) : Prop := ∀ v, algT v → IsAlgebraic ℚ (f v)

lemma algVec_sub_smul' {n : ℕ} {v w : Fin n → ℂ} (hv : AlgVec v) (hw : AlgVec w) {c : ℂ}
    (hc : IsAlgebraic ℚ c) : AlgVec (v - c • w) := by
  intro j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← K11.mem_Kq]
  exact K11.Kq.sub_mem (K11.mem_Kq.mpr (hv j)) (K11.Kq.mul_mem (K11.mem_Kq.mpr hc)
    (K11.mem_Kq.mpr (hw j)))

lemma algT_sub_smul {v w : Tan d0 d1 m} (hv : algT v) (hw : algT w) {c : ℂ}
    (hc : IsAlgebraic ℚ c) : algT (v - c • w) :=
  ⟨algVec_sub_smul' hv.1 hw.1 hc, algVec_sub_smul' hv.2.1 hw.2.1 hc,
    algVec_sub_smul' hv.2.2 hw.2.2 hc⟩

lemma ratT_inf_ker {W : Submodule ℂ (Tan d0 d1 m)} (hW : RatT W) {f : Tan d0 d1 m →ₗ[ℂ] ℂ}
    (hf : AlgFormT f) : RatT (W ⊓ LinearMap.ker f) := by
  classical
  obtain ⟨S, hSalg, rfl⟩ := hW
  by_cases h : ∀ s ∈ S, f s = 0
  · refine ⟨S, hSalg, ?_⟩
    refine inf_eq_left.mpr (Submodule.span_le.mpr fun s hs => ?_)
    exact LinearMap.mem_ker.mpr (h s hs)
  push Not at h
  obtain ⟨s₀, hs₀, hfs₀⟩ := h
  let g : Tan d0 d1 m → Tan d0 d1 m := fun s => s - (f s / f s₀) • s₀
  refine ⟨g '' S, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine algT_sub_smul (hSalg s hs) (hSalg s₀ hs₀) ?_
    rw [← K11.mem_Kq]
    exact K11.Kq.div_mem (K11.mem_Kq.mpr (hf s (hSalg s hs)))
      (K11.mem_Kq.mpr (hf s₀ (hSalg s₀ hs₀)))
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

lemma ratT_inf_finsetInf {W : Submodule ℂ (Tan d0 d1 m)} (hW : RatT W) {ι : Type*}
    (f : ι → Tan d0 d1 m →ₗ[ℂ] ℂ) (hf : ∀ i, AlgFormT (f i)) (s : Finset ι) :
    RatT (W ⊓ s.inf fun i => LinearMap.ker (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hW
  | insert a s _ ih =>
    rw [Finset.inf_insert, inf_comm (LinearMap.ker (f a)), ← inf_assoc]
    exact ratT_inf_ker ih (hf a)

/-- Intersecting with the preimage of a `ℚ̄`-rational subspace under an algebraic projection. -/
lemma ratT_inf_comap {n : ℕ} {W : Submodule ℂ (Tan d0 d1 m)} (hW : RatT W)
    (p : Tan d0 d1 m →ₗ[ℂ] (Fin n → ℂ)) (hp : ∀ v, algT v → AlgVec (p v))
    {R : Submodule ℂ (Fin n → ℂ)} (hR : RationalOverQbar R) : RatT (W ⊓ R.comap p) := by
  classical
  obtain ⟨A, B, hBA, hA⟩ := exists_algFrame R hR
  set P : Matrix (Fin n) (Fin n) K11.Kq := 1 - A * B with hP
  have hRker : R = LinearMap.ker (cmK K11.Kq P).mulVecLin := by
    apply le_antisymm
    · rw [← hA]; rintro _ ⟨c, rfl⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
        hP, cmK_sub, cmK_one, Matrix.sub_mul, Matrix.one_mul, cmK_mul, Matrix.mul_assoc,
        ← cmK_mul B A, hBA, cmK_one, Matrix.mul_one, sub_self, Matrix.zero_mulVec]
    · intro x hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hP, cmK_sub, cmK_one, Matrix.sub_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at hx
      rw [← hA, hx, cmK_mul, ← Matrix.mulVec_mulVec]
      exact ⟨_, rfl⟩
  let f : Fin n → Tan d0 d1 m →ₗ[ℂ] ℂ := fun i =>
    (LinearMap.proj i).comp ((cmK K11.Kq P).mulVecLin.comp p)
  have hf : ∀ i, AlgFormT (f i) := by
    intro i v hv
    have : f i v = (cmK K11.Kq P).mulVec (p v) i := rfl
    rw [this, ← K11.mem_Kq]
    simp only [cmK, Matrix.mulVec, dotProduct, Matrix.map_apply, Subfield.coe_subtype]
    exact K11.Kq.sum_mem fun j _ => K11.Kq.mul_mem (SetLike.coe_mem _) (K11.mem_Kq.mpr (hp v hv j))
  have h1 := ratT_inf_finsetInf hW f hf Finset.univ
  convert h1 using 2
  ext x
  rw [Submodule.mem_comap, hRker, LinearMap.mem_ker, Submodule.mem_finsetInf]
  simp only [Finset.mem_univ, true_implies, LinearMap.mem_ker]
  constructor
  · intro h i; exact congrFun h i
  · intro h; funext i; exact h i

lemma rational_torusLie (U : Submodule ℚ (Fin d1 → ℚ)) : RationalOverQbar (torusLie U) := by
  rw [torusLie_eq_annC, K11.annC_eq_cspan]
  apply le_antisymm
  · rw [K11.cspan_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨K11.castL_mem_cspan hq, fun j => ?_⟩
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (q j)
  · exact Submodule.span_le.mpr fun _ hw => hw.1

/-- **`W ∩ T_H` is `ℚ̄`-rational**, if abelian tangent spaces are. -/
lemma ratT_inf_tan (Ls : Fin m → PeriodPair)
    (hrat : ∀ t, IsAbelianTangent Ls t → RationalOverQbar t) {W : Submodule ℂ (Tan d0 d1 m)}
    (hW : RationalOverQbarTan W) (H : SubgroupData (d0 := d0) (d1 := d1) Ls) :
    RationalOverQbarTan (W ⊓ H.tan) := by
  rw [← ratT_iff] at hW ⊢
  let p1 : Tan d0 d1 m →ₗ[ℂ] (Fin d0 → ℂ) := LinearMap.fst ℂ _ _
  let p2 : Tan d0 d1 m →ₗ[ℂ] (Fin d1 → ℂ) := (LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)
  let p3 : Tan d0 d1 m →ₗ[ℂ] (Fin m → ℂ) := (LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)
  have e : H.tan = (H.h0.comap p1 ⊓ (torusLie H.U).comap p2) ⊓ H.t.comap p3 := by
    ext x; simp [SubgroupData.tan, Submodule.mem_prod, p1, p2, p3, and_assoc]
  rw [e, ← inf_assoc, ← inf_assoc]
  refine ratT_inf_comap (ratT_inf_comap (ratT_inf_comap hW p1 (fun v hv => hv.1) H.h0_rat)
    p2 (fun v hv => hv.2.1) (rational_torusLie H.U)) p3 (fun v hv => hv.2.2) (hrat _ H.t_ab)

/-! ### Abelian tangent spaces of a power of one curve are `ℚ̄`-rational -/

lemma isAlgebraic_of_lattice (L : PeriodPair) {x : ℂ} {n n' : ℕ} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (h1 : (n : ℂ) * L.ω₁ * x ∈ L.lattice) (h2 : (n' : ℂ) * L.ω₂ * x ∈ L.lattice) :
    IsAlgebraic ℚ x := by
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp h1
  obtain ⟨c, d, hcd⟩ := PeriodPair.mem_lattice.mp h2
  have hω₁ : L.ω₁ ≠ 0 := by
    intro h0
    have := LinearIndependent.pair_iff.mp L.indep 1 0 (by simp [h0])
    exact one_ne_zero this.1
  -- `n n' x² − (a n' + d n) x − (b c − a d) = 0`
  have key : ((n : ℂ) * n') * x ^ 2 - ((a : ℂ) * n' + d * n) * x - ((b : ℂ) * c - a * d) = 0 := by
    have e : L.ω₁ * (((n : ℂ) * n') * x ^ 2 - ((a : ℂ) * n' + d * n) * x - ((b : ℂ) * c - a * d))
        = 0 := by
      linear_combination ((n' : ℂ) * x) * hab.symm + (b : ℂ) * hcd.symm - (d : ℂ) * hab.symm
    exact (mul_eq_zero.mp e).resolve_left hω₁
  refine ⟨Polynomial.C ((n : ℚ) * n') * Polynomial.X ^ 2 -
    Polynomial.C ((a : ℚ) * n' + d * n) * Polynomial.X - Polynomial.C ((b : ℚ) * c - a * d),
    ?_, ?_⟩
  · intro h0
    have := congrArg (fun P => Polynomial.coeff P 2) h0
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at this
    have h3 : ((n : ℚ) * n') = 0 := by simpa using this
    rcases mul_eq_zero.mp h3 with h | h
    · exact hn (by exact_mod_cast h)
    · exact hn' (by exact_mod_cast h)
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow]
    simpa using key

/-- **Abelian tangent spaces of `E^r` are `ℚ̄`-rational.** -/
theorem abTan_rat_const (L : PeriodPair) {r : ℕ} (t : Submodule ℂ (Fin r → ℂ))
    (hab : IsAbelianTangent (fun _ : Fin r => L) t) : RationalOverQbar t := by
  classical
  obtain ⟨c⟩ := LSG.CM.nonempty_chart t
  have halg : ∀ k j, IsAlgebraic ℚ (c.lift (Pi.single k 1) j) := by
    intro k j
    have hw : ∀ ω ∈ L.lattice, ∀ k', (Pi.single k ω : Fin (finrank ℂ t) → ℂ) k' ∈
        ((fun _ : Fin r => L) (c.ι k')).lattice := by
      intro ω hω k'
      by_cases h : k' = k
      · subst h; simpa using hω
      · simp [h, L.lattice.zero_mem]
    obtain ⟨n, hn, hn1⟩ := c.exists_nsmul_lift_mem hab (hw _ L.ω₁_mem_lattice)
    obtain ⟨n', hn', hn2⟩ := c.exists_nsmul_lift_mem hab (hw _ L.ω₂_mem_lattice)
    have e : ∀ (N : ℕ) (ω : ℂ), c.lift (N • (Pi.single k ω : Fin (finrank ℂ t) → ℂ)) j =
        (N : ℂ) * ω * c.lift (Pi.single k 1) j := by
      intro N ω
      have : (N • (Pi.single k ω : Fin (finrank ℂ t) → ℂ)) = ((N : ℂ) * ω) • Pi.single k 1 := by
        ext i; by_cases h : i = k
        · subst h; simp [nsmul_eq_mul]
        · simp [h]
      rw [this, map_smul]; simp [mul_assoc]
    have h1 := hn1 j; rw [e] at h1
    have h2 := hn2 j; rw [e] at h2
    exact isAlgebraic_of_lattice L hn hn' h1 h2
  apply le_antisymm
  · intro z hz
    rw [← c.lift_proj hz]
    have : LSG.CM.proj c.ι z = ∑ k, (LSG.CM.proj c.ι z k) • (Pi.single k 1 : Fin (finrank ℂ t) → ℂ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c.lift_mem _, halg k⟩)
  · exact Submodule.span_le.mpr fun _ hw => hw.1

end LSG.W88.K5d
