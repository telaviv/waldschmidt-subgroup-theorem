/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVar5dA
import LSG.W88.K5dRat
import LSG.W88.AbVarQbar

/-!
# A5.9g: `hratA` from the `ℚ̄`-rationality of abelian tangents (`STAGE_A5.md` §6.7 (i))

`RatTangentsA` (defined by γ in `LSG/W88/AbVarQbar.lean`, statement agreed in `STAGE_A5.md` §6.7): every
`t ⊂ (ℂ²)^r` with `IsAbelianTangentA t` is spanned by its vectors with algebraic coordinates.

**`ratA_inf_tan`**: then `W ∩ T_H` is `ℚ̄`-rational for `ℚ̄`-rational `W ⊂ TanA d₀ d₁ r` and every `SubgroupDataB`.
Copy of `K5d.ratT_inf_tan` (`K5dRat.lean`): `T_H` is the intersection of preimages of `h₀`, `torusLie U` and `t` under
the algebraic projections, and intersecting with the kernel of an algebraic linear form preserves rationality. The
`t`-part is flattened along `(Fin r → Fin 2 → ℂ) ≃ (Fin (r·2) → ℂ)` (`flatA`).

**`hyperplaneKappaAbVar_of_ratTangents (hRT : RatTangentsA) : HyperplaneKappaAbVar`**.
-/

open Module LSG.AuxA LSG.JacBlock

noncomputable section

namespace LSG.W88

open K5d (cmK cmK_sub cmK_one cmK_mul exists_algFrame algVec_sub_smul' rational_torusLie)

variable {d0 d1 r : ℕ}

/-- `W` is spanned by algebraic vectors. -/
def RatA (W : Submodule ℂ (TanA d0 d1 r)) : Prop :=
  ∃ S : Set (TanA d0 d1 r), (∀ v ∈ S, AlgTanA v) ∧ W = Submodule.span ℂ S

lemma ratA_iff (W : Submodule ℂ (TanA d0 d1 r)) : RatA W ↔ RationalOverQbarA W := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    apply le_antisymm
    · exact Submodule.span_mono fun v hv => ⟨Submodule.subset_span hv, hS v hv⟩
    · exact Submodule.span_le.mpr fun _ hw => hw.1
  · intro h; exact ⟨_, fun v hv => hv.2, h⟩

/-- A linear form taking algebraic values on algebraic vectors. -/
def AlgFormA (f : TanA d0 d1 r →ₗ[ℂ] ℂ) : Prop := ∀ v, AlgTanA v → IsAlgebraic ℚ (f v)

lemma algTanA_sub_smul {v w : TanA d0 d1 r} (hv : AlgTanA v) (hw : AlgTanA w) {c : ℂ}
    (hc : IsAlgebraic ℚ c) : AlgTanA (v - c • w) :=
  ⟨algVec_sub_smul' hv.1 hw.1 hc, algVec_sub_smul' hv.2.1 hw.2.1 hc,
    fun j => algVec_sub_smul' (hv.2.2 j) (hw.2.2 j) hc⟩

lemma ratA_inf_ker {W : Submodule ℂ (TanA d0 d1 r)} (hW : RatA W) {f : TanA d0 d1 r →ₗ[ℂ] ℂ}
    (hf : AlgFormA f) : RatA (W ⊓ LinearMap.ker f) := by
  classical
  obtain ⟨S, hSalg, rfl⟩ := hW
  by_cases h : ∀ s ∈ S, f s = 0
  · refine ⟨S, hSalg, ?_⟩
    refine inf_eq_left.mpr (Submodule.span_le.mpr fun s hs => ?_)
    exact LinearMap.mem_ker.mpr (h s hs)
  push Not at h
  obtain ⟨s₀, hs₀, hfs₀⟩ := h
  let g : TanA d0 d1 r → TanA d0 d1 r := fun s => s - (f s / f s₀) • s₀
  refine ⟨g '' S, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine algTanA_sub_smul (hSalg s hs) (hSalg s₀ hs₀) ?_
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

lemma ratA_inf_finsetInf {W : Submodule ℂ (TanA d0 d1 r)} (hW : RatA W) {ι : Type*}
    (f : ι → TanA d0 d1 r →ₗ[ℂ] ℂ) (hf : ∀ i, AlgFormA (f i)) (s : Finset ι) :
    RatA (W ⊓ s.inf fun i => LinearMap.ker (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hW
  | insert a s _ ih =>
    rw [Finset.inf_insert, inf_comm (LinearMap.ker (f a)), ← inf_assoc]
    exact ratA_inf_ker ih (hf a)

/-- Intersecting with the preimage of a `ℚ̄`-rational subspace under an algebraic projection. -/
lemma ratA_inf_comap {n : ℕ} {W : Submodule ℂ (TanA d0 d1 r)} (hW : RatA W)
    (p : TanA d0 d1 r →ₗ[ℂ] (Fin n → ℂ)) (hp : ∀ v, AlgTanA v → AlgVec (p v))
    {R : Submodule ℂ (Fin n → ℂ)} (hR : RationalOverQbar R) : RatA (W ⊓ R.comap p) := by
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
  let f : Fin n → TanA d0 d1 r →ₗ[ℂ] ℂ := fun i =>
    (LinearMap.proj i).comp ((cmK K11.Kq P).mulVecLin.comp p)
  have hf : ∀ i, AlgFormA (f i) := by
    intro i v hv
    have : f i v = (cmK K11.Kq P).mulVec (p v) i := rfl
    rw [this, ← K11.mem_Kq]
    simp only [cmK, Matrix.mulVec, dotProduct, Matrix.map_apply, Subfield.coe_subtype]
    exact K11.Kq.sum_mem fun j _ => K11.Kq.mul_mem (SetLike.coe_mem _) (K11.mem_Kq.mpr (hp v hv j))
  have h1 := ratA_inf_finsetInf hW f hf Finset.univ
  convert h1 using 2
  ext x
  rw [Submodule.mem_comap, hRker, LinearMap.mem_ker, Submodule.mem_finsetInf]
  simp only [Finset.mem_univ, true_implies, LinearMap.mem_ker]
  constructor
  · intro h i; exact congrFun h i
  · intro h; funext i; exact h i

/-- Flattening `(ℂ²)^r ≃ ℂ^{2r}`. -/
def flatA (r : ℕ) : (Fin r → Fin 2 → ℂ) ≃ₗ[ℂ] (Fin (r * 2) → ℂ) :=
  (LinearEquiv.curry ℂ ℂ (Fin r) (Fin 2)).symm.trans (LinearEquiv.funCongrLeft ℂ ℂ finProdFinEquiv.symm)

lemma flatA_apply (z : Fin r → Fin 2 → ℂ) (i : Fin (r * 2)) :
    flatA r z i = z (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := rfl

lemma algVec_flatA {z : Fin r → Fin 2 → ℂ} (hz : AlgVecA z) : AlgVec (flatA r z) := fun i => by
  rw [flatA_apply]; exact hz _ _

lemma rational_flatA {t : Submodule ℂ (Fin r → Fin 2 → ℂ)}
    (ht : t = Submodule.span ℂ {z | z ∈ t ∧ AlgVecA z}) : RationalOverQbar (t.map (flatA r).toLinearMap) := by
  apply le_antisymm
  · conv_lhs => rw [ht]
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz.1, rfl⟩, algVec_flatA hz.2⟩
  · exact Submodule.span_le.mpr fun _ hw => hw.1

/-- **`W ∩ T_H` is `ℚ̄`-rational**, given `RatTangentsA`. -/
theorem ratA_inf_tan (hRT : RatTangentsA) {W : Submodule ℂ (TanA d0 d1 r)}
    (hW : RationalOverQbarA W) (H : SubgroupDataA d0 d1 r) : RationalOverQbarA (W ⊓ H.tan) := by
  rw [← ratA_iff] at hW ⊢
  let p1 : TanA d0 d1 r →ₗ[ℂ] (Fin d0 → ℂ) := LinearMap.fst ℂ _ _
  let p2 : TanA d0 d1 r →ₗ[ℂ] (Fin d1 → ℂ) := (LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)
  let p3 : TanA d0 d1 r →ₗ[ℂ] (Fin (r * 2) → ℂ) :=
    (flatA r).toLinearMap.comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))
  have e3 : H.t.comap ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _) :
      TanA d0 d1 r →ₗ[ℂ] (Fin r → Fin 2 → ℂ)) = (H.t.map (flatA r).toLinearMap).comap p3 := by
    ext x
    simp only [Submodule.mem_comap, p3, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, hxy⟩ => (flatA r).injective hxy ▸ hy⟩
  have e : H.tan = (H.h0.comap p1 ⊓ (torusLie H.U).comap p2) ⊓ (H.t.map (flatA r).toLinearMap).comap p3 := by
    rw [← e3]
    ext x; simp [SubgroupDataA.tan, Submodule.mem_prod, p1, p2, and_assoc]
  rw [e, ← inf_assoc, ← inf_assoc]
  exact ratA_inf_comap (ratA_inf_comap (ratA_inf_comap hW p1 (fun v hv => hv.1) H.h0_rat)
    p2 (fun v hv => hv.2.1) (rational_torusLie H.U)) p3 (fun v hv => algVec_flatA hv.2.2)
    (rational_flatA (hRT r H.t H.t_ab))

/-- **`hratA` from `RatTangentsA`**, in the form `hyperplaneKappaAbVar_of_rat` takes. -/
theorem hratA_of (hRT : RatTangentsA) (d0 d1 r : ℕ)
    (W : Submodule ℂ (MEB.Tan d0 d1 (fun _ : Fin r => aBlock)))
    (H : SubgroupDataB d0 d1 (fun _ : Fin r => aBlock)) :
    RationalOverQbarB W → RationalOverQbarB (W ⊓ H.tan) := by
  intro hW
  have hΛle : ∀ k, latF (aBlockAnF r) k ≤ ((fun _ : Fin r => aBlock) k).per :=
    fun k => (aBlockAnF r k).lat_le
  have hΛ : ∀ k, IsNsmulIn (latF (aBlockAnF r) k) ((fun _ : Fin r => aBlock) k).per :=
    fun k => (aBlockAnF r k).lat_nsmul
  have hset : {z | z ∈ H.t ∧ z ∈ LSG.MEB.perAbL (latF (aBlockAnF r))} =
      {z : Fin r → Fin 2 → ℂ | z ∈ H.t ∧ ∀ j, z j ∈ LSG.JacAn.latt} := by
    ext z
    simp only [Set.mem_ofPred_eq, LSG.MEB.perAbL, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    rfl
  have htab : IsAbelianTangentA H.t := by
    have := (LSG.MEB.isRatSub_perAb_iff hΛle hΛ H.t).mpr H.t_rat
    unfold LSG.MEB.IsRatSub at this
    unfold IsAbelianTangentA
    exact this.trans (congrArg (Submodule.span ℝ) hset)
  exact ratA_inf_tan (d0 := d0) (d1 := d1) (r := r) hRT hW ⟨H.h0, H.U, H.t, H.h0_rat, htab⟩

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × A^r`**, given `RatTangentsA`. -/
theorem hyperplaneKappaAbVar_of_ratTangents (hRT : RatTangentsA) : HyperplaneKappaAbVar :=
  hyperplaneKappaAbVar_of_rat (hratA_of hRT)

end LSG.W88
