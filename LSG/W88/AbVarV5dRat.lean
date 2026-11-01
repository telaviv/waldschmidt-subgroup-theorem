/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarV5dRoy
import LSG.W88.K5dRat

/-!
# M2.7e: `W ∩ T_H` is `ℚ̄`-rational (vector-extension class)

**`ratAV_inf_tan`**: for `W ⊂ TanAV d₀ d₁ r B` `ℚ̄`-rational and a member `H`, `W ∩ T_H` is `ℚ̄`-rational, given
`RatTangentsV B` and `PerTanFib B M`. Copy of `ratA_inf_tan` (`AbVar5dRat.lean`): `T_H` is an intersection of
preimages of `ℚ̄`-rational subspaces under algebraic projections,
* `t ≠ 0`: `pr₀ Γ`, `torusLie U`, `t` (`mem_tan_iff_of_ne`);
* `t = 0`: `Γ` (flattened), `torusLie U`, `0` (`tan_eq_of_bot`).
-/

open Complex Module Submodule LSG.AuxAV LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.W88.AVS

open LSG.MEB (IsRatSub)
open LSG.MEBV (VBlock perTanId perBase)
open LSG.W88.Vec (RatPair AlgPair AlgMat)
open K5d (cmK cmK_sub cmK_one cmK_mul exists_algFrame algVec_sub_smul' rational_torusLie)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {M : Matrix (Fin r) (Fin m) ℂ}

/-- `W` is spanned by algebraic vectors. -/
def RatAV (W : Submodule ℂ (TanAV d₀ d₁ r B)) : Prop :=
  ∃ S : Set (TanAV d₀ d₁ r B), (∀ v ∈ S, AlgTanAV v) ∧ W = Submodule.span ℂ S

lemma ratAV_iff (W : Submodule ℂ (TanAV d₀ d₁ r B)) : RatAV W ↔ RationalOverQbarAV W := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    apply le_antisymm
    · exact Submodule.span_mono fun v hv => ⟨Submodule.subset_span hv, hS v hv⟩
    · exact Submodule.span_le.mpr fun _ hw => hw.1
  · intro h; exact ⟨_, fun v hv => hv.2, h⟩

/-- A linear form taking algebraic values on algebraic vectors. -/
def AlgFormAV (f : TanAV d₀ d₁ r B →ₗ[ℂ] ℂ) : Prop := ∀ v, AlgTanAV v → IsAlgebraic ℚ (f v)

lemma algTanAV_sub_smul {v w : TanAV d₀ d₁ r B} (hv : AlgTanAV v) (hw : AlgTanAV w) {c : ℂ}
    (hc : IsAlgebraic ℚ c) : AlgTanAV (v - c • w) := by
  refine ⟨algVec_sub_smul' hv.1 hw.1 hc, algVec_sub_smul' hv.2.1 hw.2.1 hc, fun k j => ?_,
    algVec_sub_smul' hv.2.2.2 hw.2.2.2 hc⟩
  change IsAlgebraic ℚ (v.2.2.1 k j - c * w.2.2.1 k j)
  exact (hv.2.2.1 k j).sub (hc.mul (hw.2.2.1 k j))

lemma ratAV_inf_ker {W : Submodule ℂ (TanAV d₀ d₁ r B)} (hW : RatAV W) {f : TanAV d₀ d₁ r B →ₗ[ℂ] ℂ}
    (hf : AlgFormAV f) : RatAV (W ⊓ LinearMap.ker f) := by
  classical
  obtain ⟨S, hSalg, rfl⟩ := hW
  by_cases h : ∀ s ∈ S, f s = 0
  · refine ⟨S, hSalg, ?_⟩
    refine inf_eq_left.mpr (Submodule.span_le.mpr fun s hs => ?_)
    exact LinearMap.mem_ker.mpr (h s hs)
  push Not at h
  obtain ⟨s₀, hs₀, hfs₀⟩ := h
  let g : TanAV d₀ d₁ r B → TanAV d₀ d₁ r B := fun s => s - (f s / f s₀) • s₀
  refine ⟨g '' S, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine algTanAV_sub_smul (hSalg s hs) (hSalg s₀ hs₀) ?_
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

lemma ratAV_inf_finsetInf {W : Submodule ℂ (TanAV d₀ d₁ r B)} (hW : RatAV W) {ι : Type*}
    (f : ι → TanAV d₀ d₁ r B →ₗ[ℂ] ℂ) (hf : ∀ i, AlgFormAV (f i)) (s : Finset ι) :
    RatAV (W ⊓ s.inf fun i => LinearMap.ker (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hW
  | insert a s _ ih =>
    rw [Finset.inf_insert, inf_comm (LinearMap.ker (f a)), ← inf_assoc]
    exact ratAV_inf_ker ih (hf a)

/-- Intersecting with the preimage of a `ℚ̄`-rational subspace under an algebraic projection. -/
lemma ratAV_inf_comap {n : ℕ} {W : Submodule ℂ (TanAV d₀ d₁ r B)} (hW : RatAV W)
    (p : TanAV d₀ d₁ r B →ₗ[ℂ] (Fin n → ℂ)) (hp : ∀ v, AlgTanAV v → AlgVec (p v))
    {R : Submodule ℂ (Fin n → ℂ)} (hR : RationalOverQbar R) : RatAV (W ⊓ R.comap p) := by
  classical
  obtain ⟨A, Bf, hBA, hA⟩ := exists_algFrame R hR
  set P : Matrix (Fin n) (Fin n) K11.Kq := 1 - A * Bf with hP
  have hRker : R = LinearMap.ker (cmK K11.Kq P).mulVecLin := by
    apply le_antisymm
    · rw [← hA]; rintro _ ⟨c, rfl⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
        hP, cmK_sub, cmK_one, Matrix.sub_mul, Matrix.one_mul, cmK_mul, Matrix.mul_assoc,
        ← cmK_mul Bf A, hBA, cmK_one, Matrix.mul_one, sub_self, Matrix.zero_mulVec]
    · intro x hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hP, cmK_sub, cmK_one, Matrix.sub_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at hx
      rw [← hA, hx, cmK_mul, ← Matrix.mulVec_mulVec]
      exact ⟨_, rfl⟩
  let f : Fin n → TanAV d₀ d₁ r B →ₗ[ℂ] ℂ := fun i =>
    (LinearMap.proj i).comp ((cmK K11.Kq P).mulVecLin.comp p)
  have hf : ∀ i, AlgFormAV (f i) := by
    intro i v hv
    have : f i v = (cmK K11.Kq P).mulVec (p v) i := rfl
    rw [this, ← K11.mem_Kq]
    simp only [cmK, Matrix.mulVec, dotProduct, Matrix.map_apply, Subfield.coe_subtype]
    exact K11.Kq.sum_mem fun j _ => K11.Kq.mul_mem (SetLike.coe_mem _) (K11.mem_Kq.mpr (hp v hv j))
  have h1 := ratAV_inf_finsetInf hW f hf Finset.univ
  convert h1 using 2
  ext x
  rw [Submodule.mem_comap, hRker, LinearMap.mem_ker, Submodule.mem_finsetInf]
  simp only [Finset.mem_univ, true_implies, LinearMap.mem_ker]
  constructor
  · intro h i; exact congrFun h i
  · intro h; funext i; exact h i

/-! ### Flattening the block coordinates -/

variable (B) in
/-- The number of block coordinates. -/
abbrev nZ : ℕ := Fintype.card (Σ k, Fin (B k).g)

variable (B) in
/-- `z ↦ (z_{k,j})` flattened to `Fin (nZ B)`. -/
def flatZ : (∀ k, Fin (B k).g → ℂ) →ₗ[ℂ] (Fin (nZ B) → ℂ) where
  toFun z i := z ((Fintype.equivFin _).symm i).1 ((Fintype.equivFin _).symm i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma flatZ_injective : Function.Injective (flatZ B) := by
  intro z w h
  funext k j
  obtain ⟨i, hi⟩ := (Fintype.equivFin (Σ k, Fin (B k).g)).symm.surjective ⟨k, j⟩
  have := congrFun h i
  change z ((Fintype.equivFin _).symm i).1 ((Fintype.equivFin _).symm i).2 =
    w ((Fintype.equivFin _).symm i).1 ((Fintype.equivFin _).symm i).2 at this
  rw [hi] at this
  exact this

lemma rational_flatZ {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)}
    (ht : t = span ℂ {z | z ∈ t ∧ ∀ k j, IsAlgebraic ℚ (z k j)}) :
    RationalOverQbar (t.map (flatZ B)) := by
  apply le_antisymm
  · conv_lhs => rw [ht]
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz.1, rfl⟩, fun i => hz.2 _ _⟩
  · exact Submodule.span_le.mpr fun _ hw => hw.1

lemma comap_flatZ (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) (x : TanAV d₀ d₁ r B) :
    flatZ B x.2.2.1 ∈ t.map (flatZ B) ↔ x.2.2.1 ∈ t :=
  ⟨fun ⟨y, hy, hxy⟩ => flatZ_injective hxy ▸ hy, fun h => ⟨_, h, rfl⟩⟩

/-- **`W ∩ T_H` is `ℚ̄`-rational.** -/
theorem ratAV_inf_tan (hRT : RatTangentsV B) (hF : PerTanFib B M) {W : Submodule ℂ (TanAV d₀ d₁ r B)}
    (hW : RationalOverQbarAV W) (H : SubgroupDataAV d₀ d₁ B M) : RationalOverQbarAV (W ⊓ H.tan) := by
  rw [← ratAV_iff] at hW ⊢
  let p2 : TanAV d₀ d₁ r B →ₗ[ℂ] (Fin d₁ → ℂ) := (LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)
  let p3 : TanAV d₀ d₁ r B →ₗ[ℂ] (Fin (nZ B) → ℂ) :=
    (flatZ B).comp ((LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)))
  have hp2 : ∀ v : TanAV d₀ d₁ r B, AlgTanAV v → AlgVec (p2 v) := fun v hv => hv.2.1
  have hp3 : ∀ v : TanAV d₀ d₁ r B, AlgTanAV v → AlgVec (p3 v) := fun v hv i => hv.2.2.1 _ _
  by_cases ht : H.t = ⊥
  · let p1 : TanAV d₀ d₁ r B →ₗ[ℂ] (Fin (d₀ + r) → ℂ) :=
      (flatL d₀ r).comp ((LinearMap.fst ℂ _ _).prod
        ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))))
    have hp1 : ∀ v : TanAV d₀ d₁ r B, AlgTanAV v → AlgVec (p1 v) := fun v hv =>
      algVec_flat ⟨hv.1, hv.2.2.2⟩
    have e : H.tan = ((H.gam.map (flatL d₀ r)).comap p1 ⊓ (torusLie H.U).comap p2) ⊓
        ((⊥ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)).map (flatZ B)).comap p3 := by
      rw [tan_eq_of_bot H ht]
      ext x
      simp only [Submodule.mem_inf, Submodule.mem_comap]
      change _ ↔ (_ ∧ _) ∧ flatZ B x.2.2.1 ∈ _
      rw [comap_flatZ ⊥ x]
      constructor
      · intro hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
        obtain ⟨γ, hγ, rfl⟩ := hy
        obtain ⟨b, hb, rfl⟩ := hz
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · refine ⟨γ, hγ, ?_⟩
          change flatL d₀ r γ = flatL d₀ r (γ.1 + 0, γ.2 + 0)
          simp
        · change 0 + b ∈ torusLie H.U; simpa using hb
        · change (0 : ∀ k, Fin (B k).g → ℂ) + 0 ∈ (⊥ : Submodule ℂ _); simp
      · rintro ⟨⟨⟨γ, hγ, hγx⟩, hb⟩, hz⟩
        have hz0 : x.2.2.1 = 0 := (mem_bot ℂ).mp hz
        have hγ' : γ = (x.1, x.2.2.2) := by
          have := congrArg (unflatL d₀ r) hγx
          rw [unflat_flat] at this
          exact this.trans (unflat_flat (x.1, x.2.2.2))
        have e : x = vecInclA γ + torInclA x.2.1 := by
          rw [hγ']; obtain ⟨a, b, z, s⟩ := x; simp only at hz0; subst hz0
          ext <;> simp [vecInclA, torInclA]
        rw [e]
        exact add_mem (mem_sup_left ⟨γ, hγ, rfl⟩) (mem_sup_right ⟨x.2.1, hb, rfl⟩)
    rw [e, ← inf_assoc, ← inf_assoc]
    exact ratAV_inf_comap (ratAV_inf_comap (ratAV_inf_comap hW p1 hp1 (rational_map_flat H.gam_rat))
      p2 hp2 (rational_torusLie H.U)) p3 hp3 (rational_flatZ (le_antisymm bot_le (span_le.mpr fun z hz => hz.1)))
  · let p1 : TanAV d₀ d₁ r B →ₗ[ℂ] (Fin d₀ → ℂ) := LinearMap.fst ℂ _ _
    have hrat0 : RationalOverQbar (H.gam.map (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin r → ℂ))) := by
      apply le_antisymm
      · conv_lhs => rw [H.gam_rat]
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨s, hs, rfl⟩
        exact Submodule.subset_span ⟨⟨s, hs.1, rfl⟩, hs.2.1⟩
      · exact Submodule.span_le.mpr fun _ hw => hw.1
    have e : H.tan = ((H.gam.map (LinearMap.fst ℂ _ _)).comap p1 ⊓ (torusLie H.U).comap p2) ⊓
        (H.t.map (flatZ B)).comap p3 := by
      ext x
      simp only [Submodule.mem_inf, Submodule.mem_comap]
      change _ ↔ (_ ∧ _) ∧ flatZ B x.2.2.1 ∈ _
      rw [comap_flatZ H.t x, mem_tan_iff_of_ne hF H ht, and_assoc]
      rfl
    rw [e, ← inf_assoc, ← inf_assoc]
    exact ratAV_inf_comap (ratAV_inf_comap (ratAV_inf_comap hW p1 (fun v hv => hv.1) hrat0)
      p2 hp2 (rational_torusLie H.U)) p3 hp3 (rational_flatZ (hRT H.t H.t_rat))

end LSG.W88
