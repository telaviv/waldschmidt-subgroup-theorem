/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVar5dTrans

/-!
# A5.9d: Theorem 4.1 for `G_a^{k₀} × G_m^{k₁}` inside `MEB.Tan k₀ k₁ B`, from Roy's Theorem 1 (`STAGE_A5.md` §6.6 (a)2)

**`thm41SubAtB_bot`**: `Thm41SubAtB An k₀ k₁ ⊥` (no (NR) needed). Copy of `K5d.sub41Concl_bot`, through
`epsB : Roy.E k₀ k₁ → MEB.Tan k₀ k₁ B`, `x ↦ (x.1, x.2, 0)`; only the `G_a`/`G_m` parts enter.
-/

open Complex Module LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.MEB (AbBlock perAb IsRatSub tanOf)
open K5d (cmK mem_omega_iff finrank_comap_inj finrank_map_inj finrank_map_add_inf_ker map_inf_comap
  rightInv_of_surjective ker_eq_span_cols)

variable {m : ℕ} {B : Fin m → AbBlock}

/-- `(a, c) ↦ (a, c, 0)`. -/
def epsB (k0 k1 : ℕ) (B : Fin m → AbBlock) : StrongSix.Roy.E k0 k1 →ₗ[ℂ] MEB.Tan k0 k1 B :=
  (LinearMap.fst ℂ _ _).prod ((LinearMap.snd ℂ _ _).prod 0)

lemma epsB_apply (k0 k1 : ℕ) (x : StrongSix.Roy.E k0 k1) : epsB k0 k1 B x = (x.1, x.2, 0) := rfl

lemma epsB_injective (k0 k1 : ℕ) : Function.Injective (epsB k0 k1 B) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun p => p.2.1) h
  exact Prod.ext h1 h2

lemma range_epsB (k0 k1 : ℕ) :
    LinearMap.range (epsB k0 k1 B) = tanBB k0 k1 (⊥ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) := by
  ext x; constructor
  · rintro ⟨y, rfl⟩; simp [epsB_apply, tanBB, Submodule.mem_prod]
  · intro hx
    simp only [tanBB, Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot, true_and] at hx
    exact ⟨(x.1, x.2.1), by rw [epsB_apply, ← hx]⟩

lemma isRatSub_botB : IsRatSub (perAb B) (⊥ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) := by
  apply le_antisymm
  · intro x hx
    have : x = 0 := (Submodule.mem_bot ℂ).mp hx
    rw [this]; exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro z ⟨hz, -⟩
    exact hz

lemma span_lam_propB {k0 k1 : ℕ} {An : ∀ k, AbBlockAn (B k)} {Y : AddSubgroup (MEB.Tan k0 k1 B)}
    (hY : ∀ y ∈ Y, y ∈ LamB k0 k1 An) {x : MEB.Tan k0 k1 B} (hx : x ∈ Submodule.span ℚ (Y : Set _)) :
    LSG.W88.AlgVec x.1 ∧ ∀ j, IsAlgebraic ℚ (Complex.exp (x.2.1 j)) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨(hY x hx).1, (hY x hx).2.1⟩
  | zero => exact ⟨fun i => by simpa using isAlgebraic_zero, fun j => by simpa using isAlgebraic_one⟩
  | add x y _ _ hx hy =>
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, ← K11.mem_Kq]
      exact K11.Kq.add_mem (K11.mem_Kq.mpr (hx.1 i)) (K11.mem_Kq.mpr (hy.1 i))
    · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Complex.exp_add, ← K11.mem_Kq]
      exact K11.Kq.mul_mem (K11.mem_Kq.mpr (hx.2 j)) (K11.mem_Kq.mpr (hy.2 j))
  | smul q x _ hx =>
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simp only [Prod.smul_fst, Pi.smul_apply, Rat.smul_def, ← K11.mem_Kq]
      exact K11.Kq.mul_mem (SubfieldClass.ratCast_mem _ _) (K11.mem_Kq.mpr (hx.1 i))
    · simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, Rat.smul_def]
      exact K11.isAlg_exp_ratMul q (hx.2 j)

/-! ### The period spaces -/

/-- Elements of `span_ℚ Per` have zero additive part and toric part in `2πiℚ^{k₁}`. -/
lemma span_per_propB {k0 k1 : ℕ} {x : MEB.Tan k0 k1 B}
    (hx : x ∈ Submodule.span ℚ ((MEB.Per k0 k1 B : AddSubgroup (MEB.Tan k0 k1 B)) : Set (MEB.Tan k0 k1 B))) :
    x.1 = 0 ∧ ∃ q : Fin k1 → ℚ, x.2.1 = (2 * Real.pi * I : ℂ) • K11.castL k1 q := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h1, h2, -⟩ := hx
    choose kv hkv using h2
    refine ⟨h1, fun i => (kv i : ℚ), ?_⟩
    ext i; rw [hkv i]; simp [mul_comm]
  | zero => exact ⟨rfl, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, q, hq⟩ := hx
    obtain ⟨hy1, q', hq'⟩ := hy
    exact ⟨by simp [hx1, hy1], q + q', by simp [hq, hq', smul_add]⟩
  | smul c x _ hx =>
    obtain ⟨hx1, q, hq⟩ := hx
    refine ⟨by simp [hx1], c • q, ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, hq, map_smul]
    rw [smul_comm]

lemma comap_span_perB {k0 k1 : ℕ} :
    (Submodule.span ℚ ((MEB.Per k0 k1 B : AddSubgroup (MEB.Tan k0 k1 B)) : Set (MEB.Tan k0 k1 B))).comap
      ((epsB k0 k1 B).restrictScalars ℚ) =
      StrongSix.Roy.Omega k0 k1 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, q, hq⟩ := span_per_propB hx
    exact mem_omega_iff.mpr ⟨h1, q, hq⟩
  · rw [StrongSix.Roy.Omega, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨rfl, fun i => ⟨if i = j then 1 else 0, ?_⟩,
      fun k => (B k).per.zero_mem⟩
    change (Pi.single j (2 * Real.pi * I) : Fin k1 → ℂ) i = _
    by_cases h : i = j
    · subst h; simp
    · simp [h]


/-- **Theorem 4.1 for `G_a^{k₀} × G_m^{k₁}` (no (NR)), from Roy's Theorem 1.** -/
theorem sub41ConclB_bot {k0 k1 : ℕ} (An : ∀ k, AbBlockAn (B k)) (V W : Submodule ℂ (MEB.Tan k0 k1 B))
    (Y : AddSubgroup (MEB.Tan k0 k1 B)) (hVT : V ≤ tanBB k0 k1 ⊥) (hdim : finrank ℂ V < k0 + k1)
    (hWV : W ≤ V) (hWrat : RationalOverQbarB W) (hYfg : Y.FG)
    (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamB k0 k1 An) :
    ∃ H : SubgroupDataB k0 k1 B, H.t ≤ ⊥ ∧ H.δBt ⊥ ≠ 0 ∧
      finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) < H.δBt ⊥ ∧
      (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ MEB.Per k0 k1 B)) + H.δ1 +
          2 * (finrank ℂ (⊥ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) - finrank ℂ H.t) : ℕ) : ℤ) *
          ((k0 + k1 + finrank ℂ (⊥ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : ℕ) - finrank ℂ V : ℤ) ≤
        ((H.δBt ⊥ : ℤ) - (finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ)) *
          ((k1 + 2 * finrank ℂ (⊥ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : ℕ) -
            rk (Y ⊓ MEB.Per k0 k1 B) : ℤ)) := by
  classical
  set ε := epsB k0 k1 B with hε
  set εq := ε.restrictScalars ℚ with hεq
  have hεinj : Function.Injective ε := epsB_injective (B := B) k0 k1
  have hεqinj : Function.Injective εq := hεinj
  have hrange : LinearMap.range ε = tanBB k0 k1 ⊥ := range_epsB (B := B) k0 k1
  set Yq := Submodule.span ℚ (Y : Set (MEB.Tan k0 k1 B)) with hYq
  have : FiniteDimensional ℚ Yq := K11.finiteDimensional_span_of_fg hYfg
  have hYqr : Yq ≤ LinearMap.range εq := by
    rw [Submodule.span_le]; intro y hy
    obtain ⟨z, hz⟩ := hrange.symm ▸ hVT (hY y hy).1
    exact ⟨z, hz⟩
  have hVr : V ≤ LinearMap.range ε := hrange ▸ hVT
  have hWr : W ≤ LinearMap.range ε := hWV.trans hVr
  set YR := Yq.comap εq with hYR
  set WR := W.comap ε with hWR
  set VR := V.comap ε with hVR
  have hfYR : finrank ℚ YR = finrank ℚ Yq := finrank_comap_inj hεqinj hYqr
  have hfVR : finrank ℂ VR = finrank ℂ V := finrank_comap_inj hεinj hVr
  have hfWR : finrank ℂ WR = finrank ℂ W := finrank_comap_inj hεinj hWr
  have hYRfin : FiniteDimensional ℚ YR := by
    have : FiniteDimensional ℚ ↥(YR.map εq) :=
      Submodule.finiteDimensional_of_le (Submodule.map_comap_le _ _)
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective εq hεqinj YR).symm
  -- the projection `ρ`
  let ρ : MEB.Tan k0 k1 B →ₗ[ℂ] StrongSix.Roy.E k0 k1 :=
    (LinearMap.fst ℂ _ _).prod ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))
  have hερ : ∀ x ∈ LinearMap.range ε, ε (ρ x) = x := by
    rintro _ ⟨y, rfl⟩; rfl
  have hWRrat : StrongSix.Roy.RationalOverQbar WR := by
    set S := {w | w ∈ W ∧ AlgTanB w} with hS
    have hSW : ∀ s ∈ S, s ∈ W := fun s hs => hs.1
    apply le_antisymm
    · intro x hx
      have hx' : ε x ∈ Submodule.span ℂ S := by rw [← hWrat]; exact hx
      have : x = ρ (ε x) := rfl
      rw [this]
      have hmap : (Submodule.span ℂ S).map ρ ≤ Submodule.span ℂ
          {w | w ∈ WR ∧ StrongSix.Roy.AlgVec w.1 ∧ StrongSix.Roy.AlgVec w.2} := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨s, hs, rfl⟩
        refine Submodule.subset_span ⟨?_, hs.2.1, hs.2.2.1⟩
        change ε (ρ s) ∈ W
        rw [hερ s (hWr hs.1)]; exact hs.1
      exact hmap ⟨ε x, hx', rfl⟩
    · rw [Submodule.span_le]; exact fun x hx => hx.1
  have hYprop : ∀ p ∈ YR, StrongSix.Roy.AlgVec p.1 ∧ ∀ j, p.2 j ∈ StrongSix.logAlg := by
    intro p hp
    have := span_lam_propB (fun y hy => (hY y hy).2) (show εq p ∈ Yq from hp)
    exact ⟨this.1, this.2⟩
  have hYV : ∀ p ∈ YR, p ∈ VR := by
    intro p hp
    change ε p ∈ V
    have : εq p ∈ Yq := hp
    exact (Submodule.span_le.mpr (fun y hy => (hY y hy).1) : Yq ≤ V.restrictScalars ℚ) this
  have hVne : VR ≠ ⊤ := by
    intro htop
    have := hfVR
    rw [htop, finrank_top] at this
    simp only [StrongSix.Roy.E, Module.finrank_prod, Module.finrank_fin_fun] at this
    omega
  obtain ⟨d0', d1', s, hsurj, hs0, hs1, hWs, hratio⟩ :=
    StrongSix.M2.waldschmidtTheorem1 k0 k1 YR WR VR hYRfin hYprop hWRrat hYV
      (Submodule.comap_mono hWV) hVne
  -- `s` is block diagonal
  have algSingle : ∀ (n : ℕ) (i : Fin n), StrongSix.Roy.AlgVec (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
    intro n i j; by_cases h : j = i
    · subst h; simpa using isAlgebraic_one
    · simpa [h] using isAlgebraic_zero
  have ratSingle : ∀ (n : ℕ) (i : Fin n), StrongSix.Roy.RatVec (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
    intro n i j; refine ⟨if j = i then 1 else 0, ?_⟩
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have hsmul1 : ∀ (n : ℕ) (i : Fin n) (x : ℂ), (Pi.single i x : Fin n → ℂ) = x • Pi.single i 1 := by
    intro n i x; ext j; by_cases h : j = i
    · subst h; simp
    · simp [h]
  have hb0 : ∀ u, (s (u, 0)).2 = 0 := by
    have hf : (LinearMap.snd ℂ _ _).comp (s.comp (LinearMap.inl ℂ (Fin k0 → ℂ) (Fin k1 → ℂ))) =
        0 := by
      refine LinearMap.pi_ext fun i x => ?_
      obtain ⟨u', -, hu'⟩ := hs0 (Pi.single i 1) (algSingle k0 i)
      have e : ((Pi.single i x : Fin k0 → ℂ), (0 : Fin k1 → ℂ)) =
          x • ((Pi.single i 1 : Fin k0 → ℂ), (0 : Fin k1 → ℂ)) := by
        rw [hsmul1 k0 i x]; simp
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply,
        LinearMap.zero_apply]
      rw [e, map_smul, hu']; simp
    intro u; exact LinearMap.congr_fun hf u
  have hb1 : ∀ v, (s (0, v)).1 = 0 := by
    have hf : (LinearMap.fst ℂ _ _).comp (s.comp (LinearMap.inr ℂ (Fin k0 → ℂ) (Fin k1 → ℂ))) =
        0 := by
      refine LinearMap.pi_ext fun i x => ?_
      obtain ⟨v', -, hv'⟩ := hs1 (Pi.single i 1) (ratSingle k1 i)
      have e : ((0 : Fin k0 → ℂ), (Pi.single i x : Fin k1 → ℂ)) =
          x • ((0 : Fin k0 → ℂ), (Pi.single i 1 : Fin k1 → ℂ)) := by
        rw [hsmul1 k1 i x]; simp
      simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply,
        LinearMap.zero_apply]
      rw [e, map_smul, hv']; simp
    intro v; exact LinearMap.congr_fun hf v
  have hsplit : ∀ x, s x = ((s (x.1, 0)).1, (s (0, x.2)).2) := by
    intro x
    have e : x = (x.1, 0) + (0, x.2) := by simp
    conv_lhs => rw [e, map_add]
    refine Prod.ext ?_ ?_
    · simp [hb1]
    · simp [hb0]
  let s₀ : (Fin k0 → ℂ) →ₗ[ℂ] (Fin d0' → ℂ) :=
    (LinearMap.fst ℂ _ _).comp (s.comp (LinearMap.inl ℂ (Fin k0 → ℂ) (Fin k1 → ℂ)))
  let s₁ : (Fin k1 → ℂ) →ₗ[ℂ] (Fin d1' → ℂ) :=
    (LinearMap.snd ℂ _ _).comp (s.comp (LinearMap.inr ℂ (Fin k0 → ℂ) (Fin k1 → ℂ)))
  have hs₀ : ∀ u, s₀ u = (s (u, 0)).1 := fun _ => rfl
  have hs₁ : ∀ v, s₁ v = (s (0, v)).2 := fun _ => rfl
  have hsx : ∀ x, s x = (s₀ x.1, s₁ x.2) := hsplit
  have hs₀surj : Function.Surjective s₀ := by
    intro u'; obtain ⟨x, hx⟩ := hsurj (u', 0)
    exact ⟨x.1, by have := congrArg Prod.fst (hsx x); rw [hx] at this; exact this.symm⟩
  have hs₁surj : Function.Surjective s₁ := by
    intro v'; obtain ⟨x, hx⟩ := hsurj (0, v')
    exact ⟨x.2, by have := congrArg Prod.snd (hsx x); rw [hx] at this; exact this.symm⟩
  -- the matrices of `s₀` (algebraic) and `s₁` (rational)
  have hc0 : ∀ j, ∃ u' : Fin d0' → ℂ, StrongSix.Roy.AlgVec u' ∧
      s ((Pi.single j 1 : Fin k0 → ℂ), 0) = (u', 0) := fun j => hs0 _ (algSingle k0 j)
  choose u' hu'alg hu' using hc0
  let S₀ : Matrix (Fin d0') (Fin k0) K11.Kq :=
    Matrix.of fun i j => ⟨u' j i, K11.mem_Kq.mpr (hu'alg j i)⟩
  have hS₀ : s₀ = (cmK K11.Kq S₀).mulVecLin := by
    refine LinearMap.pi_ext fun j x => ?_
    rw [hsmul1 k0 j x, map_smul, map_smul, hs₀, hu']
    ext i; simp only [cmK, S₀, Pi.smul_apply, smul_eq_mul, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, Matrix.of_apply]
    first | rfl | exact mul_comm _ _ | (simp only [Subfield.coe_subtype]; ring)
  have hc1 : ∀ j, ∃ v' : Fin d1' → ℂ, StrongSix.Roy.RatVec v' ∧
      s (0, (Pi.single j 1 : Fin k1 → ℂ)) = (0, v') := fun j => hs1 _ (ratSingle k1 j)
  choose v' hv'rat hv' using hc1
  choose qq hqq using hv'rat
  let R₁ : Matrix (Fin d1') (Fin k1) ℚ := Matrix.of fun i j => qq j i
  have hR₁ : s₁ = (K11.cm R₁).mulVecLin := by
    refine LinearMap.pi_ext fun j x => ?_
    rw [hsmul1 k1 j x, map_smul, map_smul, hs₁, hv']
    ext i; simp [K11.cm, R₁, Matrix.mulVec_single, hqq j i]
  -- the subgroup `H = ker s₀ × ker s₁ × 0`
  obtain ⟨Rinv, hSR⟩ := rightInv_of_surjective S₀ (by
    intro y; obtain ⟨u, hu⟩ := hs₀surj y; exact ⟨u, by rw [← hu, hS₀]; rfl⟩)
  have hker0 := ker_eq_span_cols S₀ Rinv hSR
  have h0rat : RationalOverQbar (LinearMap.ker s₀) := by
    apply le_antisymm
    · rw [hS₀, hker0]
      refine Submodule.span_mono ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨?_, fun i => K11.mem_Kq.mp (SetLike.coe_mem _)⟩
      exact Submodule.subset_span (Set.mem_range_self j)
    · rw [Submodule.span_le]; exact fun x hx => hx.1
  set U : Submodule ℚ (Fin k1 → ℚ) := Submodule.span ℚ (Set.range fun i : Fin d1' => fun j => R₁ i j)
    with hU
  have hrowv : ∀ v : Fin k1 → ℂ, ∀ i, (s₁ v) i = ∑ j, ((R₁ i j : ℚ) : ℂ) * v j := by
    intro v i; rw [hR₁]; simp [K11.cm, Matrix.mulVec, dotProduct]
  have htl : torusLie U = LinearMap.ker s₁ := by
    ext v
    simp only [torusLie, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      LinearMap.mem_ker]
    constructor
    · intro h; ext i; rw [hrowv]; exact h _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro h φ hφ
      induction hφ using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨i, rfl⟩ := hφ
        have := congrFun h i; rw [hrowv] at this; simpa using this
      | zero => simp
      | add a b _ _ ha hb => simp only [Pi.add_apply, Rat.cast_add, add_mul,
          Finset.sum_add_distrib, ha, hb, add_zero]
      | smul c a _ ha =>
        simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, mul_assoc]
        rw [← Finset.mul_sum, ha, mul_zero]
  have hli : LinearIndependent ℚ (fun i : Fin d1' => fun j => R₁ i j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i₀
    obtain ⟨v, hv⟩ := hs₁surj (Pi.single i₀ 1)
    have hz : ∀ j, ∑ i, c i * R₁ i j = 0 := by
      intro j; have := congrFun hc j; simpa [Finset.sum_apply] using this
    have h1 : ∑ i, ((c i : ℚ) : ℂ) * (s₁ v) i = ((c i₀ : ℚ) : ℂ) := by
      rw [hv]; simp [Pi.single_apply]
    have h2 : ∑ i, ((c i : ℚ) : ℂ) * (s₁ v) i = 0 := by
      simp only [hrowv, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : ∑ i, ((c i : ℚ) : ℂ) * (((R₁ i j : ℚ) : ℂ) * v j) =
          ((∑ i, c i * R₁ i j : ℚ) : ℂ) * v j := by
        push_cast; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, hz j]; simp
    exact_mod_cast h1.symm.trans h2
  have hUrank : finrank ℚ U = d1' := by
    rw [hU, finrank_span_eq_card hli, Fintype.card_fin]
  let H : SubgroupDataB k0 k1 B :=
    { h0 := LinearMap.ker s₀, U := U, t := ⊥, h0_rat := h0rat, t_rat := isRatSub_botB }
  have hkerT : H.tan = (LinearMap.ker s).map ε := by
    ext x
    simp only [H, SubgroupDataB.tan, tanOf, Submodule.mem_prod, htl, LinearMap.mem_ker,
      Submodule.mem_bot, Submodule.mem_map]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨(x.1, x.2.1), ?_, ?_⟩
      · rw [hsx]; simp [h1, h2]
      · rw [epsB_apply, ← h3]
    · rintro ⟨y, hy, rfl⟩
      rw [hsx] at hy
      exact ⟨congrArg Prod.fst hy, congrArg Prod.snd hy, rfl⟩
  -- `δ`
  have hfk0 : finrank ℂ (LinearMap.ker s₀) + d0' = k0 := by
    have := LinearMap.finrank_range_add_finrank_ker s₀
    rw [LinearMap.range_eq_top.mpr hs₀surj, finrank_top] at this
    simp only [Module.finrank_fin_fun] at this; omega
  have hδB : H.δBt ⊥ = d0' + d1' := by
    simp only [SubgroupDataB.δBt, SubgroupDataB.δ0, SubgroupDataB.δ1, H, hUrank, finrank_bot]
    omega
  -- `τ`
  have hWeq : W = WR.map ε := by rw [hWR, Submodule.map_comap_eq, inf_eq_right.mpr hWr]
  have hWinf : W ⊓ H.tan = (WR ⊓ LinearMap.ker s).map ε := by
    rw [Submodule.map_inf _ hεinj, ← hkerT, ← hWeq]
  have hτ : finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) = finrank ℂ ↥(WR.map s) := by
    have e1 := finrank_map_add_inf_ker s WR
    rw [hWinf, finrank_map_inj hεinj]
    omega
  have hWslt : finrank ℂ ↥(WR.map s) < d0' + d1' := by
    have := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hWs)
    rw [finrank_top] at this
    simpa [StrongSix.Roy.E, Module.finrank_prod, Module.finrank_fin_fun] using this
  -- ranks
  set Ωs := Submodule.span ℚ ((MEB.Per k0 k1 B : AddSubgroup (MEB.Tan k0 k1 B)) : Set (MEB.Tan k0 k1 B)) with hΩs
  set sq := s.restrictScalars ℚ with hsq
  set C := (LinearMap.ker s).restrictScalars ℚ ⊔ StrongSix.Roy.Omega k0 k1 with hC
  have hΩc : Ωs.comap εq = StrongSix.Roy.Omega k0 k1 := comap_span_perB
  have hcomapT : (H.tan.restrictScalars ℚ ⊔ Ωs).comap εq = C := by
    apply le_antisymm
    · intro x hx
      obtain ⟨t, ht, p, hp, htp⟩ := Submodule.mem_sup.mp (show εq x ∈ _ from hx)
      have ht' : t ∈ H.tan := ht
      rw [hkerT] at ht'
      obtain ⟨y, hy, rfl⟩ := ht'
      have hp' : p = ε (x - y) := by
        rw [map_sub]; change p = εq x - ε y; rw [← htp]; abel
      have hxy : x - y ∈ StrongSix.Roy.Omega k0 k1 := by
        rw [← hΩc]; change ε (x - y) ∈ Ωs; rw [← hp']; exact hp
      have : x = y + (x - y) := by abel
      rw [this]
      exact Submodule.add_mem_sup (show y ∈ (LinearMap.ker s).restrictScalars ℚ from hy) hxy
    · refine sup_le (fun y hy => ?_) ?_
      · have : ε y ∈ H.tan := by rw [hkerT]; exact ⟨y, hy, rfl⟩
        exact Submodule.mem_sup_left this
      · rw [← hΩc]; exact Submodule.comap_mono le_sup_right
  have hrk2 : finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ωs)) = finrank ℚ ↥(YR ⊓ C) := by
    rw [← finrank_comap_inj hεqinj (inf_le_left.trans hYqr), Submodule.comap_inf, hcomapT]
  have hrk3 : finrank ℚ ↥(Yq ⊓ Ωs) = finrank ℚ ↥(YR ⊓ StrongSix.Roy.Omega k0 k1) := by
    rw [← finrank_comap_inj hεqinj (inf_le_left.trans hYqr), Submodule.comap_inf, hΩc]
  -- `s⁻¹(Ω') = ker s + Ω`
  have hrowsT : LinearMap.ker R₁.transpose.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Matrix.mulVecLin_apply] at hc
    have := Fintype.linearIndependent_iff.mp hli c (by
      ext j; have := congrFun hc j
      simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using this)
    exact funext this
  have hR₁surj : ∀ q' : Fin d1' → ℚ, ∃ q, R₁.mulVec q = q' := by
    have hrk : R₁.rank = d1' := by
      rw [← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj
        (LinearMap.ker_eq_bot.mp hrowsT)]
      simp
    have htop : LinearMap.range R₁.mulVecLin = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [← Matrix.rank, hrk]; simp)
    intro q'
    obtain ⟨q, hq⟩ := (LinearMap.range_eq_top.mp htop) q'
    exact ⟨q, hq⟩
  have hsΩ : ∀ q : Fin k1 → ℚ, s ((0 : Fin k0 → ℂ), (2 * Real.pi * I : ℂ) • K11.castL k1 q) =
      (0, (2 * Real.pi * I : ℂ) • K11.castL d1' (R₁.mulVec q)) := by
    intro q
    rw [hsx]
    refine Prod.ext (by simp) ?_
    change s₁ _ = _
    rw [hR₁, Matrix.mulVecLin_apply, Matrix.mulVec_smul, K11.cm_mulVec_castL]
  have hcomapΩ' : (StrongSix.Roy.Omega d0' d1').comap sq = C := by
    apply le_antisymm
    · intro x hx
      obtain ⟨h1, q', hq'⟩ := mem_omega_iff.mp (show s x ∈ StrongSix.Roy.Omega d0' d1' from hx)
      obtain ⟨q, hq⟩ := hR₁surj q'
      set ω : StrongSix.Roy.E k0 k1 := ((0 : Fin k0 → ℂ), (2 * Real.pi * I : ℂ) • K11.castL k1 q)
      have hω : ω ∈ StrongSix.Roy.Omega k0 k1 := mem_omega_iff.mpr ⟨rfl, q, rfl⟩
      have hsω : s ω = s x := by
        rw [hsΩ, hq]; exact Prod.ext h1.symm hq'.symm
      have hk : x - ω ∈ (LinearMap.ker s).restrictScalars ℚ := by
        change s (x - ω) = 0; rw [map_sub, hsω, sub_self]
      have : x = (x - ω) + ω := by abel
      rw [this]; exact Submodule.add_mem_sup hk hω
    · refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · change s y ∈ StrongSix.Roy.Omega d0' d1'
        rw [show s y = 0 from hy]; exact Submodule.zero_mem _
      · obtain ⟨h1, q, hq⟩ := mem_omega_iff.mp hy
        change s y ∈ StrongSix.Roy.Omega d0' d1'
        have : y = ((0 : Fin k0 → ℂ), (2 * Real.pi * I : ℂ) • K11.castL k1 q) := Prod.ext h1 hq
        rw [this, hsΩ]
        exact mem_omega_iff.mpr ⟨rfl, _, rfl⟩
  have hkersq : LinearMap.ker sq = (LinearMap.ker s).restrictScalars ℚ := rfl
  have hlam : (finrank ℚ ↥(YR.map sq) : ℤ) - finrank ℚ ↥(YR.map sq ⊓ StrongSix.Roy.Omega d0' d1') =
      finrank ℚ YR - finrank ℚ ↥(YR ⊓ C) := by
    have e1 := finrank_map_add_inf_ker sq YR
    have : FiniteDimensional ℚ ↥(YR ⊓ C) := Submodule.finiteDimensional_of_le inf_le_left
    have e2 := finrank_map_add_inf_ker sq (YR ⊓ C)
    rw [← map_inf_comap, hcomapΩ']
    have e3 : YR ⊓ C ⊓ LinearMap.ker sq = YR ⊓ LinearMap.ker sq := by
      rw [inf_assoc, inf_eq_right.mpr (show LinearMap.ker sq ≤ C from le_sup_left)]
    rw [e3] at e2
    omega
  -- assemble
  have hrkY : rk Y = finrank ℚ Yq := rfl
  have hrkT : rk (Y ⊓ (H.tan.toAddSubgroup ⊔ MEB.Per k0 k1 B)) =
      finrank ℚ ↥(Yq ⊓ (H.tan.restrictScalars ℚ ⊔ Ωs)) := by
    rw [rk, K11.span_inf_addSubgroup, K11.span_sup_addSubgroup, K11.span_submodule_coe]
  have hrkP : rk (Y ⊓ MEB.Per k0 k1 B) = finrank ℚ ↥(Yq ⊓ Ωs) := by
    rw [rk, K11.span_inf_addSubgroup]
  have hle1 : finrank ℚ ↥(YR ⊓ C) ≤ finrank ℚ YR := Submodule.finrank_mono inf_le_left
  refine ⟨H, le_refl _, by omega, ?_, ?_⟩
  · rw [hτ, hδB]; exact hWslt
  · rw [hτ, hδB, hrkY, hrkT, hrkP, hrk2, hrk3, ← hfYR, finrank_bot]
    have hδ1 : H.δ1 = d1' := hUrank
    rw [hδ1]
    have hpos1 : (0 : ℚ) < (d0' + d1' : ℚ) - finrank ℂ ↥(WR.map s) := by
      have : ((finrank ℂ ↥(WR.map s) : ℕ) : ℚ) < ((d0' + d1' : ℕ) : ℚ) := by exact_mod_cast hWslt
      push_cast at this; linarith
    have hpos2 : (0 : ℚ) < (k0 + k1 : ℚ) - finrank ℂ VR := by
      have : ((finrank ℂ VR : ℕ) : ℚ) < ((k0 + k1 : ℕ) : ℚ) := by rw [hfVR]; exact_mod_cast hdim
      push_cast at this; linarith
    rw [div_le_div_iff₀ hpos1 hpos2] at hratio
    have hlamQ : (finrank ℚ ↥(YR.map sq) : ℚ) =
        finrank ℚ ↥(YR.map sq ⊓ StrongSix.Roy.Omega d0' d1') + finrank ℚ YR - finrank ℚ ↥(YR ⊓ C) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hlam
      push_cast at this; linarith
    rw [hlamQ, hfVR] at hratio
    have key : (((finrank ℚ YR - finrank ℚ ↥(YR ⊓ C) + d1' + 2 * (0 - 0) : ℕ) : ℤ) : ℚ) *
        (((k0 + k1 + 0 : ℕ) : ℤ) - (finrank ℂ V : ℤ) : ℚ) ≤
        ((((d0' + d1' : ℕ) : ℤ) - ((finrank ℂ ↥(WR.map s) : ℕ) : ℤ) : ℤ) : ℚ) *
          ((((k1 + 2 * 0 : ℕ) : ℤ) - (finrank ℚ ↥(YR ⊓ StrongSix.Roy.Omega k0 k1) : ℤ) : ℤ) : ℚ) := by
      push_cast [Nat.cast_sub hle1]
      nlinarith [hratio]
    exact_mod_cast key

/-- **`Thm41SubAtB` for `t = 0`** (Roy). -/
theorem thm41SubAtB_bot (An : ∀ k, AbBlockAn (B k)) (k0 k1 : ℕ) :
    Thm41SubAtB An k0 k1 (⊥ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) := by
  intro V W Y hVT hdim hWV hWrat hYfg hY _ _
  exact sub41ConclB_bot An V W Y hVT (by simpa using hdim) hWV hWrat hYfg hY

end LSG.W88
