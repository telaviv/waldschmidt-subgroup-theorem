/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.K5dRoy
import LSG.W88.MStarCopyStd

/-!
# The standard model `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`: logarithms, periods, ranks

* `lamSub`: `Lam Ls` is an additive subgroup (group law of each `E_j`).
* `Ωs`: the `ℚ`-span of the periods; `mem_Ωs`: its elements are `(0, 2πi q, z)` with `q ∈ ℚ^{d₁}`
  and `z ∈ latQ` (the `ℚ`-span of `Λ₁ × ⋯ × Λ_m`); `dim Ωs ≤ d₁ + 2m`.
* `finrank_Ωs_inf_ge`: `dim (Ωs ∩ T_H) ≥ dim T_U^⊥ + 2 dim t` for every `SubgroupData H`.
* `finrank_le_real`: for `K ⊂ latQ`, `dim_ℚ K ≤ dim_ℝ span_ℝ K` (`ℚ`-independent lattice vectors are
  `ℝ`-independent).
-/

open Complex Module

namespace LSG.W88.K5d

variable {d0 d1 m : ℕ}

/-! ### `Lam` is a subgroup -/

section Lam

variable (L : PeriodPair)

lemma lam_coord_iff (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) (z : ℂ) :
    (z ∈ L.lattice ∨ IsAlgebraic ℚ (L.weierstrassP z)) ↔
      LSG.Weierstrass.expE L z ∈ LSG.Weierstrass.ratPoints L K11.Kq (K11.mem_Kq.mpr hg₂) := by
  constructor
  · rintro (h | h)
    · rw [LSG.Weierstrass.expE_of_mem L h]; exact AddSubgroup.zero_mem _
    · by_cases hz : z ∈ L.lattice
      · rw [LSG.Weierstrass.expE_of_mem L hz]; exact AddSubgroup.zero_mem _
      have hd : IsAlgebraic ℚ (L.derivWeierstrassP z) := by
        refine IsAlgebraic.of_pow (n := 2) two_pos ?_
        rw [L.derivWeierstrassP_sq z hz, ← K11.mem_Kq]
        have h1 := K11.mem_Kq.mpr h
        exact K11.Kq.sub_mem (K11.Kq.sub_mem (K11.Kq.mul_mem (by simp) (K11.Kq.pow_mem h1 3))
          (K11.Kq.mul_mem (K11.mem_Kq.mpr hg₂) h1)) (K11.mem_Kq.mpr hg₃)
      intro x y' hh hP
      rw [LSG.Weierstrass.expE_of_notMem L hz] at hP
      simp only [WeierstrassCurve.Affine.Point.some.injEq] at hP
      obtain ⟨rfl, rfl⟩ := hP
      exact ⟨K11.mem_Kq.mpr h, K11.Kq.div_mem (K11.mem_Kq.mpr hd) (by simp)⟩
  · intro h
    by_cases hz : z ∈ L.lattice
    · exact Or.inl hz
    · exact Or.inr (K11.mem_Kq.mp (h _ _ _ (LSG.Weierstrass.expE_of_notMem L hz)).1)

end Lam

/-- `Lam Ls` as an additive subgroup (curves with algebraic invariants). -/
noncomputable def lamSub (Ls : Fin m → PeriodPair)
    (hLs : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) :
    AddSubgroup (Tan d0 d1 m) where
  carrier := Lam Ls
  add_mem' {a b} ha hb := by
    refine ⟨fun i => ?_, fun i => ?_, fun j => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, ← K11.mem_Kq]
      exact K11.Kq.add_mem (K11.mem_Kq.mpr (ha.1 i)) (K11.mem_Kq.mpr (hb.1 i))
    · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Complex.exp_add, ← K11.mem_Kq]
      exact K11.Kq.mul_mem (K11.mem_Kq.mpr (ha.2.1 i)) (K11.mem_Kq.mpr (hb.2.1 i))
    · have h1 := (lam_coord_iff (Ls j) (hLs j).1 (hLs j).2 _).mp (ha.2.2 j)
      have h2 := (lam_coord_iff (Ls j) (hLs j).1 (hLs j).2 _).mp (hb.2.2 j)
      refine (lam_coord_iff (Ls j) (hLs j).1 (hLs j).2 _).mpr ?_
      simp only [Prod.snd_add, Pi.add_apply, LSG.Weierstrass.expE_add]
      exact AddSubgroup.add_mem _ h1 h2
  zero_mem' := ⟨fun i => by simpa using isAlgebraic_zero, fun i => by simpa using isAlgebraic_one,
    fun j => Or.inl (Ls j).lattice.zero_mem⟩
  neg_mem' {a} ha := by
    refine ⟨fun i => ?_, fun i => ?_, fun j => ?_⟩
    · simp only [Prod.fst_neg, Pi.neg_apply, ← K11.mem_Kq]
      exact K11.Kq.neg_mem (K11.mem_Kq.mpr (ha.1 i))
    · simp only [Prod.snd_neg, Prod.fst_neg, Pi.neg_apply, Complex.exp_neg, ← K11.mem_Kq]
      exact K11.Kq.inv_mem (K11.mem_Kq.mpr (ha.2.1 i))
    · have h1 := (lam_coord_iff (Ls j) (hLs j).1 (hLs j).2 _).mp (ha.2.2 j)
      refine (lam_coord_iff (Ls j) (hLs j).1 (hLs j).2 _).mpr ?_
      simp only [Prod.snd_neg, Pi.neg_apply, LSG.Weierstrass.expE_neg]
      exact AddSubgroup.neg_mem _ h1

/-! ### The period space -/

variable (Ls : Fin m → PeriodPair)

/-- `Ω_ℚ = span_ℚ Per`. -/
noncomputable abbrev Ωs (d0 d1 : ℕ) : Submodule ℚ (Tan d0 d1 m) :=
  Submodule.span ℚ ((Per (d0 := d0) (d1 := d1) Ls : AddSubgroup (Tan d0 d1 m)) : Set (Tan d0 d1 m))

/-- The `ℚ`-span of `Λ₁ × ⋯ × Λ_m`. -/
noncomputable def latQ : Submodule ℚ (Fin m → ℂ) :=
  Submodule.span ℚ {z | ∀ j, z j ∈ (Ls j).lattice}

/-- `(p, p') ↦ (p_j ω₁ʲ + p'_j ω₂ʲ)_j` on `ℚ^{m×2}`. -/
noncomputable def PhiE : (Fin m × Fin 2 → ℚ) →ₗ[ℚ] (Fin m → ℂ) where
  toFun p := fun j => (p (j, 0) : ℂ) * (Ls j).ω₁ + (p (j, 1) : ℂ) * (Ls j).ω₂
  map_add' p q := by funext j; simp; ring
  map_smul' c p := by funext j; simp [Rat.smul_def]; ring

lemma latQ_le_range : latQ Ls ≤ LinearMap.range (PhiE Ls) := by
  rw [latQ, Submodule.span_le]
  intro z hz
  choose a b hab using fun j => PeriodPair.mem_lattice.mp (hz j)
  refine ⟨fun x => if x.2 = 0 then (a x.1 : ℚ) else (b x.1 : ℚ), ?_⟩
  funext j; simp [PhiE, ← hab j]

instance : FiniteDimensional ℚ (latQ Ls) := by
  have : FiniteDimensional ℚ (LinearMap.range (PhiE Ls)) := inferInstance
  exact Submodule.finiteDimensional_of_le (latQ_le_range Ls)

/-- `z ↦ (0, 0, z)`. -/
noncomputable def inE (d0 d1 : ℕ) : (Fin m → ℂ) →ₗ[ℚ] Tan d0 d1 m :=
  (LinearMap.inr ℚ _ _).comp (LinearMap.inr ℚ (Fin d1 → ℂ) (Fin m → ℂ))

/-- `q ↦ (0, 2πi q, 0)`. -/
noncomputable def inT (d0 d1 : ℕ) : (Fin d1 → ℚ) →ₗ[ℚ] Tan d0 d1 m :=
  (LinearMap.inr ℚ _ _).comp ((LinearMap.inl ℚ (Fin d1 → ℂ) (Fin m → ℂ)).comp
    ((2 * Real.pi * I : ℂ) • (K11.castL d1).restrictScalars ℚ))

lemma inT_apply (q : Fin d1 → ℚ) :
    inT (m := m) d0 d1 q = (0, (2 * Real.pi * I : ℂ) • K11.castL d1 q, 0) := rfl
lemma inE_apply (z : Fin m → ℂ) : inE d0 d1 z = ((0 : Fin d0 → ℂ), (0 : Fin d1 → ℂ), z) := rfl

lemma inT_injective : Function.Injective (inT (m := m) d0 d1) := by
  intro q q' h
  have := congrArg (fun p => p.2.1) h
  simp only [inT_apply] at this
  exact K11.castL_injective d1 (smul_right_injective _ K11.two_pi_I_ne_zero this)

lemma inE_injective : Function.Injective (inE (m := m) d0 d1) := by
  intro z z' h; exact congrArg (fun p => p.2.2) h

lemma mem_Ωs {x : Tan d0 d1 m} (hx : x ∈ Ωs Ls d0 d1) :
    ∃ q z, z ∈ latQ Ls ∧ x = inT d0 d1 q + inE d0 d1 z := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h1, h2, h3⟩ := hx
    choose kv hkv using h2
    refine ⟨fun i => (kv i : ℚ), x.2.2, Submodule.subset_span h3, ?_⟩
    refine Prod.ext (by simp [inT_apply, inE_apply, h1]) (Prod.ext ?_ (by simp [inT_apply,
      inE_apply]))
    ext i; simp [inT_apply, inE_apply, hkv i, mul_comm]
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨q, z, hz, rfl⟩ := hx
    obtain ⟨q', z', hz', rfl⟩ := hy
    exact ⟨q + q', z + z', Submodule.add_mem _ hz hz', by rw [map_add, map_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨q, z, hz, rfl⟩ := hx
    exact ⟨c • q, c • z, Submodule.smul_mem _ _ hz, by rw [map_smul, map_smul, smul_add]⟩

lemma inT_mem_Ωs (q : Fin d1 → ℚ) : inT d0 d1 q ∈ Ωs Ls d0 d1 := by
  have : inT (m := m) d0 d1 q = ∑ j, q j • ((0 : Fin d0 → ℂ),
      (Pi.single j (2 * Real.pi * I) : Fin d1 → ℂ), (0 : Fin m → ℂ)) := by
    rw [inT_apply]
    refine Prod.ext (by simp [Prod.fst_sum]) (Prod.ext ?_ (by simp [Prod.snd_sum]))
    ext i; simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply, Rat.smul_def,
      mul_comm]
  rw [this]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨rfl, fun i => ⟨if i = j then 1 else 0, ?_⟩, fun _ => (Ls _).lattice.zero_mem⟩
  change (Pi.single j (2 * Real.pi * I) : Fin d1 → ℂ) i = _
  by_cases h : i = j
  · subst h; simp
  · simp [h]

lemma inE_mem_Ωs {z : Fin m → ℂ} (hz : z ∈ latQ Ls) : inE d0 d1 z ∈ Ωs Ls d0 d1 := by
  have : (latQ Ls).map (inE d0 d1) ≤ Ωs Ls d0 d1 := by
    rw [latQ, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact Submodule.subset_span ⟨rfl, fun _ => ⟨0, by simp [inE_apply]⟩, hw⟩
  exact this ⟨z, hz, rfl⟩

lemma Ωs_le_range : Ωs Ls d0 d1 ≤ LinearMap.range ((inT (m := m) d0 d1).coprod
    ((inE d0 d1).comp (PhiE Ls))) := by
  intro x hx
  obtain ⟨q, z, hz, rfl⟩ := mem_Ωs Ls hx
  obtain ⟨p, rfl⟩ := latQ_le_range Ls hz
  exact ⟨(q, p), by simp⟩

instance : FiniteDimensional ℚ (Ωs Ls d0 d1) :=
  Submodule.finiteDimensional_of_le (Ωs_le_range Ls)

lemma finrank_Ωs_le : finrank ℚ (Ωs Ls d0 d1) ≤ d1 + 2 * m := by
  refine (Submodule.finrank_mono (Ωs_le_range Ls)).trans ((LinearMap.finrank_range_le _).trans ?_)
  simp [Module.finrank_prod]; ring_nf; omega

/-! ### Real versus rational dimensions -/

lemma linIndep_cast {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [CharZero F]
    {r : ℕ} (c : Fin r → ι → ℚ) (hc : LinearIndependent ℚ c) :
    LinearIndependent F (fun i j => ((c i j : ℚ) : F)) := by
  classical
  let M : Matrix ι (Fin r) ℚ := Matrix.of fun j i => c i j
  have hM : ∀ a, M.mulVec a = ∑ i, a i • c i := by
    intro a; ext j; simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinj : LinearMap.ker M.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha; rw [Matrix.mulVecLin_apply, hM] at ha
    exact funext (Fintype.linearIndependent_iff.mp hc a ha)
  obtain ⟨g, hg⟩ := M.mulVecLin.exists_leftInverse_of_injective hinj
  have hDM : LinearMap.toMatrix' g * M = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin'] at this
  have hDMc : (LinearMap.toMatrix' g).map (Rat.castHom F) * M.map (Rat.castHom F) = 1 := by
    rw [← Matrix.map_mul, hDM]; simp
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h1 : (M.map (Rat.castHom F)).mulVec a = 0 := by
    rw [← ha]; ext j; simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have := congrArg ((LinearMap.toMatrix' g).map (Rat.castHom F)).mulVec h1
  rw [Matrix.mulVec_mulVec, hDMc, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  exact fun i => congrFun this i

/-- `(a, b) ↦ (a_j ω₁ʲ + b_j ω₂ʲ)_j` on `ℝ^{m×2}`: injective. -/
noncomputable def PsiR : (Fin m × Fin 2 → ℝ) →ₗ[ℝ] (Fin m → ℂ) where
  toFun p := fun j => (p (j, 0) : ℂ) * (Ls j).ω₁ + (p (j, 1) : ℂ) * (Ls j).ω₂
  map_add' p q := by funext j; simp; ring
  map_smul' c p := by funext j; simp [Complex.real_smul]; ring

lemma psiR_injective : Function.Injective (PsiR Ls) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  funext x
  obtain ⟨j, i⟩ := x
  have h := congrFun hp j
  have := LinearIndependent.pair_iff.mp (Ls j).indep (p (j, 0)) (p (j, 1)) (by
    simpa [PsiR, Complex.real_smul] using h)
  fin_cases i
  · exact this.1
  · exact this.2

/-- For `K ⊂ latQ`, `dim_ℚ K ≤ dim_ℝ span_ℝ K`. -/
lemma finrank_le_real (K : Submodule ℚ (Fin m → ℂ)) (hK : K ≤ latQ Ls) :
    finrank ℚ K ≤ finrank ℝ (Submodule.span ℝ (K : Set (Fin m → ℂ))) := by
  classical
  have : FiniteDimensional ℚ K := Submodule.finiteDimensional_of_le hK
  let b := Module.finBasis ℚ K
  have hb : ∀ i, ∃ c, PhiE Ls c = (b i : Fin m → ℂ) := fun i => latQ_le_range Ls (hK (b i).2)
  choose c hc using hb
  have hbli : LinearIndependent ℚ (fun i => (b i : Fin m → ℂ)) :=
    b.linearIndependent.map' K.subtype (Submodule.ker_subtype K)
  have hcli : LinearIndependent ℚ c := by
    have : (fun i => (b i : Fin m → ℂ)) = (PhiE Ls) ∘ c := funext fun i => (hc i).symm
    rw [this] at hbli
    exact hbli.of_comp _
  have hR := linIndep_cast (F := ℝ) c hcli
  have hR2 : LinearIndependent ℝ (fun i => (b i : Fin m → ℂ)) := by
    have : (fun i => (b i : Fin m → ℂ)) = (PsiR Ls) ∘ (fun i j => ((c i j : ℚ) : ℝ)) := by
      funext i j; rw [← hc i]; simp [PsiR, PhiE]
    rw [this]
    exact hR.map' (PsiR Ls) (LinearMap.ker_eq_bot.mpr (psiR_injective Ls))
  have h1 := finrank_span_eq_card hR2
  rw [Fintype.card_fin] at h1
  have hle : Submodule.span ℝ (Set.range fun i => (b i : Fin m → ℂ)) ≤
      Submodule.span ℝ (K : Set (Fin m → ℂ)) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact (b i).2)
  rw [← h1]
  exact Submodule.finrank_mono hle

/-! ### Dimensions of subgroups -/

/-- `p × q ≃ p.prod q`. -/
def prodSubEquiv {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
    [Module R N] (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1, y.2), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma finrank_prodSub {R M N : Type*} [Ring R] [StrongRankCondition R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (p : Submodule R M) (q : Submodule R N)
    [Module.Free R p] [Module.Free R q] [Module.Finite R p] [Module.Finite R q] :
    finrank R ↥(p.prod q) = finrank R p + finrank R q := by
  rw [LinearEquiv.finrank_eq (prodSubEquiv p q), Module.finrank_prod]

lemma finrank_tan (H : SubgroupData (d0 := d0) (d1 := d1) Ls) :
    finrank ℂ H.tan = finrank ℂ H.h0 + finrank ℂ (torusLie H.U) + finrank ℂ H.t := by
  rw [SubgroupData.tan, finrank_prodSub, finrank_prodSub, add_assoc]

lemma torusLie_eq_annC (U : Submodule ℚ (Fin d1 → ℚ)) : torusLie U = K11.annC U := rfl

lemma finrank_torusLie (U : Submodule ℚ (Fin d1 → ℚ)) :
    finrank ℂ (torusLie U) + finrank ℚ U = d1 := K11.finrank_annC U

lemma castL_mem_torusLie_iff {U : Submodule ℚ (Fin d1 → ℚ)} {q : Fin d1 → ℚ} :
    (2 * Real.pi * I : ℂ) • K11.castL d1 q ∈ torusLie U ↔ q ∈ K11.annQ U := by
  rw [torusLie_eq_annC, K11.annC_eq_cspan]
  constructor
  · intro h
    apply K11.mem_of_castL_mem_cspan
    have := Submodule.smul_mem _ (2 * Real.pi * I : ℂ)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ K11.two_pi_I_ne_zero, one_smul] at this
  · intro h; exact Submodule.smul_mem _ _ (K11.castL_mem_cspan h)

/-- The lattice points of an abelian tangent space, `ℚ`-spanned. -/
noncomputable def latT (t : Submodule ℂ (Fin m → ℂ)) : Submodule ℚ (Fin m → ℂ) :=
  Submodule.span ℚ {z | z ∈ t ∧ ∀ j, z j ∈ (Ls j).lattice}

lemma latT_le_latQ (t : Submodule ℂ (Fin m → ℂ)) : latT Ls t ≤ latQ Ls :=
  Submodule.span_mono fun _ hz => hz.2

lemma latT_le (t : Submodule ℂ (Fin m → ℂ)) : latT Ls t ≤ t.restrictScalars ℚ :=
  Submodule.span_le.mpr fun _ hz => hz.1

lemma finrank_real_restrict (t : Submodule ℂ (Fin m → ℂ)) :
    finrank ℝ (t.restrictScalars ℝ) = 2 * finrank ℂ t :=
  finrank_real_of_complex ↥t

lemma two_mul_le_finrank_latT {t : Submodule ℂ (Fin m → ℂ)} (ht : IsAbelianTangent Ls t) :
    2 * finrank ℂ t ≤ finrank ℚ (latT Ls t) := by
  classical
  have : FiniteDimensional ℚ (latT Ls t) := Submodule.finiteDimensional_of_le (latT_le_latQ Ls t)
  let b := Module.finBasis ℚ (latT Ls t)
  have hspan : Submodule.span ℝ {z | z ∈ t ∧ ∀ j, z j ∈ (Ls j).lattice} ≤
      Submodule.span ℝ (Set.range fun i => (b i : Fin m → ℂ)) := by
    rw [Submodule.span_le]
    intro z hz
    have hz' : z ∈ latT Ls t := Submodule.subset_span hz
    have h1 : z ∈ Submodule.span ℚ (Set.range fun i => (b i : Fin m → ℂ)) := by
      have := congrArg Subtype.val (b.sum_repr ⟨z, hz'⟩)
      rw [Submodule.coe_sum] at this
      change _ = z at this
      rw [← this]
      exact Submodule.sum_mem _ fun i _ => by
        rw [Submodule.coe_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact Submodule.span_le_restrictScalars ℚ ℝ _ h1
  rw [← finrank_real_restrict, ht]
  refine (Submodule.finrank_mono hspan).trans ((finrank_range_le_card _).trans ?_)
  simp

/-- `dim (Ω_ℚ ∩ T_H) ≥ dim T_U^⊥ + 2 dim t`. -/
lemma finrank_Ωs_inf_ge (H : SubgroupData (d0 := d0) (d1 := d1) Ls) :
    finrank ℂ (torusLie H.U) + 2 * finrank ℂ H.t ≤
      finrank ℚ ↥(Ωs Ls d0 d1 ⊓ H.tan.restrictScalars ℚ) := by
  classical
  set A := (K11.annQ H.U).map (inT (m := m) d0 d1) with hA
  set B := (latT Ls H.t).map (inE (m := m) d0 d1) with hB
  have hAle : A ≤ Ωs Ls d0 d1 ⊓ H.tan.restrictScalars ℚ := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨inT_mem_Ωs Ls q, ?_⟩
    change inT d0 d1 q ∈ H.tan
    rw [inT_apply, SubgroupData.tan, Submodule.mem_prod, Submodule.mem_prod]
    exact ⟨H.h0.zero_mem, castL_mem_torusLie_iff.mpr hq, H.t.zero_mem⟩
  have hBle : B ≤ Ωs Ls d0 d1 ⊓ H.tan.restrictScalars ℚ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨inE_mem_Ωs Ls (latT_le_latQ Ls _ hz), ?_⟩
    change inE d0 d1 z ∈ H.tan
    rw [inE_apply, SubgroupData.tan, Submodule.mem_prod, Submodule.mem_prod]
    exact ⟨H.h0.zero_mem, (torusLie H.U).zero_mem, latT_le Ls _ hz⟩
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨q, -, rfl⟩, ⟨z, -, hz⟩⟩
    have h2 : (inE (m := m) d0 d1 z).2.1 = (inT d0 d1 q).2.1 := congrArg (fun p => p.2.1) hz
    have h2' : (2 * Real.pi * I : ℂ) • K11.castL d1 q = 0 := by
      simpa [inT_apply, inE_apply] using h2.symm
    rw [Submodule.mem_bot, inT_apply, h2']; rfl
  have : FiniteDimensional ℚ (latT Ls H.t) :=
    Submodule.finiteDimensional_of_le (latT_le_latQ Ls _)
  have hfA : finrank ℚ A = finrank ℂ (torusLie H.U) := by
    rw [hA, finrank_map_inj inT_injective]
    have h1 := K11.finrank_annQ H.U
    have h2 := finrank_torusLie H.U
    omega
  have hfB : 2 * finrank ℂ H.t ≤ finrank ℚ B := by
    rw [hB, finrank_map_inj inE_injective]; exact two_mul_le_finrank_latT Ls H.t_ab
  have e := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hAB, finrank_bot] at e
  have hle := Submodule.finrank_mono (sup_le hAle hBle)
  omega

/-- `torusLie ⊤ = 0`. -/
lemma torusLie_top : torusLie (⊤ : Submodule ℚ (Fin d1 → ℚ)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  funext j
  have := hv (Pi.single j 1) Submodule.mem_top
  simpa [Pi.single_apply, apply_ite (fun x : ℚ => (x : ℂ)), ite_mul] using this

lemma rational_bot {n : ℕ} : RationalOverQbar (⊥ : Submodule ℂ (Fin n → ℂ)) :=
  le_antisymm bot_le (Submodule.span_le.mpr fun _ hw => hw.1)

/-- The subgroup `0 × 0 × B` for an abelian tangent `t`. -/
def abSub (t : Submodule ℂ (Fin m → ℂ)) (ht : IsAbelianTangent Ls t) :
    SubgroupData (d0 := d0) (d1 := d1) Ls :=
  { h0 := ⊥, U := ⊤, t := t, h0_rat := rational_bot, t_ab := ht }

lemma abSub_tan (t : Submodule ℂ (Fin m → ℂ)) (ht : IsAbelianTangent Ls t) :
    (abSub (d0 := d0) (d1 := d1) Ls t ht).tan =
      (⊥ : Submodule ℂ (Fin d0 → ℂ)).prod ((⊥ : Submodule ℂ (Fin d1 → ℂ)).prod t) := by
  rw [SubgroupData.tan, abSub, torusLie_top]

/-- **The (NR) corner with a nonzero abelian part.** If `X ⊂ Ω_ℚ ∩ T_H ∩ V` has dimension
`≥ dim T_U^⊥ + 2 dim t − 1` with `t ≠ 0`, then `V ⊇ 0 × 0 × t`, a nonzero algebraic subgroup. -/
lemma corner_false (V : Submodule ℂ (Tan d0 d1 m))
    (hno : ∀ H : SubgroupData (d0 := d0) (d1 := d1) Ls, H.tan ≤ V → H.tan = ⊥)
    (H : SubgroupData (d0 := d0) (d1 := d1) Ls) (hb : 1 ≤ finrank ℂ H.t)
    (X : Submodule ℚ (Tan d0 d1 m)) (hXΩ : X ≤ Ωs Ls d0 d1 ⊓ H.tan.restrictScalars ℚ)
    (hXV : X ≤ V.restrictScalars ℚ)
    (hX : finrank ℂ (torusLie H.U) + 2 * finrank ℂ H.t ≤ finrank ℚ X + 1) : False := by
  classical
  have : FiniteDimensional ℚ X := Submodule.finiteDimensional_of_le (hXΩ.trans inf_le_left)
  let p₂ : Tan d0 d1 m →ₗ[ℚ] (Fin d1 → ℂ) := (LinearMap.fst ℚ _ _).comp (LinearMap.snd ℚ _ _)
  let p₃ : Tan d0 d1 m →ₗ[ℚ] (Fin m → ℂ) := (LinearMap.snd ℚ _ _).comp (LinearMap.snd ℚ _ _)
  -- the toric image has dimension `≤ dim T_U^⊥`
  have hdec : ∀ x ∈ X, ∃ q z, q ∈ K11.annQ H.U ∧ z ∈ latQ Ls ∧ x = inT d0 d1 q + inE d0 d1 z := by
    intro x hx
    obtain ⟨q, z, hz, rfl⟩ := mem_Ωs Ls (hXΩ hx).1
    refine ⟨q, z, ?_, hz, rfl⟩
    have h := (hXΩ hx).2
    change inT d0 d1 q + inE d0 d1 z ∈ H.tan at h
    rw [SubgroupData.tan, Submodule.mem_prod, Submodule.mem_prod] at h
    have h2 := h.2.1
    simp only [inT_apply, inE_apply, Prod.snd_add, Prod.fst_add, add_zero] at h2
    exact castL_mem_torusLie_iff.mp h2
  let g : (Fin d1 → ℚ) →ₗ[ℚ] (Fin d1 → ℂ) :=
    (2 * Real.pi * I : ℂ) • (K11.castL d1).restrictScalars ℚ
  have himg : X.map p₂ ≤ (K11.annQ H.U).map g := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, z, hq, -, rfl⟩ := hdec x hx
    exact ⟨q, hq, by simp [g, p₂, inT_apply, inE_apply]⟩
  have hgdim : finrank ℚ ↥((K11.annQ H.U).map g) ≤ finrank ℂ (torusLie H.U) := by
    have h1 := K11.finrank_annQ H.U
    have h2 := finrank_torusLie H.U
    have h3 := Submodule.finrank_map_le g (K11.annQ H.U)
    omega
  set K₁ := X ⊓ LinearMap.ker p₂ with hK₁
  have : FiniteDimensional ℚ K₁ := Submodule.finiteDimensional_of_le inf_le_left
  have hK₁dim : finrank ℚ X ≤ finrank ℚ K₁ + finrank ℂ (torusLie H.U) := by
    have e1 := finrank_map_add_inf_ker p₂ X
    rw [← hK₁] at e1
    have e2 := Submodule.finrank_mono himg
    omega
  set K := K₁.map p₃ with hK
  have hKinj : K₁ ⊓ LinearMap.ker p₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxX, hx2⟩, hx3⟩
    obtain ⟨q, z, -, -, rfl⟩ := hdec _ hxX
    rw [Submodule.mem_bot]
    have h2 : (inT d0 d1 q + inE d0 d1 z).2.1 = 0 := hx2
    have h3 : (inT d0 d1 q + inE d0 d1 z).2.2 = 0 := hx3
    refine Prod.ext ?_ (Prod.ext h2 h3)
    simp [inT_apply, inE_apply]
  have hKdim : finrank ℚ K = finrank ℚ K₁ := by
    have := finrank_map_add_inf_ker p₃ K₁
    rw [hKinj, finrank_bot] at this; omega
  have hKlat : K ≤ latQ Ls := by
    rintro _ ⟨x, ⟨hxX, hx2⟩, rfl⟩
    obtain ⟨q, z, -, hz, rfl⟩ := hdec _ hxX
    simpa [p₃, inT_apply, inE_apply] using hz
  have hKt : K ≤ H.t.restrictScalars ℚ := by
    rintro _ ⟨x, ⟨hxX, -⟩, rfl⟩
    have h := (hXΩ hxX).2
    change x ∈ H.tan at h
    rw [SubgroupData.tan, Submodule.mem_prod, Submodule.mem_prod] at h
    exact h.2.2
  have hKV : ∀ z ∈ K, ((0 : Fin d0 → ℂ), (0 : Fin d1 → ℂ), z) ∈ V := by
    rintro _ ⟨x, ⟨hxX, hx2⟩, rfl⟩
    obtain ⟨q, z, -, -, rfl⟩ := hdec _ hxX
    have hq : (2 * Real.pi * I : ℂ) • K11.castL d1 q = 0 := by
      have : (inT d0 d1 q + inE d0 d1 z).2.1 = 0 := hx2
      simpa [inT_apply, inE_apply] using this
    have : inT d0 d1 q + inE d0 d1 z = ((0 : Fin d0 → ℂ), (0 : Fin d1 → ℂ), z) := by
      rw [inT_apply, inE_apply, hq]; simp
    have hv := hXV hxX
    rw [this] at hv ⊢
    simpa [p₃] using hv
  -- `span_ℂ K = t`
  set S := Submodule.span ℂ (K : Set (Fin m → ℂ)) with hS
  have hSt : S ≤ H.t := Submodule.span_le.mpr fun z hz => hKt hz
  have hreal : finrank ℚ K ≤ 2 * finrank ℂ S := by
    refine (finrank_le_real Ls K hKlat).trans ?_
    rw [← finrank_real_restrict]
    refine Submodule.finrank_mono ?_
    rw [Submodule.span_le]; intro z hz; exact Submodule.subset_span hz
  have hSdim : finrank ℂ S ≤ finrank ℂ H.t := Submodule.finrank_mono hSt
  have hSeq : S = H.t := Submodule.eq_of_le_of_finrank_eq hSt (by omega)
  -- `0 × 0 × t ⊂ V`
  have hle : (abSub (d0 := d0) (d1 := d1) Ls H.t H.t_ab).tan ≤ V := by
    rw [abSub_tan]
    rintro ⟨a, v, z⟩ hx
    rw [Submodule.mem_prod, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_bot] at hx
    obtain ⟨rfl, rfl, hz⟩ := hx
    rw [← hSeq] at hz
    let ι₃ : (Fin m → ℂ) →ₗ[ℂ] Tan d0 d1 m :=
      (LinearMap.inr ℂ _ _).comp (LinearMap.inr ℂ (Fin d1 → ℂ) (Fin m → ℂ))
    have : S.map ι₃ ≤ V := by
      rw [hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩; exact hKV w hw
    exact this ⟨z, hz, rfl⟩
  have hbot := hno _ hle
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (fun h => by
    rw [h, finrank_bot] at hb; omega : H.t ≠ ⊥)
  have hmem : ((0 : Fin d0 → ℂ), (0 : Fin d1 → ℂ), z) ∈
      (abSub (d0 := d0) (d1 := d1) Ls H.t H.t_ab).tan := by
    rw [abSub_tan, Submodule.mem_prod, Submodule.mem_prod]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, hz⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hz0 (congrArg (fun p => p.2.2) hmem)

end LSG.W88.K5d
