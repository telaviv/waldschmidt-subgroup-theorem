/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Statement
import LSG.W88.K11Omega

/-!
# Theorem 4.1 for a connected algebraic subgroup `G' = T_ℒ × (0 or E)` of `G_m^{d₁} × E`

`thm41Sub`: `LSG.W88.Theorem41Abelian`, applied to `G_m^k × E^{b}` (`k = dim ℒ`, `b ∈ {0, 1}`) and
transported to `G' ⊂ G_m^{d₁} × E` along the isogeny `ι : (c, z) ↦ (Σ cᵢ βᵢ, z)`, where
`β₁, …, β_k` is a `ℚ`-basis of `ℒ` (the columns of a rational matrix `C` with rational left
inverse `D`). The statement is written in the coordinates `T d₁` of `lean_mstar`: subgroups of
`G'` are again `tangentSub ℒ'' b''`, ranks are `ℚ`-dimensions of `ℚ`-spans, and the periods of `G'`
span `Ω_ℚ ∩ T_{G'}` (`omegaQ_inf_tangent`).
-/

open Complex Module Matrix

namespace LSG.W88.K11

open MStarCopy

variable {d₁ : ℕ}

/-! ### Helpers -/

lemma finrank_map_of_injective {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] {f : M →ₗ[R] N} (hf : Function.Injective f) (S : Submodule R M) :
    finrank R (S.map f) = finrank R S :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf S)).symm

lemma fg_map_addSubgroup {E F : Type*} [AddCommGroup E] [AddCommGroup F] {Y : AddSubgroup E}
    (hY : Y.FG) (f : E →+ F) : (Y.map f).FG := by
  obtain ⟨S, hS, hfin⟩ := (AddSubgroup.fg_iff Y).mp hY
  exact (AddSubgroup.fg_iff _).mpr ⟨f '' S, by rw [← hS, AddMonoidHom.map_closure], hfin.image f⟩

lemma span_closure_eq {E : Type*} [AddCommGroup E] [Module ℚ E] (S : Set E) :
    Submodule.span ℚ ((AddSubgroup.closure S : AddSubgroup E) : Set E) = Submodule.span ℚ S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact (AddSubgroup.closure_le (Submodule.span ℚ S).toAddSubgroup).mpr Submodule.subset_span
  · exact Submodule.span_mono AddSubgroup.subset_closure

lemma finiteDimensional_span_of_fg {E : Type*} [AddCommGroup E] [Module ℚ E] {Y : AddSubgroup E}
    (hY : Y.FG) : FiniteDimensional ℚ (Submodule.span ℚ (Y : Set E)) := by
  obtain ⟨S, hS, hfin⟩ := (AddSubgroup.fg_iff Y).mp hY
  rw [← hS, span_closure_eq]
  exact FiniteDimensional.span_of_finite ℚ hfin

instance subsingleton_fin_toNat (b : Bool) : Subsingleton (Fin b.toNat) := by
  cases b
  · change Subsingleton (Fin 0); infer_instance
  · change Subsingleton (Fin 1); infer_instance

lemma sum_fin_toNat (b : Bool) (z : ℂ) : ∑ _j : Fin b.toNat, z = if b then z else 0 := by
  cases b <;> simp

/-- A subspace of `ℂ^{b}` (`b ∈ {0,1}`) is `0` or everything; it is nonzero only if `b = 1`. -/
lemma eq_top_of_ne_bot_toNat {b : Bool} {t : Submodule ℂ (Fin b.toNat → ℂ)} (ht : t ≠ ⊥) :
    b = true ∧ t = ⊤ := by
  cases b
  · exact absurd ((Submodule.eq_bot_iff t).mpr fun x _ => funext fun i => absurd i.2 (by simp)) ht
  · refine ⟨rfl, Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)⟩
    have := Submodule.one_le_finrank_iff.mpr ht
    simpa using this

/-! ### The isogeny `ι` and its rational left inverse `π` -/

/-- `z ↦ Σ zⱼ`. -/
def sumL (m : ℕ) : (Fin m → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ j, z j
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum]

/-- `z ↦ (z, …, z)`. -/
def constL (m : ℕ) : ℂ →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun _ => LinearMap.id

variable {k : ℕ}

/-- `ι : ℂ⁰ × ℂ^k × ℂ^{b} → T d₁`, `(a, c, z) ↦ (C c, Σ z)`. -/
noncomputable def iotaL (C : Matrix (Fin d₁) (Fin k) ℚ) (b : Bool) :
    Tan 0 k b.toNat →ₗ[ℂ] T d₁ :=
  ((cm C).mulVecLin.comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))).prod
    ((sumL b.toNat).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)))

/-- `π : T d₁ → ℂ⁰ × ℂ^k × ℂ^{b}`, `(v, z) ↦ (0, D v, (z))`. -/
noncomputable def piL (D : Matrix (Fin k) (Fin d₁) ℚ) (b : Bool) :
    T d₁ →ₗ[ℂ] Tan 0 k b.toNat :=
  (0 : T d₁ →ₗ[ℂ] (Fin 0 → ℂ)).prod (((cm D).mulVecLin.comp (LinearMap.fst ℂ _ _)).prod
    ((constL b.toNat).comp (LinearMap.snd ℂ _ _)))

lemma iotaL_apply (C : Matrix (Fin d₁) (Fin k) ℚ) (b : Bool) (x : Tan 0 k b.toNat) :
    iotaL C b x = ((cm C).mulVec x.2.1, ∑ j, x.2.2 j) := rfl

lemma piL_apply (D : Matrix (Fin k) (Fin d₁) ℚ) (b : Bool) (v : T d₁) :
    piL D b v = (0, (cm D).mulVec v.1, fun _ => v.2) := rfl

variable {ℒ : Submodule ℚ (Fin d₁ → ℚ)} {C : Matrix (Fin d₁) (Fin k) ℚ}
  {D : Matrix (Fin k) (Fin d₁) ℚ}

lemma piL_iotaL (hDC : D * C = 1) (b : Bool) (x : Tan 0 k b.toNat) :
    piL D b (iotaL C b x) = x := by
  rw [iotaL_apply, piL_apply]
  refine Prod.ext (Subsingleton.elim _ _) (Prod.ext (mulVec_left_inv hDC _) ?_)
  funext j
  exact Fintype.sum_subsingleton _ j

lemma iotaL_injective (hDC : D * C = 1) (b : Bool) : Function.Injective (iotaL C b) := by
  intro x y h
  rw [← piL_iotaL hDC b x, ← piL_iotaL hDC b y, h]

lemma iotaL_piL (hDC : D * C = 1) (hC : LinearMap.range C.mulVecLin = ℒ) {b : Bool} {v : T d₁}
    (hv : v ∈ tangentSub ℒ b) : iotaL C b (piL D b v) = v := by
  rw [mem_tangentSub, cspan_eq_range hC] at hv
  obtain ⟨⟨c, hc⟩, hb⟩ := hv
  rw [piL_apply, iotaL_apply, sum_fin_toNat]
  refine Prod.ext ?_ ?_
  · change (cm C).mulVec ((cm D).mulVec v.1) = v.1
    rw [← hc]; simp only [Matrix.mulVecLin_apply]; rw [mulVec_left_inv hDC]
  · cases b
    · simpa using (hb.resolve_left (by simp)).symm
    · rfl

lemma range_iotaL (hDC : D * C = 1) (hC : LinearMap.range C.mulVecLin = ℒ) (b : Bool) :
    LinearMap.range (iotaL C b) = tangentSub ℒ b := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [mem_tangentSub, iotaL_apply, cspan_eq_range hC]
    refine ⟨⟨x.2.1, rfl⟩, ?_⟩
    cases b
    · right; simp
    · left; rfl
  · intro v hv
    exact ⟨piL D b v, iotaL_piL hDC hC hv⟩

lemma piL_mem_lam (L : PeriodPair) (b : Bool) {y : T d₁} (hy : GoodPt L y) :
    piL D b y ∈ Lam (d0 := 0) (fun _ : Fin b.toNat => L) := by
  rw [piL_apply]
  refine ⟨fun i => i.elim0, fun i => ?_, fun _ => hy.2⟩
  have : (cm D).mulVec y.1 i = ∑ j, ((D i j : ℚ) : ℂ) * y.1 j := by
    simp [cm, Matrix.mulVec, dotProduct]
  change IsAlgebraic ℚ (Complex.exp ((cm D).mulVec y.1 i))
  rw [this]; exact isAlg_exp_ratComb _ _ hy.1

lemma piL_algVec (b : Bool) {w : T d₁} (hw : MStarCopy.AlgVec w) :
    LSG.W88.AlgVec (piL D b w).1 ∧ LSG.W88.AlgVec (piL D b w).2.1 ∧
      LSG.W88.AlgVec (piL D b w).2.2 := by
  rw [piL_apply]
  refine ⟨fun i => i.elim0, fun i => ?_, fun _ => hw.2⟩
  have : (cm D).mulVec w.1 i = ∑ j, ((D i j : ℚ) : ℂ) * w.1 j := by
    simp [cm, Matrix.mulVec, dotProduct]
  change IsAlgebraic ℚ ((cm D).mulVec w.1 i)
  rw [this]; exact isAlg_ratComb _ _ hw.1

/-- `ι` maps `cspan M` onto `cspan (C M)`. -/
lemma map_cspan (C : Matrix (Fin d₁) (Fin k) ℚ) (M : Submodule ℚ (Fin k → ℚ)) :
    (cspan M).map (cm C).mulVecLin = cspan (M.map C.mulVecLin) := by
  rw [cspan_eq, cspan_eq, Submodule.map_span, Set.image_image]
  congr 1
  ext v
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨C.mulVec q, ⟨q, hq, rfl⟩, by rw [Matrix.mulVecLin_apply, cm_mulVec_castL]⟩
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, by rw [Matrix.mulVecLin_apply, cm_mulVec_castL]; rfl⟩

/-! ### Periods -/

lemma per_basis_mem (L : PeriodPair) (b : Bool) (i : Fin k) :
    ((0 : Fin 0 → ℂ), (Pi.single i (2 * Real.pi * I) : Fin k → ℂ), (0 : Fin b.toNat → ℂ)) ∈
      Per (d0 := 0) (fun _ : Fin b.toNat => L) := by
  refine ⟨rfl, fun i' => ⟨if i' = i then 1 else 0, ?_⟩, fun _ => L.lattice.zero_mem⟩
  by_cases h : i' = i
  · subst h; simp
  · simp [h]

lemma per_lattice_mem (L : PeriodPair) (b : Bool) {ω : ℂ} (hω : ω ∈ L.lattice) :
    ((0 : Fin 0 → ℂ), (0 : Fin k → ℂ), (fun _ => ω : Fin b.toNat → ℂ)) ∈
      Per (d0 := 0) (fun _ : Fin b.toNat => L) :=
  ⟨rfl, fun _ => ⟨0, by simp⟩, fun _ => hω⟩

lemma map_span_per (L : PeriodPair) (hDC : D * C = 1) (hC : LinearMap.range C.mulVecLin = ℒ)
    (b : Bool) :
    (Submodule.span ℚ ((Per (d0 := 0) (fun _ : Fin b.toNat => L) : AddSubgroup (Tan 0 k b.toNat)) :
      Set (Tan 0 k b.toNat))).map
      ((iotaL C b).restrictScalars ℚ) = OmegaQ L d₁ ⊓ Tq ℒ b := by
  classical
  rw [Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, ⟨-, hp2, hp3⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · choose kv hkv using hp2
      obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp
        (L.lattice.sum_mem fun j _ => hp3 j : ∑ j, p.2.2 j ∈ L.lattice)
      refine (mem_omegaQ L).mpr ⟨C.mulVec (fun i => (kv i : ℚ)), m, n, ?_⟩
      rw [phiL_apply]
      change iotaL C b p = _
      rw [iotaL_apply]
      have hp : p.2.1 = (2 * Real.pi * I : ℂ) • castL k (fun i => (kv i : ℚ)) := by
        funext i; rw [hkv i]; simp [mul_comm]
      rw [hp, Matrix.mulVec_smul, cm_mulVec_castL, ← hmn]
      simp
    · change iotaL C b p ∈ tangentSub ℒ b
      rw [← range_iotaL hDC hC]; exact ⟨p, rfl⟩
  · intro x hx
    rw [omegaQ_inf_tangent] at hx
    have key : ∀ (c : Fin k → ℚ) (p₁ p₂ : ℚ), (b = true ∨ (p₁ = 0 ∧ p₂ = 0)) →
        PhiL L d₁ (C.mulVec c, p₁, p₂) ∈ Submodule.span ℚ
          (((iotaL C b).restrictScalars ℚ) '' ((Per (d0 := 0) (fun _ : Fin b.toNat => L) :
            AddSubgroup (Tan 0 k b.toNat)) : Set (Tan 0 k b.toNat))) := by
      intro c p₁ p₂ hb
      rw [← Submodule.map_span]
      let y : Tan 0 k b.toNat := (0, (2 * Real.pi * I : ℂ) • castL k c,
        fun _ => (p₁ : ℂ) * L.ω₁ + (p₂ : ℂ) * L.ω₂)
      refine ⟨y, ?_, ?_⟩
      · have hy : y = ∑ i, c i • ((0 : Fin 0 → ℂ), (Pi.single i (2 * Real.pi * I) : Fin k → ℂ),
            (0 : Fin b.toNat → ℂ)) + p₁ • ((0 : Fin 0 → ℂ), (0 : Fin k → ℂ),
            (fun _ => L.ω₁ : Fin b.toNat → ℂ)) + p₂ • ((0 : Fin 0 → ℂ), (0 : Fin k → ℂ),
            (fun _ => L.ω₂ : Fin b.toNat → ℂ)) := by
          refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ ?_)
          · funext i
            simp [y, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply, Rat.smul_def,
              mul_comm]
          · funext j
            simp [y, Prod.snd_sum, Rat.smul_def]
        rw [hy]
        refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span (per_basis_mem L b i))) ?_) ?_
        · exact Submodule.smul_mem _ _ (Submodule.subset_span (per_lattice_mem L b
            L.ω₁_mem_lattice))
        · exact Submodule.smul_mem _ _ (Submodule.subset_span (per_lattice_mem L b
            L.ω₂_mem_lattice))
      · change iotaL C b y = _
        rw [iotaL_apply, phiL_apply, sum_fin_toNat]
        refine Prod.ext ?_ ?_
        · change (cm C).mulVec ((2 * Real.pi * I : ℂ) • castL k c) = _
          rw [Matrix.mulVec_smul, cm_mulVec_castL]
        · cases b
          · obtain ⟨rfl, rfl⟩ := hb.resolve_left (by simp)
            simp
          · rfl
    have hL : ∀ q ∈ ℒ, ∃ c, C.mulVec c = q := by
      intro q hq; rw [← hC] at hq; obtain ⟨c, rfl⟩ := hq; exact ⟨c, rfl⟩
    cases b
    · obtain ⟨⟨q, hq⟩, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hL q hq
      exact key c 0 0 (Or.inr ⟨rfl, rfl⟩)
    · obtain ⟨⟨⟨q, hq⟩, p₁, p₂⟩, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hL q hq
      exact key c p₁ p₂ (Or.inl rfl)

/-! ### The transported theorem -/

/-- `dim G'` for `G' = T_ℒ × (0 or E)`. -/
noncomputable abbrev nT (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) : ℕ := finrank ℚ ℒ + b.toNat
/-- `d₁' + 2d₂'` for `G' = T_ℒ × (0 or E)`. -/
noncomputable abbrev nP (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) : ℕ := finrank ℚ ℒ + 2 * b.toNat

lemma mem_tan {k m : ℕ} {Ls : Fin m → PeriodPair} (H : SubgroupData (d0 := 0) (d1 := k) Ls)
    {x : Tan 0 k m} : x ∈ H.tan ↔ x.1 ∈ H.h0 ∧ x.2.1 ∈ torusLie H.U ∧ x.2.2 ∈ H.t := by
  simp [SubgroupData.tan, Submodule.mem_prod]

/-- **W88 Thm 4.1 for `G' = T_ℒ × (0 or E) ⊂ G_m^{d₁} × E`**, in the coordinates of `G`, with
`V' ⊂ T_{G'}` a hyperplane of `T_{G'}`. The subgroup `G''` of `G'` is again `tangentSub ℒ'' b''`. -/
theorem thm41Sub (h : Theorem41Abelian) (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool)
    (V' W' : Submodule ℂ (T d₁)) (Y : AddSubgroup (T d₁))
    (hVT : V' ≤ tangentSub ℒ b) (hVdim : finrank ℂ V' + 1 = nT ℒ b)
    (hWV : W' ≤ V') (hWrat : RatSub W') (hYfg : Y.FG) (hY : ∀ y ∈ Y, y ∈ V' ∧ GoodPt L y)
    (hNR : finrank ℚ ℒ + finrank ℚ ↥(Submodule.span ℚ (Y : Set (T d₁)) ⊓ OmegaQ L d₁) ≤
      2 * finrank ℂ V') :
    ∃ (ℒ'' : Submodule ℚ (Fin d₁ → ℚ)) (b'' : Bool), tangentSub ℒ'' b'' ≤ tangentSub ℒ b ∧
      (finrank ℂ W' : ℤ) - finrank ℂ ↥(W' ⊓ tangentSub ℒ'' b'') < (nT ℒ b : ℤ) - nT ℒ'' b'' ∧
      ((finrank ℚ (Submodule.span ℚ (Y : Set (T d₁))) : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Y : Set (T d₁)) ⊓ (Tq ℒ'' b'' ⊔ OmegaQ L d₁)) +
          ((nP ℒ b : ℤ) - nP ℒ'' b'')) ≤
        (((nT ℒ b : ℤ) - nT ℒ'' b'') -
            ((finrank ℂ W' : ℤ) - finrank ℂ ↥(W' ⊓ tangentSub ℒ'' b''))) *
          ((nP ℒ b : ℤ) - finrank ℚ ↥(Submodule.span ℚ (Y : Set (T d₁)) ⊓ OmegaQ L d₁)) := by
  classical
  obtain ⟨C, D, hDC, hC⟩ := exists_frame ℒ
  have hVdim' : finrank ℂ V' + 1 = finrank ℚ ℒ + b.toNat := hVdim
  set ι := iotaL C b with hι
  set π := piL D b with hπ
  have hinj : Function.Injective ι := iotaL_injective hDC b
  have hrange : LinearMap.range ι = tangentSub ℒ b := range_iotaL hDC hC b
  have hιπ : ∀ v ∈ tangentSub ℒ b, ι (π v) = v := fun v hv => iotaL_piL hDC hC hv
  have hπι : ∀ x, π (ι x) = x := piL_iotaL hDC b
  set Vs := V'.comap ι with hVs_def
  set Ws := W'.comap ι with hWs_def
  set Ys := Y.map π.toAddMonoidHom with hYs_def
  have hmap : ∀ S : Submodule ℂ (T d₁), S ≤ tangentSub ℒ b → (S.comap ι).map ι = S := by
    intro S hS; rw [Submodule.map_comap_eq, hrange, inf_eq_right.mpr hS]
  have hWT : W' ≤ tangentSub ℒ b := hWV.trans hVT
  have hVs : finrank ℂ Vs = finrank ℂ V' := by
    rw [← finrank_map_of_injective hinj, hmap V' hVT]
  have hWs : finrank ℂ Ws = finrank ℂ W' := by
    rw [← finrank_map_of_injective hinj, hmap W' hWT]
  -- `Ws` is `ℚ̄`-rational
  have hWsrat : RationalOverQbarTan Ws := by
    obtain ⟨S, hSalg, hS⟩ := hWrat
    have hWs_eq : Ws = W'.map π := by
      ext x; constructor
      · intro hx; exact ⟨ι x, hx, hπι x⟩
      · rintro ⟨w, hw, rfl⟩
        change ι (π w) ∈ W'
        rw [hιπ w (hWT hw)]; exact hw
    have hWs_span : Ws = Submodule.span ℂ (π '' S) := by rw [hWs_eq, hS, Submodule.map_span]
    refine le_antisymm (hWs_span.le.trans (Submodule.span_mono ?_)) ?_
    · rintro _ ⟨s, hs, rfl⟩
      have hsW : s ∈ W' := hS ▸ Submodule.subset_span hs
      exact ⟨by rw [hWs_eq]; exact ⟨s, hsW, rfl⟩, piL_algVec b (hSalg s hs)⟩
    · rw [Submodule.span_le]; exact fun x hx => hx.1
  have hYsfg : Ys.FG := fg_map_addSubgroup hYfg _
  have hYsmem : ∀ x ∈ Ys, x ∈ Vs ∧ x ∈ Lam (d0 := 0) (fun _ : Fin b.toNat => L) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyV, hyG⟩ := hY y hy
    refine ⟨?_, piL_mem_lam L b hyG⟩
    change ι (π y) ∈ V'
    rw [hιπ y (hVT hyV)]; exact hyV
  -- the `ℚ`-structures
  set ιq := ι.restrictScalars ℚ with hιq
  have hinjq : Function.Injective ιq := hinj
  set Yq := Submodule.span ℚ (Y : Set (T d₁)) with hYq
  have : FiniteDimensional ℚ Yq := finiteDimensional_span_of_fg hYfg
  have hYT : Yq ≤ Tq ℒ b := Submodule.span_le.mpr fun y hy => hVT (hY y hy).1
  have hYmap : (Submodule.span ℚ (Ys : Set (Tan 0 (finrank ℚ ℒ) b.toNat))).map ιq = Yq := by
    rw [Submodule.map_span]; congr 1
    ext v; constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      change ι (π y) ∈ Y
      rw [hιπ y (hVT (hY y hy).1)]; exact hy
    · intro hv; exact ⟨π v, ⟨v, hv, rfl⟩, hιπ v (hVT (hY v hv).1)⟩
  have hPmap := map_span_per L hDC hC b
  have rk1 : rk Ys = finrank ℚ Yq := by
    rw [rk, ← finrank_map_of_injective hinjq, hYmap]
  have rk2 : rk (Ys ⊓ Per (fun _ : Fin b.toNat => L)) = finrank ℚ ↥(Yq ⊓ OmegaQ L d₁) := by
    rw [rk, span_inf_addSubgroup, ← finrank_map_of_injective hinjq, Submodule.map_inf _ hinjq,
      hYmap, hPmap, inf_comm (OmegaQ L d₁), ← inf_assoc, inf_eq_left.mpr hYT]
  obtain ⟨H, -, hτ, hineq⟩ := h 0 (finrank ℚ ℒ) b.toNat (fun _ => L) (fun _ => ⟨hg₂, hg₃⟩) Vs Ws Ys
    (by rw [hVs]; omega) (Submodule.comap_mono hWV) hWsrat hYsfg hYsmem
    (by rw [rk2, hVs]; simpa using hNR)
  -- the subgroup `G''`
  set ℒ'' := (annQ H.U).map C.mulVecLin with hℒ''
  set b'' := decide (H.t ≠ ⊥) with hb''
  have ht : (H.t = ⊥ ∧ b'' = false) ∨ (H.t = ⊤ ∧ b = true ∧ b'' = true) := by
    by_cases h0 : H.t = ⊥
    · left; exact ⟨h0, by simp [b'', h0]⟩
    · right
      obtain ⟨hb, htop⟩ := eq_top_of_ne_bot_toNat h0
      exact ⟨htop, hb, by simp [b'', h0]⟩
  have hft : finrank ℂ H.t = b''.toNat := by
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2]; simp
    · rw [h1, h3]; subst h2; simp
  have hbb : b''.toNat ≤ b.toNat := by
    rcases ht with ⟨-, h2⟩ | ⟨-, h2, h3⟩
    · rw [h2]; simp
    · rw [h2, h3]
  have hL'' : finrank ℚ ℒ'' + finrank ℚ H.U = finrank ℚ ℒ := by
    rw [hℒ'', finrank_map_of_injective (f := C.mulVecLin) (ratMulVec_injective hDC)]
    exact finrank_annQ H.U
  have htl : torusLie H.U = cspan (annQ H.U) := by rw [← annC_eq_cspan]; rfl
  have hTan : H.tan.map ι = tangentSub ℒ'' b'' := by
    ext ⟨v, z⟩
    rw [mem_tangentSub, Submodule.mem_map]
    constructor
    · rintro ⟨⟨a, c, w⟩, hx, hxe⟩
      rw [mem_tan] at hx
      obtain ⟨-, hc, hw⟩ := hx
      rw [iotaL_apply] at hxe
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxe
      refine ⟨?_, ?_⟩
      · rw [hℒ'', ← map_cspan, ← htl]; exact ⟨c, hc, rfl⟩
      · rcases ht with ⟨h1, -⟩ | ⟨-, -, h3⟩
        · right; rw [h1, Submodule.mem_bot] at hw
          have hw' : w = 0 := hw
          simp [hw']
        · left; exact h3
    · rintro ⟨hv, hz⟩
      rw [hℒ'', ← map_cspan, ← htl] at hv
      obtain ⟨c, hc, rfl⟩ := hv
      rcases ht with ⟨-, h2⟩ | ⟨h1, h2, -⟩
      · have hz0 : z = 0 := hz.resolve_left (by simp [h2])
        refine ⟨(0, c, 0), (mem_tan H).mpr ⟨H.h0.zero_mem, hc, H.t.zero_mem⟩, ?_⟩
        rw [iotaL_apply]; simp [hz0]
      · refine ⟨(0, c, fun _ => z), (mem_tan H).mpr ⟨H.h0.zero_mem, hc, h1 ▸ Submodule.mem_top⟩, ?_⟩
        rw [iotaL_apply, sum_fin_toNat]; simp [h2]
  have hT''T : tangentSub ℒ'' b'' ≤ tangentSub ℒ b := by
    rw [← hTan, ← hrange]; exact LinearMap.map_le_range
  have hWinf : finrank ℂ ↥(Ws ⊓ H.tan) = finrank ℂ ↥(W' ⊓ tangentSub ℒ'' b'') := by
    rw [← finrank_map_of_injective hinj, Submodule.map_inf _ hinj, hmap W' hWT, hTan]
  have hTq : (Submodule.span ℚ ((H.tan.toAddSubgroup : AddSubgroup (Tan 0 (finrank ℚ ℒ) b.toNat)) :
      Set (Tan 0 (finrank ℚ ℒ) b.toNat))).map ιq = Tq ℒ'' b'' := by
    rw [span_submodule_coe]
    change _ = (tangentSub ℒ'' b'').restrictScalars ℚ
    rw [← hTan]; rfl
  have rk3 : rk (Ys ⊓ (H.tan.toAddSubgroup ⊔ Per (fun _ : Fin b.toNat => L))) =
      finrank ℚ ↥(Yq ⊓ (Tq ℒ'' b'' ⊔ OmegaQ L d₁)) := by
    rw [rk, span_inf_addSubgroup, span_sup_addSubgroup, ← finrank_map_of_injective hinjq,
      Submodule.map_inf _ hinjq, Submodule.map_sup, hYmap, hTq, hPmap]
    have hT''q : Tq ℒ'' b'' ≤ Tq ℒ b := fun x hx => hT''T hx
    have : Yq ⊓ (Tq ℒ'' b'' ⊔ OmegaQ L d₁ ⊓ Tq ℒ b) = Yq ⊓ (Tq ℒ'' b'' ⊔ OmegaQ L d₁) := by
      rw [← sup_inf_assoc_of_le _ hT''q, inf_comm _ (Tq ℒ b), ← inf_assoc, inf_eq_left.mpr hYT]
    rw [this]
  -- numerics
  have hle1 : finrank ℚ ↥(Yq ⊓ (Tq ℒ'' b'' ⊔ OmegaQ L d₁)) ≤ finrank ℚ Yq :=
    Submodule.finrank_mono inf_le_left
  have hle2 : finrank ℂ ↥(W' ⊓ tangentSub ℒ'' b'') ≤ finrank ℂ W' :=
    Submodule.finrank_mono inf_le_left
  have hδ0 : H.δ0 = 0 := by simp [SubgroupData.δ0]
  have hLz : ((finrank ℚ ℒ'' : ℕ) : ℤ) + (finrank ℚ H.U : ℤ) = (finrank ℚ ℒ : ℤ) := by exact_mod_cast hL''
  have hbz : ((b.toNat - b''.toNat : ℕ) : ℤ) = (b.toNat : ℤ) - b''.toNat := Nat.cast_sub hbb
  have hδ : (H.δ : ℤ) = (nT ℒ b : ℤ) - nT ℒ'' b'' := by
    simp only [SubgroupData.δ, hδ0, SubgroupData.δ1, SubgroupData.δ2, hft, zero_add, nT]
    push_cast [hbz]
    linarith
  have hδ12 : ((H.δ1 + 2 * H.δ2 : ℕ) : ℤ) = (nP ℒ b : ℤ) - nP ℒ'' b'' := by
    simp only [SubgroupData.δ1, SubgroupData.δ2, hft, nP]
    push_cast [hbz]
    linarith
  refine ⟨ℒ'', b'', hT''T, ?_, ?_⟩
  · rw [hWs, hWinf] at hτ
    have := (Nat.cast_lt (α := ℤ)).mpr hτ
    rw [Nat.cast_sub hle2, hδ] at this
    exact this
  · rw [rk1, rk3, rk2, hVs, hWs, hWinf] at hineq
    have e1 : ((finrank ℚ Yq - finrank ℚ ↥(Yq ⊓ (Tq ℒ'' b'' ⊔ OmegaQ L d₁)) + H.δ1 +
        2 * H.δ2 : ℕ) : ℤ) = (finrank ℚ Yq : ℤ) -
          finrank ℚ ↥(Yq ⊓ (Tq ℒ'' b'' ⊔ OmegaQ L d₁)) + ((nP ℒ b : ℤ) - nP ℒ'' b'') := by
      rw [← hδ12]; push_cast [Nat.cast_sub hle1]; ring
    have e2 : (((0 + finrank ℚ ℒ + b.toNat : ℕ) : ℤ) - finrank ℂ V') = 1 := by
      omega
    have e3 : ((H.δ : ℤ) - ((finrank ℂ W' - finrank ℂ ↥(W' ⊓ tangentSub ℒ'' b'') : ℕ) : ℤ)) =
        ((nT ℒ b : ℤ) - nT ℒ'' b'') -
          ((finrank ℂ W' : ℤ) - finrank ℂ ↥(W' ⊓ tangentSub ℒ'' b'')) := by
      rw [hδ, Nat.cast_sub hle2]
    have e4 : (((finrank ℚ ℒ + 2 * b.toNat : ℕ) : ℤ) - finrank ℚ ↥(Yq ⊓ OmegaQ L d₁)) =
        (nP ℒ b : ℤ) - finrank ℚ ↥(Yq ⊓ OmegaQ L d₁) := rfl
    rw [e1, e2, e3, e4, mul_one] at hineq
    exact hineq

end LSG.W88.K11
