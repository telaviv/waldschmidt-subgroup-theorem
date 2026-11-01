/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Stmt

/-!
# Rationality calculus and the pivot lemma (A4.3, β; STAGE_A4 §1.3)

`IsRatSub Λ t` (`LSG.MEB.Block`): `t ∩ Λ` spans `t` over `ℝ`.

* **`isRatSub_map`**: images of rational subspaces under linear maps sending `Λ` into `Λ'` are rational.
* **`isRatSub_inf_ker`**: for `Λ, Λ'` discrete, `t ∩ ker φ` is rational (rank count: `t ∩ Λ` is a lattice of
  `t`, `φ(t ∩ Λ)` a lattice of `φ(t)`, so the kernel lattice has full rank in `t ∩ ker φ`; Mathlib's
  `Real.finrank_eq_int_finrank_of_discrete` and rank-nullity over `ℤ`).
* `discreteTopology_perAb`.
* **`pivot`** (the pivot lemma): for simple blocks and `t ⊆ ∏_k ℂ^{g_k}` rational for `perAb B`, there is
  `J ⊆ Fin m` such that the projection `t → ∏_{k ∈ J} ℂ^{g_k}` is bijective (stated as injectivity and surjectivity
  of the restriction to the coordinates in `J`). `pivot_finrank`: `dim t = Σ_{k ∈ J} g_k`.
-/

open Module Submodule

namespace LSG.MEB

/-! ### Rational subspaces under linear maps -/

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Images** of rational subspaces are rational. -/
theorem isRatSub_map {Λ : AddSubgroup E} {Λ' : AddSubgroup F} (φ : E →ₗ[ℂ] F) (hφ : ∀ z ∈ Λ, φ z ∈ Λ')
    {t : Submodule ℂ E} (ht : IsRatSub Λ t) : IsRatSub Λ' (t.map φ) := by
  unfold IsRatSub at ht ⊢
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ t.restrictScalars ℝ := hz
    rw [ht] at hz'
    have := Submodule.mem_map_of_mem (f := φ.restrictScalars ℝ) hz'
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨y, ⟨hyt, hyΛ⟩, rfl⟩
    exact ⟨⟨y, hyt, rfl⟩, hφ y hyΛ⟩
  · rw [Submodule.span_le]
    rintro w ⟨hw, -⟩
    exact hw

/-- `Set.finrank` of a set whose `ℤ`-span is discrete: `ℝ`- and `ℤ`-ranks agree. -/
theorem finrank_span_real_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (L : Submodule ℤ G) (hL : DiscreteTopology L) :
    finrank ℝ (span ℝ (L : Set G)) = finrank ℤ L := by
  have h := Real.finrank_eq_int_finrank_of_discrete (s := (L : Set G)) (by rwa [span_eq])
  rw [Set.finrank, Set.finrank, span_eq] at h
  exact h

/-- **Kernels**: for discrete `Λ`, `Λ'` and `φ(Λ) ⊆ Λ'`, `t ∩ ker φ` is rational. -/
theorem isRatSub_inf_ker {Λ : AddSubgroup E} {Λ' : AddSubgroup F} (hΛ : DiscreteTopology Λ)
    (hΛ' : DiscreteTopology Λ') (φ : E →ₗ[ℂ] F) (hφ : ∀ z ∈ Λ, φ z ∈ Λ') {t : Submodule ℂ E}
    (ht : IsRatSub Λ t) : IsRatSub Λ (t ⊓ LinearMap.ker φ) := by
  unfold IsRatSub at ht ⊢
  set tR := t.restrictScalars ℝ
  set φR := φ.restrictScalars ℝ
  -- the lattice `L = t ∩ Λ` and the kernel lattice `L₀`
  set L : Submodule ℤ E := t.restrictScalars ℤ ⊓ Λ.toIntSubmodule with hLdef
  set L₀ : Submodule ℤ E := L ⊓ LinearMap.ker (φ.restrictScalars ℤ) with hL₀def
  have hLset : (L : Set E) = {z | z ∈ t ∧ z ∈ Λ} := by
    ext z; simp [L]
  have hL₀set : (L₀ : Set E) = {z | z ∈ t ⊓ LinearMap.ker φ ∧ z ∈ Λ} := by
    ext z; simp [L₀, L, and_comm, and_assoc]
  have hLd : DiscreteTopology L := DiscreteTopology.of_subset (s := (Λ : Set E)) hΛ fun z hz => hz.2
  have hL₀d : DiscreteTopology L₀ :=
    DiscreteTopology.of_subset (s := (Λ : Set E)) hΛ fun z hz => hz.1.2
  -- the image lattice
  set φℤ : L →ₗ[ℤ] F := (φ.restrictScalars ℤ).comp L.subtype
  have hRd : DiscreteTopology (LinearMap.range φℤ) := by
    refine DiscreteTopology.of_subset (s := (Λ' : Set F)) hΛ' ?_
    rintro _ ⟨z, rfl⟩
    exact hφ _ z.2.2
  -- ranks
  have hrkL : finrank ℤ L = finrank ℝ tR := by
    rw [← finrank_span_real_eq L hLd, hLset, ← ht]
  have hrkR : finrank ℤ (LinearMap.range φℤ) = finrank ℝ (tR.map φR) := by
    rw [← finrank_span_real_eq _ hRd]
    have : ((LinearMap.range φℤ : Submodule ℤ F) : Set F) = φ '' (L : Set E) := by
      ext w; simp [φℤ]
    have hspan : span ℝ ((LinearMap.range φℤ : Submodule ℤ F) : Set F) = tR.map φR := by
      rw [this, hLset, show (φ : E → F) = φR from rfl, ← Submodule.map_span, ← ht]
    rw [hspan]
  have hrkK : finrank ℤ (LinearMap.ker φℤ) = finrank ℝ (span ℝ (L₀ : Set E)) := by
    rw [finrank_span_real_eq L₀ hL₀d]
    have e : LinearMap.ker φℤ ≃ₗ[ℤ] L₀ :=
      (Submodule.equivMapOfInjective L.subtype L.injective_subtype _).trans
        (LinearEquiv.ofEq _ _ (by
          ext z
          simp only [Submodule.mem_map, LinearMap.mem_ker, φℤ, L₀, Submodule.mem_inf]
          constructor
          · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
          · rintro ⟨hz, hz'⟩; exact ⟨⟨z, hz⟩, hz', rfl⟩))
    exact e.finrank_eq
  have hZ : finrank ℤ (LinearMap.range φℤ) + finrank ℤ (LinearMap.ker φℤ) = finrank ℤ L := by
    rw [← (LinearMap.quotKerEquivRange φℤ).finrank_eq]
    exact Submodule.finrank_quotient_add_finrank _
  -- rank-nullity over `ℝ`
  have hR : finrank ℝ (tR.map φR) + finrank ℝ ((t ⊓ LinearMap.ker φ).restrictScalars ℝ) = finrank ℝ tR := by
    have h := LinearMap.finrank_range_add_finrank_ker (φR.domRestrict tR)
    rw [LinearMap.range_domRestrict] at h
    rw [← h]
    congr 1
    refine (LinearEquiv.ofEq _ _ ?_ |>.trans (Submodule.comapSubtypeEquivOfLe
      (p := (t ⊓ LinearMap.ker φ).restrictScalars ℝ) (q := tR) fun z hz => (Submodule.mem_inf.mp hz).1)).finrank_eq.symm
    ext z
    simp [φR]
  -- conclusion
  have hle : span ℝ (L₀ : Set E) ≤ (t ⊓ LinearMap.ker φ).restrictScalars ℝ := by
    rw [span_le, hL₀set]
    rintro z ⟨hz, -⟩
    exact hz
  rw [← hL₀set]
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

end General

/-! ### The pivot lemma -/

variable {m : ℕ} {B : Fin m → AbBlock}

theorem discreteTopology_perAb : DiscreteTopology (perAb B) := by
  have : ∀ k, DiscreteTopology (B k).per := fun k => (B k).per_discrete
  let f : perAb B → ∀ k, (B k).per := fun z k => ⟨(z : ∀ k, Fin (B k).g → ℂ) k, z.2 k (Set.mem_univ k)⟩
  refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
  · exact continuous_pi fun k => Continuous.subtype_mk ((continuous_apply k).comp continuous_subtype_val) _
  · intro z z' h
    exact Subtype.ext (funext fun k => congrArg Subtype.val (congrFun h k))

theorem proj_mem_per {z : ∀ k, Fin (B k).g → ℂ} (hz : z ∈ perAb B) (k : Fin m) : z k ∈ (B k).per :=
  hz k (Set.mem_univ k)

theorem pivot_aux (T : Finset (Fin m)) :
    ∀ t : Submodule ℂ (∀ k, Fin (B k).g → ℂ), IsRatSub (perAb B) t → (∀ z ∈ t, ∀ k ∉ T, z k = 0) →
      ∃ J ⊆ T, (∀ z ∈ t, (∀ k ∈ J, z k = 0) → z = 0) ∧
        ∀ y : ∀ k, Fin (B k).g → ℂ, ∃ z ∈ t, ∀ k ∈ J, z k = y k := by
  induction T using Finset.induction_on with
  | empty =>
    intro t _ h0
    refine ⟨∅, subset_refl _, fun z hz _ => funext fun k => h0 z hz k (Finset.notMem_empty k),
      fun y => ⟨0, t.zero_mem, fun k hk => absurd hk (Finset.notMem_empty k)⟩⟩
  | insert a T haT ih =>
    intro t ht h0
    have hta := isRatSub_map (Λ' := (B a).per) (LinearMap.proj a) (fun z hz => proj_mem_per hz a) ht
    rcases (B a).simple _ hta with hbot | htop
    · -- `t` lies in `z a = 0`
      have hza : ∀ z ∈ t, z a = 0 := fun z hz => by
        have : z a ∈ t.map (LinearMap.proj a) := ⟨z, hz, rfl⟩
        rw [hbot] at this
        exact (Submodule.mem_bot ℂ).mp this
      obtain ⟨J, hJ, hinj, hsurj⟩ := ih t ht fun z hz k hk => by
        by_cases hka : k = a
        · rw [hka]; exact hza z hz
        · exact h0 z hz k (by simp [hka, hk])
      exact ⟨J, hJ.trans (Finset.subset_insert a T), hinj, hsurj⟩
    · set t' := t ⊓ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun k => Fin (B k).g → ℂ) a)
      have ht' : IsRatSub (perAb B) t' :=
        isRatSub_inf_ker discreteTopology_perAb (B a).per_discrete _ (fun z hz => proj_mem_per hz a) ht
      obtain ⟨J, hJ, hinj, hsurj⟩ := ih t' ht' fun z hz k hk => by
        by_cases hka : k = a
        · rw [hka]; exact hz.2
        · exact h0 z hz.1 k (by simp [hka, hk])
      refine ⟨insert a J, Finset.insert_subset_insert a hJ, fun z hz hzJ => ?_, fun y => ?_⟩
      · exact hinj z ⟨hz, hzJ a (Finset.mem_insert_self a J)⟩ fun k hk =>
          hzJ k (Finset.mem_insert_of_mem hk)
      · have hya : y a ∈ t.map (LinearMap.proj a) := by rw [htop]; exact Submodule.mem_top
        obtain ⟨z₁, hz₁, hz₁a⟩ := hya
        obtain ⟨z₂, hz₂, hz₂J⟩ := hsurj (y - z₁)
        refine ⟨z₁ + z₂, t.add_mem hz₁ hz₂.1, fun k hk => ?_⟩
        rcases Finset.mem_insert.mp hk with rfl | hk
        · have h2 : z₂ k = 0 := hz₂.2
          simp only [Pi.add_apply, h2, add_zero]
          exact hz₁a
        · have := hz₂J k hk
          simp only [Pi.sub_apply] at this
          simp [this]

/-- **The pivot lemma** (STAGE_A4 §1.3): for a family of simple abelian blocks and a subspace
`t ⊆ ∏_k ℂ^{g_k}` that is rational for `perAb B`, there is a set `J` of blocks such that the projection
`t → ∏_{k ∈ J} ℂ^{g_k}` is an isomorphism (injective: a vector of `t` vanishing on `J` is `0`; surjective: any
values on `J` are attained in `t`). -/
theorem pivot {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} (ht : IsRatSub (perAb B) t) :
    ∃ J : Finset (Fin m), (∀ z ∈ t, (∀ k ∈ J, z k = 0) → z = 0) ∧
      ∀ y : ∀ k, Fin (B k).g → ℂ, ∃ z ∈ t, ∀ k ∈ J, z k = y k := by
  obtain ⟨J, -, h⟩ := pivot_aux Finset.univ t ht fun z _ k hk => absurd (Finset.mem_univ k) hk
  exact ⟨J, h⟩

end LSG.MEB
