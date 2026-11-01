/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Statement

/-!
# Coordinate charts of abelian subvarieties of `E₁ × ⋯ × E_r`

For a `ℂ`-subspace `t ⊂ ℂ^r` of dimension `s` we choose coordinates `ι : Fin s → Fin r` such that
the coordinate projection `π_ι : t → ℂ^s`, `v ↦ v ∘ ι`, is bijective (`exists_chart`). Its inverse
`lift : ℂ^s → t ⊂ ℂ^r` is the tangent map of an isogeny `∏ₖ E_{ι k} → B` when `t` is the tangent
space of an abelian subvariety `B` (`IsAbelianTangent`):

* `Chart.exists_nsmul_lift_mem`: the period lattice of `∏ₖ E_{ι k}` lifts to periods of `B` up to
  a nonzero integer multiple (the image of `t ∩ Λ^r` has finite index);
* `Chart.isAbelianTangent_map`: `lift` maps abelian tangents of `∏ₖ E_{ι k}` to abelian tangents
  of `E₁ × ⋯ × E_r` contained in `t`.

Also: general facts on `rk` (`ℚ`-dimension of the `ℚ`-span of an additive subgroup).
-/

open Module Complex

namespace LSG.CM

open LSG.W88

/-! ### Ranks -/

section Rank

variable {E F : Type*} [AddCommGroup E] [Module ℚ E] [AddCommGroup F] [Module ℚ F]

lemma exists_nsmul_mem_of_mem_span (A : AddSubgroup E) {x : E}
    (hx : x ∈ Submodule.span ℚ (A : Set E)) : ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨k, hk, hky⟩ := hy
    refine ⟨n * k, mul_ne_zero hn hk, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm n k x]
    exact A.add_mem (A.nsmul_mem hnx k) (A.nsmul_mem hky n)
  | smul q x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨q.den * n, mul_ne_zero q.den_nz hn, ?_⟩
    have : (q.den * n) • (q • x) = q.num • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ n, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul]
      congr 1
      have h := Rat.mul_den_eq_num q
      push_cast
      rw [← h]; ring
    rw [this]
    exact A.zsmul_mem hnx _

/-- Two subgroups, one inside the other with torsion quotient, have the same rank. -/
lemma span_eq_of_le_of_nsmul {A B : AddSubgroup E} (hAB : A ≤ B)
    (h : ∀ b ∈ B, ∃ n : ℕ, n ≠ 0 ∧ n • b ∈ A) :
    Submodule.span ℚ (A : Set E) = Submodule.span ℚ (B : Set E) := by
  refine le_antisymm (Submodule.span_mono hAB) (Submodule.span_le.mpr fun b hb => ?_)
  obtain ⟨n, hn, hnb⟩ := h b hb
  have : b = (n : ℚ)⁻¹ • (n • b) := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hnb)

lemma rk_eq_of_le_of_nsmul {A B : AddSubgroup E} (hAB : A ≤ B)
    (h : ∀ b ∈ B, ∃ n : ℕ, n ≠ 0 ∧ n • b ∈ A) : rk A = rk B := by
  rw [rk, rk, span_eq_of_le_of_nsmul hAB h]

lemma finrank_map_of_injective' {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] {f : M →ₗ[R] N} (hf : Function.Injective f) (S : Submodule R M) :
    finrank R (S.map f) = finrank R S :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf S)).symm

lemma rk_map_of_injective (f : E →+ F) (hf : Function.Injective f) (Y : AddSubgroup E) :
    rk (Y.map f) = rk Y := by
  rw [rk, rk, AddSubgroup.coe_map]
  have : (f : E → F) = f.toRatLinearMap := rfl
  rw [this, Submodule.span_image]
  exact finrank_map_of_injective' (f := f.toRatLinearMap) hf _

end Rank

/-! ### Charts -/

variable {r : ℕ}

/-- The coordinate projection `ℂ^r → ℂ^s`, `v ↦ v ∘ ι`. -/
abbrev proj {s : ℕ} (ι : Fin s → Fin r) : (Fin r → ℂ) →ₗ[ℂ] (Fin s → ℂ) :=
  LinearMap.funLeft ℂ ℂ ι

/-- The coordinate functionals span the dual of any subspace. -/
lemma span_coordFun (t : Submodule ℂ (Fin r → ℂ)) :
    Submodule.span ℂ (Set.range fun i : Fin r => (LinearMap.proj i : (Fin r → ℂ) →ₗ[ℂ] ℂ).comp
      t.subtype) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro ψ _
  have hrange : LinearMap.range t.subtype.dualMap = ⊤ := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.ker_subtype,
      Submodule.dualAnnihilator_bot]
  obtain ⟨φ, rfl⟩ : ψ ∈ LinearMap.range t.subtype.dualMap := hrange ▸ Submodule.mem_top
  have hφ : φ = ∑ i, φ (Pi.single i 1) • (LinearMap.proj i : (Fin r → ℂ) →ₗ[ℂ] ℂ) := by
    ext i
    simp [Pi.single_apply]
  rw [hφ, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Coordinates `ι` in which `t → ℂ^{dim t}`, `v ↦ v ∘ ι`, is bijective. -/
theorem exists_chart (t : Submodule ℂ (Fin r → ℂ)) :
    ∃ ι : Fin (finrank ℂ t) → Fin r, Function.Bijective ((proj ι).comp t.subtype) := by
  classical
  set f : Fin r → Module.Dual ℂ t := fun i =>
    (LinearMap.proj i : (Fin r → ℂ) →ₗ[ℂ] ℂ).comp t.subtype with hf
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ f
  have hsp' : Submodule.span ℂ (Set.range (f ∘ a)) = ⊤ := hsp.trans (span_coordFun t)
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  let b : Basis κ ℂ (Module.Dual ℂ t) := Basis.mk hli hsp'.ge
  have hcard : Fintype.card κ = finrank ℂ t := by
    rw [← Module.finrank_eq_card_basis b, Subspace.dual_finrank_eq]
  let e : Fin (finrank ℂ t) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hinj : Function.Injective ((proj (a ∘ e)).comp t.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : ∀ k : κ, f (a k) v = 0 := fun k => by
      have := congrFun hv (e.symm k)
      simpa [hf] using this
    have hall : ∀ ψ ∈ Submodule.span ℂ (Set.range (f ∘ a)), ψ v = 0 := by
      intro ψ hψ
      have hle : Submodule.span ℂ (Set.range (f ∘ a)) ≤
          LinearMap.ker (Module.Dual.eval ℂ t v) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        simpa using hv' k
      simpa using hle hψ
    ext i
    have := hall (f i) (hsp'.symm ▸ Submodule.mem_top)
    simpa [hf] using this
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj


/-- A coordinate chart of `t`: coordinates `ι` with `t → ℂ^{dim t}`, `v ↦ v ∘ ι`, bijective. -/
structure Chart (t : Submodule ℂ (Fin r → ℂ)) where
  /-- the chosen coordinates -/
  ι : Fin (finrank ℂ t) → Fin r
  bij : Function.Bijective ((proj ι).comp t.subtype)

namespace Chart

variable {t : Submodule ℂ (Fin r → ℂ)} (c : Chart t)

/-- `t ≃ ℂ^{dim t}`. -/
noncomputable def equiv : t ≃ₗ[ℂ] (Fin (finrank ℂ t) → ℂ) := LinearEquiv.ofBijective _ c.bij

/-- The inverse of the coordinate projection, `ℂ^{dim t} → t ⊂ ℂ^r`. -/
noncomputable def lift : (Fin (finrank ℂ t) → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  t.subtype.comp c.equiv.symm.toLinearMap

lemma lift_mem (u : Fin (finrank ℂ t) → ℂ) : c.lift u ∈ t := (c.equiv.symm u).2

lemma proj_lift (u : Fin (finrank ℂ t) → ℂ) : proj c.ι (c.lift u) = u :=
  c.equiv.apply_symm_apply u

lemma lift_apply (u : Fin (finrank ℂ t) → ℂ) (k : Fin (finrank ℂ t)) : c.lift u (c.ι k) = u k :=
  congrFun (c.proj_lift u) k

lemma lift_proj {z : Fin r → ℂ} (hz : z ∈ t) : c.lift (proj c.ι z) = z := by
  have : c.equiv.symm (proj c.ι z) = ⟨z, hz⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [lift, this]

lemma lift_injective : Function.Injective c.lift := fun u v h => by
  rw [← c.proj_lift u, ← c.proj_lift v, h]

lemma range_lift : LinearMap.range c.lift = t := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩; exact c.lift_mem u
  · intro z hz; exact ⟨_, c.lift_proj hz⟩

/-- The lattice points `t ∩ (Λ₁ × ⋯ × Λ_r)`. -/
def lat (Ls : Fin r → PeriodPair) (t : Submodule ℂ (Fin r → ℂ)) : AddSubgroup (Fin r → ℂ) where
  carrier := {z | z ∈ t ∧ ∀ j, z j ∈ (Ls j).lattice}
  add_mem' ha hb := ⟨t.add_mem ha.1 hb.1, fun j => (Ls j).lattice.add_mem (ha.2 j) (hb.2 j)⟩
  zero_mem' := ⟨t.zero_mem, fun j => (Ls j).lattice.zero_mem⟩
  neg_mem' ha := ⟨t.neg_mem ha.1, fun j => (Ls j).lattice.neg_mem (ha.2 j)⟩

variable {Ls : Fin r → PeriodPair}

/-- **Finite index**: every period of `∏ₖ E_{ι k}` has a nonzero multiple that lifts to a period
of `B` (`t ∩ Λ^r` spans `t` over `ℝ`, so its projection has full rank `2 dim t` in `∏ₖ Λ_{ι k}`). -/
theorem exists_nsmul_lift_mem (hab : IsAbelianTangent Ls t) {w : Fin (finrank ℂ t) → ℂ}
    (hw : ∀ k, w k ∈ (Ls (c.ι k)).lattice) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ j, c.lift (n • w) j ∈ (Ls j).lattice := by
  classical
  let A : AddSubgroup (Fin (finrank ℂ t) → ℂ) := (lat Ls t).map (proj c.ι).toAddMonoidHom
  let Λ' : AddSubgroup (Fin (finrank ℂ t) → ℂ) := lat (Ls ∘ c.ι) ⊤
  have hAΛ : A ≤ Λ' := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨Submodule.mem_top, fun k => hz.2 (c.ι k)⟩
  -- the ℚ-span of `Λ'` has dimension `≤ 2s`
  let g : Fin (finrank ℂ t) × Fin 2 → (Fin (finrank ℂ t) → ℂ) := fun p =>
    Pi.single p.1 (if p.2 = 0 then (Ls (c.ι p.1)).ω₁ else (Ls (c.ι p.1)).ω₂)
  have hΛg : (Λ' : Set (Fin (finrank ℂ t) → ℂ)) ⊆ Submodule.span ℚ (Set.range g) := by
    intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp (hx.2 k)
    have : Pi.single k (x k) = a • g (k, 0) + b • g (k, 1) := by
      simp only [g, ← hab, show ((1 : Fin 2) = 0) ↔ False by decide, ite_false]
      ext i
      by_cases hi : i = k
      · subst hi; simp [zsmul_eq_mul]
      · simp [hi]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      (Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  set Q := Submodule.span ℚ (Λ' : Set (Fin (finrank ℂ t) → ℂ))
  have hQle : Q ≤ Submodule.span ℚ (Set.range g) := Submodule.span_le.mpr hΛg
  have : FiniteDimensional ℚ (Submodule.span ℚ (Set.range g)) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range g)
  have hQfd : FiniteDimensional ℚ Q := Submodule.finiteDimensional_of_le hQle
  have hQrank : finrank ℚ Q ≤ finrank ℂ t * 2 :=
    (Submodule.finrank_mono hQle).trans ((finrank_range_le_card g).trans (by simp))
  -- the ℚ-span of `A` has dimension `≥ 2s`
  set P := Submodule.span ℚ (A : Set (Fin (finrank ℂ t) → ℂ))
  have hPQ : P ≤ Q := Submodule.span_mono hAΛ
  have : FiniteDimensional ℚ P := Submodule.finiteDimensional_of_le hPQ
  have hspanR : Submodule.span ℝ (A : Set (Fin (finrank ℂ t) → ℂ)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : c.lift x ∈ t.restrictScalars ℝ := c.lift_mem x
    rw [hab] at hx
    have hmap := Submodule.mem_map_of_mem (f := (proj c.ι).restrictScalars ℝ) hx
    rw [← Submodule.span_image] at hmap
    have heq : ((proj c.ι).restrictScalars ℝ) (c.lift x) = x := c.proj_lift x
    rw [heq] at hmap
    exact Submodule.span_mono (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z, hz, rfl⟩) hmap
  let bP := Module.finBasis ℚ P
  let v : Fin (finrank ℚ P) → (Fin (finrank ℂ t) → ℂ) := fun i => (bP i : Fin (finrank ℂ t) → ℂ)
  have hPv : P = Submodule.span ℚ (Set.range v) := by
    have : Set.range v = P.subtype '' Set.range bP := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bP.span_eq, Submodule.map_subtype_top]
  have hPrank : finrank ℂ t * 2 ≤ finrank ℚ P := by
    have htop : Submodule.span ℝ (Set.range v) = ⊤ := by
      rw [eq_top_iff, ← hspanR, Submodule.span_le]
      intro a ha
      have : a ∈ P := Submodule.subset_span ha
      rw [hPv] at this
      exact Submodule.span_le_restrictScalars ℚ ℝ _ this
    have h1 := finrank_range_le_card (R := ℝ) v
    rw [Set.finrank, htop, finrank_top, Module.finrank_pi_fintype,
      Complex.finrank_real_complex] at h1
    simpa using h1
  have hPQeq : P = Q := Submodule.eq_of_le_of_finrank_le hPQ (hQrank.trans hPrank)
  have hwQ : w ∈ Q := Submodule.subset_span ⟨Submodule.mem_top, hw⟩
  rw [← hPQeq] at hwQ
  obtain ⟨n, hn, z, hz, hzw⟩ := exists_nsmul_mem_of_mem_span A hwQ
  refine ⟨n, hn, fun j => ?_⟩
  have : c.lift (n • w) = z := by
    rw [← hzw]; exact c.lift_proj hz.1
  rw [this]; exact hz.2 j

/-- `lift` maps abelian tangents of `∏ₖ E_{ι k}` to abelian tangents of `E₁ × ⋯ × E_r`. -/
theorem isAbelianTangent_map (hab : IsAbelianTangent Ls t)
    {t'' : Submodule ℂ (Fin (finrank ℂ t) → ℂ)} (hab'' : IsAbelianTangent (Ls ∘ c.ι) t'') :
    IsAbelianTangent Ls (t''.map c.lift) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ t''.restrictScalars ℝ := hu
    rw [hab''] at hu'
    have hmap := Submodule.mem_map_of_mem (f := c.lift.restrictScalars ℝ) hu'
    rw [← Submodule.span_image] at hmap
    refine (Submodule.span_le.mpr ?_) hmap
    rintro _ ⟨w, ⟨hw'', hw⟩, rfl⟩
    obtain ⟨n, hn, hlat⟩ := c.exists_nsmul_lift_mem hab hw
    have hmem : c.lift (n • w) ∈ Submodule.span ℝ
        {z | z ∈ t''.map c.lift ∧ ∀ j, z j ∈ (Ls j).lattice} :=
      Submodule.subset_span ⟨⟨n • w, t''.smul_of_tower_mem n hw'', rfl⟩, hlat⟩
    have : c.lift.restrictScalars ℝ w = (n : ℝ)⁻¹ • c.lift (n • w) := by
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn),
        one_smul]; rfl
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ hmem
  · rw [Submodule.span_le]
    exact fun z hz => hz.1

end Chart

theorem nonempty_chart (t : Submodule ℂ (Fin r → ℂ)) : Nonempty (Chart t) :=
  let ⟨ι, h⟩ := exists_chart t; ⟨⟨ι, h⟩⟩

end LSG.CM
