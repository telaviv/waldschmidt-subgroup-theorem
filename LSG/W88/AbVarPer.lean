/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.MEB.Stmt
import LSG.W88.StatementAbVar

/-!
# A5.1: the finite-index bridge between period groups (`STAGE_A5.md` D5)

MEB's blocks carry their full kernel `per` (for the `A`-block, γ's `per = kerE G`), while lean_lsg's statements count
periods in a sublattice (`latt`). A discrete subgroup containing the `ℤ`-span of an `ℝ`-basis lies in its `ℚ`-span
(`exists_nsmul_mem_zspan`), so every period-dependent quantity of W88 agrees for the two groups.

* **Generic.** `IsNsmulIn L P`: every element of `P` has a positive multiple in `L`. Under `L ≤ P` and
  `IsNsmulIn L P`: `span_ℚ L = span_ℚ P`, `rk (Y ⊓ L) = rk (Y ⊓ P)`, `IsRatSub L t ↔ IsRatSub P t`, and
  `N • u ∈ T ⊔ P ⇒ N' • u ∈ T ⊔ L`.
* **Discrete groups.** `exists_nsmul_mem_zspan` (fractional parts in a fundamental domain, pigeonhole).
* **MEB.** `PerL d₀ d₁ B Λ = 0 × 2πiℤ^{d₁} × ∏ Λ_k` for sublattices `Λ_k ≤ per_k`; `perL_le`, `isNsmulIn_perL`,
  `isRatSub_perAb_iff`, `htil_perL`.
* **`A`.** `discreteTopology_kerE`, `isNsmulIn_latt_kerE`: `kerE G ⊆ ℚ · latt`.
-/

open Module Submodule

noncomputable section

namespace LSG.W88

/-! ### Generic commensurability -/

section Generic

variable {E : Type*} [AddCommGroup E]

/-- Every element of `P` has a positive multiple in `L`. -/
def IsNsmulIn (L P : AddSubgroup E) : Prop := ∀ ω ∈ P, ∃ N : ℕ, 0 < N ∧ N • ω ∈ L

lemma IsNsmulIn.inf {L P : AddSubgroup E} (h : IsNsmulIn L P) (Y : AddSubgroup E) :
    IsNsmulIn (Y ⊓ L) (Y ⊓ P) := fun ω hω => by
  obtain ⟨N, hN, hNω⟩ := h ω hω.2
  exact ⟨N, hN, Y.nsmul_mem hω.1 N, hNω⟩

lemma IsNsmulIn.mono_left {L L' P : AddSubgroup E} (h : IsNsmulIn L P) (hL : L ≤ L') : IsNsmulIn L' P :=
  fun ω hω => by
    obtain ⟨N, hN, hNω⟩ := h ω hω
    exact ⟨N, hN, hL hNω⟩

/-- `N • u ∈ T ⊔ P` gives a positive multiple of `u` in `T ⊔ L`. -/
lemma IsNsmulIn.sup_nsmul {L P : AddSubgroup E} (h : IsNsmulIn L P) (T : AddSubgroup E) {u : E} {N : ℕ}
    (hN : 0 < N) (hu : N • u ∈ T ⊔ P) : ∃ N' : ℕ, 0 < N' ∧ N' • u ∈ T ⊔ L := by
  obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hu
  obtain ⟨M, hM, hMz⟩ := h z hz
  refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
  rw [mul_smul, ← hyz, smul_add]
  exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (T.nsmul_mem hy M))
    (AddSubgroup.mem_sup_right hMz)

variable [Module ℚ E]

lemma mem_span_rat_of_nsmul {S : Set E} {ω : E} {N : ℕ} (hN : 0 < N) (h : N • ω ∈ span ℚ S) :
    ω ∈ span ℚ S := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have : ω = (N : ℚ)⁻¹ • (N • ω) := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hN', one_smul]
  rw [this]; exact Submodule.smul_mem _ _ h

/-- **Commensurable groups have the same `ℚ`-span.** -/
theorem span_rat_eq_of_nsmul {L P : AddSubgroup E} (hLP : L ≤ P) (h : IsNsmulIn L P) :
    span ℚ (L : Set E) = span ℚ (P : Set E) := by
  refine le_antisymm (span_mono hLP) (span_le.mpr fun ω hω => ?_)
  obtain ⟨N, hN, hNω⟩ := h ω hω
  exact mem_span_rat_of_nsmul hN (subset_span hNω)

/-- **The rank `κ` does not see the finite index.** -/
theorem rk_inf_eq_of_nsmul {L P : AddSubgroup E} (hLP : L ≤ P) (h : IsNsmulIn L P) (Y : AddSubgroup E) :
    rk (Y ⊓ L) = rk (Y ⊓ P) := by
  unfold rk
  rw [span_rat_eq_of_nsmul (inf_le_inf_left Y hLP) (h.inf Y)]

end Generic

section RatSub

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]

omit [IsScalarTower ℝ ℂ V] in
lemma span_real_inter_eq {L P : AddSubgroup V} (hLP : L ≤ P) (h : IsNsmulIn L P) (t : Submodule ℂ V) :
    span ℝ {z | z ∈ t ∧ z ∈ L} = span ℝ {z | z ∈ t ∧ z ∈ P} := by
  refine le_antisymm (span_mono fun z hz => ⟨hz.1, hLP hz.2⟩) (span_le.mpr fun z hz => ?_)
  obtain ⟨N, hN, hNz⟩ := h z hz.2
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hz' : z = (N : ℝ)⁻¹ • (N • z) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN', one_smul]
  rw [hz']
  refine Submodule.smul_mem _ _ (subset_span ⟨?_, hNz⟩)
  exact t.toAddSubgroup.nsmul_mem hz.1 N

/-- **Rationality of a tangent space does not see the finite index.** -/
theorem isRatSub_iff_of_nsmul {L P : AddSubgroup V} (hLP : L ≤ P) (h : IsNsmulIn L P) (t : Submodule ℂ V) :
    LSG.MEB.IsRatSub L t ↔ LSG.MEB.IsRatSub P t := by
  unfold LSG.MEB.IsRatSub
  rw [span_real_inter_eq hLP h t]

end RatSub

/-! ### Discrete groups containing a full lattice -/

/-- **A discrete group containing the `ℤ`-span of an `ℝ`-basis lies in its `ℚ`-span.** -/
theorem exists_nsmul_mem_zspan {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] (b : Basis ι ℝ E) (P : AddSubgroup E) [DiscreteTopology P] (hb : ∀ i, b i ∈ P) {ω : E}
    (hω : ω ∈ P) : ∃ N : ℕ, 0 < N ∧ N • ω ∈ span ℤ (Set.range b) := by
  have := Fintype.ofFinite ι
  have hZP : ∀ v ∈ span ℤ (Set.range b), v ∈ P := by
    intro v hv
    have hv' : v ∈ (span ℤ (Set.range b)).toAddSubgroup := hv
    rw [Submodule.span_int_eq_addSubgroupClosure] at hv'
    exact (AddSubgroup.closure_le P).mpr (by rintro _ ⟨i, rfl⟩; exact hb i) hv'
  have hP : IsClosed (P : Set E) := AddSubgroup.isClosed_of_discreteTopology
  have hfin : Set.Finite (ZSpan.fundamentalDomain b ∩ (P : Set E)) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete (ZSpan.fundamentalDomain_isBounded b) hP
  have hmem : ∀ n : ℕ, ZSpan.fract b (n • ω) ∈ ZSpan.fundamentalDomain b ∩ (P : Set E) := fun n => by
    refine ⟨ZSpan.fract_mem_fundamentalDomain b _, ?_⟩
    rw [ZSpan.fract_apply]
    exact P.sub_mem (P.nsmul_mem hω n) (hZP _ (ZSpan.floor b _).2)
  obtain ⟨n₁, n₂, hlt, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem hmem hfin
  refine ⟨n₂ - n₁, Nat.sub_pos_of_lt hlt, ?_⟩
  have h := (ZSpan.fract_eq_fract b _ _).mp heq
  have e : -(n₁ • ω) + n₂ • ω = (n₂ - n₁) • ω := by
    rw [sub_nsmul ω hlt.le]; abel
  rwa [e] at h

/-- The `AddSubgroup` form: `P ⊆ ℚ · closure (range b)`. -/
theorem isNsmulIn_closure_basis {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] (b : Basis ι ℝ E) (P : AddSubgroup E) [DiscreteTopology P] (hb : ∀ i, b i ∈ P) :
    IsNsmulIn (AddSubgroup.closure (Set.range b)) P := fun ω hω => by
  obtain ⟨N, hN, h⟩ := exists_nsmul_mem_zspan b P hb hω
  refine ⟨N, hN, ?_⟩
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  exact h

end LSG.W88

/-! ### MEB period groups with sublattices -/

namespace LSG.MEB

open LSG.W88

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

variable (d₀ d₁ B) in
/-- **Periods counted in sublattices** `Λ_k ≤ per_k`: `0 × 2πiℤ^{d₁} × ∏_k Λ_k`. -/
def PerL (Λ : ∀ k, AddSubgroup (Fin (B k).g → ℂ)) : AddSubgroup (Tan d₀ d₁ B) where
  carrier := {p | p.1 = 0 ∧ (∀ i, ∃ k : ℤ, p.2.1 i = 2 * Real.pi * Complex.I * k) ∧ ∀ k, p.2.2 k ∈ Λ k}
  add_mem' {p q} hp hq := by
    refine ⟨by simp [hp.1, hq.1], fun i => ?_, fun k => (Λ k).add_mem (hp.2.2 k) (hq.2.2 k)⟩
    obtain ⟨a, ha⟩ := hp.2.1 i
    obtain ⟨b, hb⟩ := hq.2.1 i
    exact ⟨a + b, by change p.2.1 i + q.2.1 i = _; rw [ha, hb]; push_cast; ring⟩
  zero_mem' := ⟨rfl, fun _ => ⟨0, by simp⟩, fun k => (Λ k).zero_mem⟩
  neg_mem' {p} hp := by
    refine ⟨by simp [hp.1], fun i => ?_, fun k => (Λ k).neg_mem (hp.2.2 k)⟩
    obtain ⟨a, ha⟩ := hp.2.1 i
    exact ⟨-a, by change -p.2.1 i = _; rw [ha]; push_cast; ring⟩

variable {Λ : ∀ k, AddSubgroup (Fin (B k).g → ℂ)}

theorem perL_le (hΛ : ∀ k, Λ k ≤ (B k).per) : PerL d₀ d₁ B Λ ≤ Per d₀ d₁ B :=
  fun _ hp => ⟨hp.1, hp.2.1, fun k => hΛ k (hp.2.2 k)⟩

/-- A common multiplier for finitely many blocks. -/
lemma _root_.LSG.W88.exists_common_mult {ι : Type*} [Finite ι] (P : ι → Prop) (Q : ι → ℕ → Prop)
    (hQ : ∀ i N M, Q i N → Q i (M * N)) (h : ∀ i, P i → ∃ N, 0 < N ∧ Q i N) (hP : ∀ i, P i) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, Q i N := by
  classical
  have := Fintype.ofFinite ι
  choose N hN hQN using fun i => h i (hP i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  rw [hc, mul_comm]
  exact hQ i _ _ (hQN i)

theorem isNsmulIn_perL (hΛ : ∀ k, IsNsmulIn (Λ k) (B k).per) :
    IsNsmulIn (PerL d₀ d₁ B Λ) (Per d₀ d₁ B) := by
  intro ω hω
  obtain ⟨N, hN, hNk⟩ := exists_common_mult (fun k => ω.2.2 k ∈ (B k).per) (fun k N => N • ω.2.2 k ∈ Λ k)
    (fun k N M h => by rw [mul_smul]; exact (Λ k).nsmul_mem h M) (fun k hk => hΛ k _ hk) hω.2.2
  refine ⟨N, hN, ?_, fun i => ?_, fun k => hNk k⟩
  · change N • ω.1 = 0; rw [hω.1, smul_zero]
  · obtain ⟨a, ha⟩ := hω.2.1 i
    exact ⟨N * a, by change N • ω.2.1 i = _; rw [ha, nsmul_eq_mul]; push_cast; ring⟩

/-- The abelian part of `PerL`. -/
def perAbL (Λ : ∀ k, AddSubgroup (Fin (B k).g → ℂ)) : AddSubgroup (∀ k, Fin (B k).g → ℂ) :=
  AddSubgroup.pi Set.univ Λ

theorem perAbL_le (hΛ : ∀ k, Λ k ≤ (B k).per) : perAbL Λ ≤ perAb B :=
  fun _ hp k _ => hΛ k (hp k (Set.mem_univ k))

theorem isNsmulIn_perAbL (hΛ : ∀ k, IsNsmulIn (Λ k) (B k).per) : IsNsmulIn (perAbL Λ) (perAb B) := by
  intro ω hω
  obtain ⟨N, hN, hNk⟩ := exists_common_mult (fun k => ω k ∈ (B k).per) (fun k N => N • ω k ∈ Λ k)
    (fun k N M h => by rw [mul_smul]; exact (Λ k).nsmul_mem h M) (fun k hk => hΛ k _ hk)
    (fun k => hω k (Set.mem_univ k))
  exact ⟨N, hN, fun k _ => hNk k⟩

/-- **`t_rat` in terms of the sublattices.** -/
theorem isRatSub_perAb_iff (hΛle : ∀ k, Λ k ≤ (B k).per) (hΛ : ∀ k, IsNsmulIn (Λ k) (B k).per)
    (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : IsRatSub (perAbL Λ) t ↔ IsRatSub (perAb B) t :=
  isRatSub_iff_of_nsmul (perAbL_le hΛle) (isNsmulIn_perAbL hΛ) t

/-- **`htil` with the sublattices.** -/
theorem ObstrDataB.htil_perL (O : ObstrDataB d₀ d₁ B) (hΛ : ∀ k, IsNsmulIn (Λ k) (B k).per)
    {u : Tan d₀ d₁ B} (hu : expG d₀ d₁ B u ∈ O.grp) :
    ∃ N : ℕ, 0 < N ∧ N • u ∈ O.tan.toAddSubgroup ⊔ PerL d₀ d₁ B Λ := by
  obtain ⟨N, hN, h⟩ := O.htil u hu
  exact (isNsmulIn_perL hΛ).sup_nsmul _ hN h

/-- `ℚ`-spans of the two period groups agree. -/
theorem span_perL (hΛle : ∀ k, Λ k ≤ (B k).per) (hΛ : ∀ k, IsNsmulIn (Λ k) (B k).per) :
    span ℚ (PerL d₀ d₁ B Λ : Set (Tan d₀ d₁ B)) = span ℚ (Per d₀ d₁ B : Set (Tan d₀ d₁ B)) :=
  span_rat_eq_of_nsmul (perL_le hΛle) (isNsmulIn_perL hΛ)

/-- Ranks of `Y ∩ periods` agree. -/
theorem rk_inf_perL (hΛle : ∀ k, Λ k ≤ (B k).per) (hΛ : ∀ k, IsNsmulIn (Λ k) (B k).per)
    (Y : AddSubgroup (Tan d₀ d₁ B)) : rk (Y ⊓ PerL d₀ d₁ B Λ) = rk (Y ⊓ Per d₀ d₁ B) :=
  rk_inf_eq_of_nsmul (perL_le hΛle) (isNsmulIn_perL hΛ) Y

/-- **A block lattice from an `ℝ`-basis of periods**: `per_k ⊆ ℚ · closure (range b)`. -/
theorem AbBlock.isNsmulIn_of_basis (b' : AbBlock) {ι : Type*} [Finite ι] (b : Basis ι ℝ (Fin b'.g → ℂ))
    (hb : ∀ i, b i ∈ b'.per) : IsNsmulIn (AddSubgroup.closure (Set.range b)) b'.per :=
  have := b'.per_discrete
  isNsmulIn_closure_basis b b'.per hb

end LSG.MEB

/-! ### The `A`-block: `kerE ⊆ ℚ · latt` -/

namespace LSG.W88

open LSG.JacAn

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}

/-- `kerE` is discrete (`expP_ker_discrete`). -/
theorem discreteTopology_kerE (G : GermRad A hp hx) : DiscreteTopology (kerE G) := by
  obtain ⟨r, hr, h⟩ := expP_ker_discrete G
  refine DiscreteTopology.of_forall_le_dist hr fun c c' hne => ?_
  by_contra hlt
  push Not at hlt
  exact hne (Subtype.ext (h c c' c.2 c'.2 hlt))

lemma latt_eq_closure_basis : latt = AddSubgroup.closure (Set.range latBasis) := by
  unfold latt
  congr 1
  ext v
  simp [latBasis_apply]

/-- **`kerE G ⊆ ℚ · latt`**: the finite-index bridge for the `A`-block. -/
theorem isNsmulIn_latt_kerE (G : GermRad A hp hx) : IsNsmulIn latt (kerE G) := by
  have := discreteTopology_kerE G
  rw [latt_eq_closure_basis]
  exact isNsmulIn_closure_basis latBasis (kerE G) fun e => by
    rw [latBasis_apply]
    exact latt_le_kerE G (AddSubgroup.subset_closure ⟨e, rfl⟩)

end LSG.W88
