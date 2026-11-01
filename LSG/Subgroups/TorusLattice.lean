/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Subgroups.Closed

/-!
# Closed subgroups containing a full lattice

Let `E` be a finite-dimensional real normed space, `L ⊂ E` a discrete `ℤ`-submodule spanning `E`
over `ℝ` (a full lattice), and `S ⊂ E` a closed additive subgroup with `L ⊆ S`. Put
`V = linPart S`, the largest real subspace inside `S`.

* `span_linPart_inter_lattice`: the lattice points of `V` span `V` over `ℝ`, i.e. `V ∩ L` is a full
  lattice in `V` (so `V / (V ∩ L)` is a compact subtorus of `E / L`);
* `exists_finset_cosets`: `S` is a finite union of cosets of `V + L`.

Geometrically: the image of `S` in the torus `E / L` is a closed subgroup, its identity component is
the subtorus `V / (V ∩ L)`, and it has finitely many components.

Proof of the first statement: pick a complement `W` of `V` and let `q` be the projection onto `W`
along `V`. Since `l - q l ∈ V ⊆ S`, `q` maps `L` into `S ∩ W`, which is discrete
(`exists_discrete`); so `q(L)` has `ℤ`-rank `≤ dim W`. Rank–nullity for `q|_L` (over `ℤ`)
shows that its kernel `L ∩ V` has `ℤ`-rank `≥ dim E - dim W = dim V`, and for a discrete group
the `ℤ`-rank is the dimension of the `ℝ`-span. The second statement reduces `x ∈ S` modulo `L`
into a bounded set (`ZSpan.fract`), and then projects to `W`, where only finitely many points of
`S ∩ W` lie in a bounded set.
-/

open Module Metric

namespace LSG.Subgroups

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A `ℤ`-submodule all of whose nonzero elements have norm `≥ ε > 0` is discrete. -/
theorem discreteTopology_of_norm_ge (M : Submodule ℤ E) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x ∈ M, x ≠ 0 → ε ≤ ‖x‖) : DiscreteTopology M :=
  DiscreteTopology.of_forall_le_dist hε fun x y hxy => by
    change ε ≤ dist x y
    rw [Subtype.dist_eq, dist_eq_norm]
    exact h _ (M.sub_mem x.2 y.2) (sub_ne_zero.mpr fun e => hxy (Subtype.ext e))

/-- With `W` a complement of `linPart S` and `q` the projection onto `W` along `linPart S`,
`x - q x ∈ linPart S`. -/
theorem sub_projection_mem_linPart {S : AddSubgroup E} {W : Submodule ℝ E}
    (hc : IsCompl (linPart S) W) (x : E) :
    x - W.projection (linPart S) hc.symm x ∈ linPart S := by
  rw [← Submodule.projection_eq_self_sub_projection hc.symm]
  exact Submodule.projection_apply_mem _ _

/-- The projection onto a complement `W` of `linPart S` along `linPart S` maps `S` into `S`. -/
theorem projection_mem_of_mem {S : AddSubgroup E} {W : Submodule ℝ E}
    (hc : IsCompl (linPart S) W) {x : E} (hx : x ∈ S) :
    W.projection (linPart S) hc.symm x ∈ S := by
  have := S.sub_mem hx (linPart_subset S (sub_projection_mem_linPart hc x))
  simpa using this

variable [FiniteDimensional ℝ E]

/-- For a discrete `ℤ`-submodule `M`, the `ℤ`-rank of `M` is the `ℝ`-dimension of its `ℝ`-span. -/
theorem finrank_int_eq_of_discrete (M : Submodule ℤ E) [DiscreteTopology M] :
    finrank ℤ M = finrank ℝ (Submodule.span ℝ (M : Set E)) := by
  have h : DiscreteTopology (Submodule.span ℤ (M : Set E)) := (Submodule.span_eq M).symm ▸ ‹_›
  have := Real.finrank_eq_int_finrank_of_discrete h
  rw [Set.finrank, Set.finrank, Submodule.span_eq] at this
  exact this.symm

section Lattice

variable (L : Submodule ℤ E) [DiscreteTopology L] (S : AddSubgroup E)

/-- **The lattice points of the linear part span it.** If `L` is a full lattice in `E` (discrete,
spanning `E` over `ℝ`) and `S ⊇ L` is a closed subgroup, then `linPart S ∩ L` spans `linPart S`
over `ℝ`. -/
theorem span_linPart_inter_lattice (hspan : Submodule.span ℝ (L : Set E) = ⊤)
    (hS : IsClosed (S : Set E)) (hLS : (L : Set E) ⊆ S) :
    Submodule.span ℝ ((linPart S : Set E) ∩ L) = linPart S := by
  obtain ⟨W, hc⟩ := (linPart S).exists_isCompl
  obtain ⟨ε, hε, hdisc⟩ := exists_discrete S hS W hc.inf_eq_bot
  let q := W.projection (linPart S) hc.symm
  let f : L →ₗ[ℤ] E := (q.restrictScalars ℤ) ∘ₗ L.subtype
  -- the image `q(L)` lies in the discrete set `S ∩ W`
  have hrange_disc : DiscreteTopology (LinearMap.range f) := by
    refine discreteTopology_of_norm_ge _ hε ?_
    rintro _ ⟨l, rfl⟩ hne
    exact hdisc _ (Submodule.projection_apply_mem _ _) (projection_mem_of_mem hc (hLS l.2)) hne
  have hrange : finrank ℤ (LinearMap.range f) ≤ finrank ℝ W := by
    rw [finrank_int_eq_of_discrete]
    apply Submodule.finrank_mono
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact Submodule.projection_apply_mem _ _
  -- the kernel of `q|_L` is `L ∩ linPart S`
  let K : Submodule ℤ E := L ⊓ (linPart S).restrictScalars ℤ
  have hker : LinearMap.ker f = K.comap L.subtype := by
    ext l
    simp [f, q, K]
  have hK : finrank ℤ (LinearMap.ker f) = finrank ℤ K := by
    rw [hker]; exact (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  have hL : finrank ℤ L = finrank ℝ E := by
    rw [finrank_int_eq_of_discrete, hspan, finrank_top]
  have hrn := f.finrank_range_add_finrank_ker
  have hVW := Submodule.finrank_add_eq_of_isCompl hc
  have : DiscreteTopology K :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : K => (⟨x.1, x.2.1⟩ : L))
      (continuous_subtype_val.subtype_mk _)
      (fun x y h => Subtype.ext (by simpa using h))
  have hKV : Submodule.span ℝ (K : Set E) ≤ linPart S :=
    Submodule.span_le.mpr fun x hx => hx.2
  have hcoe : (linPart S : Set E) ∩ L = K := Set.inter_comm _ _
  rw [hcoe]
  apply Submodule.eq_of_le_of_finrank_le hKV
  rw [← finrank_int_eq_of_discrete]
  omega

/-- **Finitely many components.** If `L` is a full lattice in `E` and `S ⊇ L` is a closed subgroup,
then `S` is a finite union of cosets of `linPart S + L`: there is a finite `F ⊆ S` with
`S = F + linPart S + L`. -/
theorem exists_finset_cosets (hspan : Submodule.span ℝ (L : Set E) = ⊤)
    (hS : IsClosed (S : Set E)) (hLS : (L : Set E) ⊆ S) :
    ∃ F : Finset E, (F : Set E) ⊆ S ∧
      ∀ x ∈ S, ∃ f ∈ F, ∃ v ∈ linPart S, ∃ l ∈ L, x = f + v + l := by
  classical
  obtain ⟨W, hc⟩ := (linPart S).exists_isCompl
  obtain ⟨ε, hε, hdisc⟩ := exists_discrete S hS W hc.inf_eq_bot
  let q := W.projection (linPart S) hc.symm
  have : IsZLattice ℝ L := ⟨hspan⟩
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hb : Submodule.span ℤ (Set.range b) = L :=
    (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L
  let qc := LinearMap.toContinuousLinearMap q
  let R := ‖qc‖ * ∑ i, ‖b i‖
  -- the finitely many points of `S ∩ W` of norm `≤ R`
  let T : Set E := ((S : Set E) ∩ W) ∩ closedBall 0 R
  have hTc : IsCompact T :=
    (isCompact_closedBall 0 R).inter_left (hS.inter W.closed_of_finiteDimensional)
  have hTd : IsDiscrete T := isDiscrete_iff_discreteTopology.mpr <|
    DiscreteTopology.of_forall_le_dist hε fun x y hxy => by
      change ε ≤ dist x y
      rw [Subtype.dist_eq, dist_eq_norm]
      exact hdisc _ (W.sub_mem x.2.1.2 y.2.1.2) (S.sub_mem x.2.1.1 y.2.1.1)
        (sub_ne_zero.mpr fun e => hxy (Subtype.ext e))
  have hTf := hTc.finite hTd
  refine ⟨hTf.toFinset, fun x hx => ((hTf.mem_toFinset).mp hx).1.1, fun x hx => ?_⟩
  -- reduce `x` modulo `L` into the fundamental domain
  have hl : (ZSpan.floor b x : E) ∈ L := hb.le (ZSpan.floor b x).2
  have hfr : ZSpan.fract b x = x - ZSpan.floor b x := ZSpan.fract_apply b x
  have hy : ZSpan.fract b x ∈ S := by
    rw [hfr]; exact S.sub_mem hx (hLS hl)
  refine ⟨q (ZSpan.fract b x), hTf.mem_toFinset.mpr ⟨⟨projection_mem_of_mem hc hy,
    Submodule.projection_apply_mem _ _⟩, ?_⟩, ZSpan.fract b x - q (ZSpan.fract b x),
    sub_projection_mem_linPart hc _, _, hl, ?_⟩
  · rw [mem_closedBall_zero_iff]
    calc ‖q (ZSpan.fract b x)‖ = ‖qc (ZSpan.fract b x)‖ := rfl
      _ ≤ ‖qc‖ * ‖ZSpan.fract b x‖ := qc.le_opNorm _
      _ ≤ R := mul_le_mul_of_nonneg_left (ZSpan.norm_fract_le b x) (norm_nonneg _)
  · rw [hfr]; abel

end Lattice

end LSG.Subgroups
