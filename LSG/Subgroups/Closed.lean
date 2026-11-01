/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Closed subgroups of a finite-dimensional real vector space

For a closed additive subgroup `S` of a finite-dimensional real normed space `E`:

* `linPart S` is the largest subspace contained in `S` (`{v | ∀ s : ℝ, s • v ∈ S}`);
* `exists_discrete`: `S` meets every complement `W` of `linPart S` discretely;
* `eq_linPart_add`: `S = linPart S + (S ∩ W)`.

This is the classical structure theorem `S ≅ ℝ^a × ℤ^b`, in the form needed to turn a closed
subgroup of a complex torus `ℂ^m / Λ` (e.g. a Zariski-closed subgroup of `E₁ × ⋯ × E_m`) into its
tangent space: the preimage `S̃` of the subgroup is closed and contains `Λ`, and its linear part
is the Lie algebra of the identity component.
-/

open Filter Topology Metric

namespace LSG.Subgroups

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The largest real subspace contained in the additive subgroup `S`. -/
def linPart (S : AddSubgroup E) : Submodule ℝ E where
  carrier := {v | ∀ s : ℝ, s • v ∈ S}
  add_mem' {a b} ha hb s := by rw [smul_add]; exact S.add_mem (ha s) (hb s)
  zero_mem' s := by simp
  smul_mem' c v hv s := by
    show s • c • v ∈ S
    rw [smul_smul]; exact hv _

theorem mem_linPart {S : AddSubgroup E} {v : E} : v ∈ linPart S ↔ ∀ s : ℝ, s • v ∈ S := Iff.rfl

theorem linPart_subset (S : AddSubgroup E) : (linPart S : Set E) ⊆ S := fun v hv => by
  simpa using hv 1

/-- If `s • u` is a limit of integer multiples `nₖ • wₖ` with `wₖ ∈ S`, `‖wₖ‖ → 0` and
`wₖ / ‖wₖ‖ → u`, then `s • u ∈ closure S`. The key step of `exists_discrete`. -/
theorem smul_mem_of_tendsto {S : AddSubgroup E} (hS : IsClosed (S : Set E)) {w : ℕ → E}
    (hwS : ∀ k, w k ∈ S) (hw0 : ∀ k, w k ≠ 0) (hlim : Tendsto (fun k => ‖w k‖) atTop (𝓝 0))
    {u : E} (hu : Tendsto (fun k => ‖w k‖⁻¹ • w k) atTop (𝓝 u)) (s : ℝ) : s • u ∈ S := by
  set n : ℕ → ℤ := fun k => ⌊s / ‖w k‖⌋ with hn
  have hpos : ∀ k, 0 < ‖w k‖ := fun k => norm_pos_iff.mpr (hw0 k)
  -- `nₖ ‖wₖ‖ → s`
  have hc : Tendsto (fun k => (n k : ℝ) * ‖w k‖) atTop (𝓝 s) := by
    have hbound : ∀ k, |(n k : ℝ) * ‖w k‖ - s| ≤ ‖w k‖ := by
      intro k
      have h1 := Int.floor_le (s / ‖w k‖)
      have h2 := Int.lt_floor_add_one (s / ‖w k‖)
      have hk := hpos k
      have e1 : (n k : ℝ) * ‖w k‖ ≤ s := by
        have := mul_le_mul_of_nonneg_right h1 hk.le
        rwa [div_mul_cancel₀ _ hk.ne'] at this
      have e2 : s < ((n k : ℝ) + 1) * ‖w k‖ := by
        have := mul_lt_mul_of_pos_right h2 hk
        rwa [div_mul_cancel₀ _ hk.ne'] at this
      rw [abs_le]; constructor <;> nlinarith
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => by
      rw [Real.norm_eq_abs]; exact hbound k) hlim
  have hmem : ∀ k, ((n k : ℝ) * ‖w k‖) • (‖w k‖⁻¹ • w k) ∈ S := by
    intro k
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hpos k).ne', mul_one]
    have : ((n k : ℝ)) • w k = n k • w k := by rw [Int.cast_smul_eq_zsmul]
    rw [this]
    exact S.zsmul_mem (hwS k) _
  exact hS.mem_of_tendsto (hc.smul hu) (Eventually.of_forall hmem)

variable [FiniteDimensional ℝ E]

/-- **A closed subgroup meets a complement of its linear part discretely.** -/
theorem exists_discrete (S : AddSubgroup E) (hS : IsClosed (S : Set E)) (W : Submodule ℝ E)
    (hW : linPart S ⊓ W = ⊥) :
    ∃ ε > 0, ∀ w ∈ W, w ∈ S → w ≠ 0 → ε ≤ ‖w‖ := by
  by_contra hcon
  push Not at hcon
  -- a sequence of nonzero elements of `S ∩ W` tending to `0`
  have hseq : ∀ k : ℕ, ∃ w ∈ W, w ∈ S ∧ w ≠ 0 ∧ ‖w‖ < 1 / ((k : ℝ) + 1) := fun k =>
    hcon _ (by positivity)
  choose w hwW hwS hw0 hwlt using hseq
  have hlim : Tendsto (fun k => ‖w k‖) atTop (𝓝 0) :=
    squeeze_zero (fun k => norm_nonneg _) (fun k => (hwlt k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- normalise: the unit vectors lie in the compact set `W ∩ sphere 0 1`
  have hWc : IsClosed (W : Set E) := W.closed_of_finiteDimensional
  have hK : IsCompact ((W : Set E) ∩ sphere (0 : E) 1) :=
    (isCompact_sphere 0 1).inter_left hWc
  have hu_mem : ∀ k, ‖w k‖⁻¹ • w k ∈ (W : Set E) ∩ sphere (0 : E) 1 := by
    intro k
    refine ⟨W.smul_mem _ (hwW k), ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hw0 k))]
  obtain ⟨u, ⟨huW, hu1⟩, φ, hφ, hu⟩ := hK.tendsto_subseq hu_mem
  -- every real multiple of `u` lies in `S`
  have hlin : u ∈ linPart S := fun s =>
    smul_mem_of_tendsto hS (fun k => hwS (φ k)) (fun k => hw0 (φ k))
      (hlim.comp hφ.tendsto_atTop) hu s
  have : u ∈ linPart S ⊓ W := ⟨hlin, huW⟩
  rw [hW, Submodule.mem_bot] at this
  rw [mem_sphere_zero_iff_norm, this, norm_zero] at hu1
  exact zero_ne_one hu1

omit [FiniteDimensional ℝ E] in
/-- `S = linPart S + (S ∩ W)` for a complement `W` of `linPart S`. -/
theorem eq_linPart_add (S : AddSubgroup E) (W : Submodule ℝ E) (hW : IsCompl (linPart S) W)
    {x : E} (hx : x ∈ S) : ∃ v ∈ linPart S, ∃ w ∈ W, w ∈ S ∧ x = v + w := by
  obtain ⟨v, w, hv, hw, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hW.codisjoint x
  refine ⟨v, hv, w, hw, ?_, rfl⟩
  have := S.sub_mem hx (linPart_subset S hv)
  simpa using this

end LSG.Subgroups
