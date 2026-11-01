/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# A nonzero maximal minor of a `ℤ`-independent family of integer vectors

Bridge item (a) of `STAGE3_D2.md`: if `P_1, …, P_κ ∈ ℤ^ι` are `ℤ`-linearly independent, some
`κ × κ` minor `(P_i(I_t))_{t,i}` (with `I : Fin κ → ι` injective) has nonzero determinant. This is
the hypothesis `(minorMat P I).det ≠ 0` of `LSG.Aux.prop21Lat`.

Proof: pass to `ℚ` (`LinearIndependent.iff_fractionRing`); the `ι × κ` matrix with columns `P_i`
has rank `κ`, so its rows span `ℚ^κ`; extract `κ` linearly independent rows
(`exists_linearIndependent'`); the corresponding square matrix is invertible.

* `LSG.Aux.exists_minor_ne_zero`.
-/

open Module

namespace LSG.Aux

/-- **A nonzero maximal minor, over a field.** If `Q_1, …, Q_κ ∈ K^ι` are linearly independent,
some `κ × κ` minor `(Q_i(I_t))_{t,i}` is invertible. -/
theorem exists_minor_isUnit {K : Type*} [Field K] {ι : Type*} [Finite ι] {κ : ℕ}
    (Q : Fin κ → ι → K) (hQ : LinearIndependent K Q) :
    ∃ I : Fin κ → ι, Function.Injective I ∧ IsUnit (Matrix.of fun t i => Q i (I t)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let A : Matrix ι (Fin κ) K := Matrix.of fun c i => Q i c
  have hrankT : A.transpose.rank = κ := by
    have : LinearIndependent K A.transpose.row := by
      convert hQ using 1
      funext i c; simp [A, Matrix.row, Matrix.transpose]
    rw [this.rank_matrix, Fintype.card_fin]
  have hspan : Submodule.span K (Set.range A.row) = ⊤ := by
    have h1 : finrank K (Submodule.span K (Set.range A.row)) = κ := by
      rw [← Matrix.rank_eq_finrank_span_row, ← Matrix.rank_transpose, hrankT]
    apply Submodule.eq_top_of_finrank_eq
    rw [h1, finrank_fin_fun]
  obtain ⟨κ', a, ha, hsp, hli⟩ := exists_linearIndependent' K A.row
  have : Finite κ' := Finite.of_injective a ha
  let _ : Fintype κ' := Fintype.ofFinite κ'
  have hcard : Fintype.card κ' = κ := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.mp hli
    rw [Set.finrank, hsp, hspan, finrank_top, finrank_fin_fun] at h1
    exact h1
  let e : Fin κ ≃ κ' := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hrows : LinearIndependent K (Matrix.of fun t i => Q i ((a ∘ e) t)).row := by
    have : (Matrix.of fun t i => Q i ((a ∘ e) t)).row = (A.row ∘ a) ∘ e := by
      funext t i; simp [A, Matrix.row, Function.comp]
    rw [this]
    exact hli.comp e e.injective
  exact Matrix.linearIndependent_row_iff_isUnit.mp hrows

/-- **A nonzero maximal minor.** -/
theorem exists_minor_ne_zero {ι : Type*} [Finite ι] {κ : ℕ} (P : Fin κ → ι → ℤ)
    (hP : LinearIndependent ℤ P) :
    ∃ I : Fin κ → ι, Function.Injective I ∧ (Matrix.of fun t i => P i (I t)).det ≠ 0 := by
  classical
  let castL : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) := (Int.castAddHom ℚ).toIntLinearMap.compLeft ι
  have hcast : Function.Injective castL := fun x y h => by
    funext c
    have := congrFun h c
    simpa [castL] using this
  let Q : Fin κ → ι → ℚ := fun i c => (P i c : ℚ)
  have hQZ : LinearIndependent ℤ Q := by
    have := hP.map' castL (LinearMap.ker_eq_bot.mpr hcast)
    convert this using 1
    funext i c; simp [Q, castL]
  have hQ : LinearIndependent ℚ Q := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hQZ
  obtain ⟨I, hI, hunit⟩ := exists_minor_isUnit Q hQ
  refine ⟨I, hI, ?_⟩
  set N : Matrix (Fin κ) (Fin κ) ℤ := Matrix.of fun t i => P i (I t)
  have hN : N.map (Int.castRingHom ℚ) = Matrix.of fun t i => Q i (I t) := by
    ext t i; simp [N, Q]
  have hdet : (N.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [hN]; exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have hmap : (N.map (Int.castRingHom ℚ)).det = ((N.det : ℤ) : ℚ) :=
    (RingHom.map_det (Int.castRingHom ℚ) N).symm
  intro h0
  exact hdet (by rw [hmap, h0, Int.cast_zero])

end LSG.Aux
