/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Elliptic.NaturalLawsPoly

/-!
# Eight addition laws of bidegree `(3, 3)` on `E^♮`; law preservation

Model `X = V(F, G) ⊂ ℙ⁴` (`NaturalModel`), vectors `P = (U, V, W, T₁, T₃) : Fin 5 → R`.
For `i ∈ Fin 2` (the `E`-law `law₁` or `law₂`) and `j, k ∈ Fin 2` (multipliers `λ, μ`, with
`0 ↦ V`, `1 ↦ W`), `NLaw g₂ g₃ i j k P Q` is
```
( 2M·lU, 2M·lV, 2M·lW,
  2μ(Q)·lW·T_λ(P) + 2λ(P)·lW·T_μ(Q) − κᵂ,
  2μ(Q)·lV·T_λ(P) + 2λ(P)·lV·T_μ(Q) − κⱽ ),        M = λ(P) μ(Q),  (lU, lV, lW) = lawᵢ(P, Q),
```
`T_V = T₃`, `T_W = T₁`, `κ = kapW/kapV` (`NaturalLawsPoly`). Each component is bihomogeneous of
bidegree `(3, 3)` (`NLaw_smul`) and affine-linear in the fibre coordinates `T`.

Main results (over any commutative ring):
* **`NLaw_mem` (a)**: `F(NLaw P Q)` and `G(NLaw P Q)` lie in `(F(P), G(P), F(Q), G(Q))`;
  in fact `F(NLaw) = (2M)³ F(lawᵢ)` and `G(NLaw) = 2M Φ` with `Φ ∈ (F(P), F(Q))`;
* `NLaw_smul`: `NLaw (u • P) (v • Q) = (u v)³ • NLaw P Q`;
* `NLaw_zero_of_base`: `NLaw` vanishes when the base part of `P` vanishes;
* `NLaw_fib_left`, `NLaw_fib_right`: equivariance under fibre translations (the laws commute with
  the `G_a`-action on the fibres; used for `ker M`-invariant polynomials).
The comparison with the group law (b) and completeness (c) are in `NaturalGroup`.
-/

namespace LSG.Elliptic

variable {R : Type*} [CommRing R]

/-- The `E`-law selector: `0 ↦ law₁`, `1 ↦ law₂`. -/
def lawSel (g₂ g₃ : R) (i : Fin 2) (P Q : Fin 3 → R) : Fin 3 → R :=
  ![law₁ g₂ g₃ P Q, law₂ g₂ g₃ P Q] i

/-- The multiplier `λ`: `0 ↦ V`, `1 ↦ W`. -/
def mult (j : Fin 2) (P : Fin 3 → R) : R :=
  ![P 1, P 2] j

/-- The fibre coordinate attached to the multiplier: `V ↦ T₃`, `W ↦ T₁` (`λ t = T_λ + ρ_λ`). -/
def tcoord (j : Fin 2) (P : Fin 5 → R) : R :=
  ![P 4, P 3] j

/-- `κᵂ` selector. -/
def kapW (g₂ g₃ : R) (i j k : Fin 2) (P Q : Fin 3 → R) : R :=
  ![![![kapW₁VV g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
        kapW₁VW g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)],
      ![kapW₁WV g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
        kapW₁WW g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)]],
    ![![kapW₂VV g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
        kapW₂VW g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)],
      ![kapW₂WV g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
        kapW₂WW g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)]]] i j k

/-- `κⱽ` selector. -/
def kapV (g₂ g₃ : R) (i j k : Fin 2) (P Q : Fin 3 → R) : R :=
  ![![![kapV₁VV g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
        kapV₁VW g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)],
      ![kapV₁WV g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
        kapV₁WW g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)]],
    ![![kapV₂VV g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
        kapV₂VW g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)],
      ![kapV₂WV g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
        kapV₂WW g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)]]] i j k

/-- **The addition law `(i, λ, μ)` on `E^♮`**, bidegree `(3, 3)`. -/
def NLaw (g₂ g₃ : R) (i j k : Fin 2) (P Q : Fin 5 → R) : Fin 5 → R :=
  let l := lawSel g₂ g₃ i (Pe P) (Pe Q)
  let lam := mult j (Pe P)
  let mu := mult k (Pe Q)
  ![2 * (lam * mu) * l 0, 2 * (lam * mu) * l 1, 2 * (lam * mu) * l 2,
    2 * mu * l 2 * tcoord j P + 2 * lam * l 2 * tcoord k Q - kapW g₂ g₃ i j k (Pe P) (Pe Q),
    2 * mu * l 1 * tcoord j P + 2 * lam * l 1 * tcoord k Q - kapV g₂ g₃ i j k (Pe P) (Pe Q)]

variable (g₂ g₃ : R)

/-- The identity `Φ = lV κᵂ − lW κⱽ + 4M lU² ∈ (F(P), F(Q))`, for all eight laws. -/
theorem phi_eq (i j k : Fin 2) (P Q : Fin 3 → R) : ∃ q₁ q₂ : R,
    lawSel g₂ g₃ i P Q 1 * kapW g₂ g₃ i j k P Q - lawSel g₂ g₃ i P Q 2 * kapV g₂ g₃ i j k P Q +
      4 * (mult j P * mult k Q) * lawSel g₂ g₃ i P Q 0 ^ 2 = q₁ * Fv g₂ g₃ P + q₂ * Fv g₂ g₃ Q := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
  simp only [lawSel, kapW, kapV, mult, law₁, law₂, Fv, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · exact ⟨_, _, phi₁VV ..⟩
  · exact ⟨_, _, phi₁VW ..⟩
  · exact ⟨_, _, phi₁WV ..⟩
  · exact ⟨_, _, phi₁WW ..⟩
  · exact ⟨_, _, phi₂VV ..⟩
  · exact ⟨_, _, phi₂VW ..⟩
  · exact ⟨_, _, phi₂WV ..⟩
  · exact ⟨_, _, phi₂WW ..⟩

variable (i j k : Fin 2) (P Q : Fin 5 → R)

/-- `F(NLaw) = (2M)³ F(lawᵢ)`. -/
theorem Fn_NLaw : Fn g₂ g₃ (NLaw g₂ g₃ i j k P Q) =
    (2 * (mult j (Pe P) * mult k (Pe Q))) ^ 3 * Fv g₂ g₃ (lawSel g₂ g₃ i (Pe P) (Pe Q)) := by
  simp only [Fn, NLaw, Fv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  exact F_smul ..

/-- `G(NLaw) = 2M Φ`: the fibre coordinates cancel. -/
theorem Gn_NLaw : Gn (NLaw g₂ g₃ i j k P Q) =
    2 * (mult j (Pe P) * mult k (Pe Q)) *
      (lawSel g₂ g₃ i (Pe P) (Pe Q) 1 * kapW g₂ g₃ i j k (Pe P) (Pe Q) -
        lawSel g₂ g₃ i (Pe P) (Pe Q) 2 * kapV g₂ g₃ i j k (Pe P) (Pe Q) +
        4 * (mult j (Pe P) * mult k (Pe Q)) * lawSel g₂ g₃ i (Pe P) (Pe Q) 0 ^ 2) := by
  simp only [Gn, NLaw]
  exact G_law_shape ..

lemma Fv_lawSel_mem (P Q : Fin 3 → R) :
    Fv g₂ g₃ (lawSel g₂ g₃ i P Q) ∈ Ideal.span {Fv g₂ g₃ P, Fv g₂ g₃ Q} := by
  fin_cases i
  · exact Fv_law₁_mem g₂ g₃ P Q
  · exact Fv_law₂_mem g₂ g₃ P Q

lemma span_FF_le_Inat :
    Ideal.span {Fv g₂ g₃ (Pe P), Fv g₂ g₃ (Pe Q)} ≤ Inat g₂ g₃ P Q := by
  apply Ideal.span_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))

/-- **Law preservation (a).** `F(NLaw P Q), G(NLaw P Q) ∈ (F(P), G(P), F(Q), G(Q))`. -/
theorem NLaw_mem : Fn g₂ g₃ (NLaw g₂ g₃ i j k P Q) ∈ Inat g₂ g₃ P Q ∧
    Gn (NLaw g₂ g₃ i j k P Q) ∈ Inat g₂ g₃ P Q := by
  refine ⟨?_, ?_⟩
  · rw [Fn_NLaw]
    exact Ideal.mul_mem_left _ _ (span_FF_le_Inat g₂ g₃ P Q (Fv_lawSel_mem g₂ g₃ i _ _))
  · rw [Gn_NLaw]
    obtain ⟨q₁, q₂, h⟩ := phi_eq g₂ g₃ i j k (Pe P) (Pe Q)
    rw [h]
    refine Ideal.mul_mem_left _ _ (span_FF_le_Inat g₂ g₃ P Q ?_)
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-! ### Bihomogeneity -/

lemma Pe_smul (u : R) (P : Fin 5 → R) : Pe (u • P) = u • Pe P := by
  funext c
  fin_cases c <;> rfl

lemma mult_smul (u : R) (P : Fin 3 → R) : mult j (u • P) = u * mult j P := by
  fin_cases j <;> rfl

lemma tcoord_smul (u : R) : tcoord j (u • P) = u * tcoord j P := by
  fin_cases j <;> rfl

lemma lawSel_smul (u v : R) (P Q : Fin 3 → R) :
    lawSel g₂ g₃ i (u • P) (v • Q) = (u * v) ^ 2 • lawSel g₂ g₃ i P Q := by
  fin_cases i
  · exact law₁_smul ..
  · exact law₂_smul ..

lemma kapW_smul (u v : R) (P Q : Fin 3 → R) :
    kapW g₂ g₃ i j k (u • P) (v • Q) = (u * v) ^ 3 * kapW g₂ g₃ i j k P Q := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
  · simp only [kapW, kapW₁VV, kapW₁VW, kapW₁WV, kapW₁WW, kapW₂VV, kapW₂VW, kapW₂WV, kapW₂WW,
      Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring

lemma kapV_smul (u v : R) (P Q : Fin 3 → R) :
    kapV g₂ g₃ i j k (u • P) (v • Q) = (u * v) ^ 3 * kapV g₂ g₃ i j k P Q := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
  · simp only [kapV, kapV₁VV, kapV₁VW, kapV₁WV, kapV₁WW, kapV₂VV, kapV₂VW, kapV₂WV, kapV₂WW,
      Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring

/-- `NLaw` is bihomogeneous of bidegree `(3, 3)`. -/
theorem NLaw_smul (u v : R) :
    NLaw g₂ g₃ i j k (u • P) (v • Q) = (u * v) ^ 3 • NLaw g₂ g₃ i j k P Q := by
  have hl := lawSel_smul g₂ g₃ i u v (Pe P) (Pe Q)
  simp only [NLaw, Pe_smul, mult_smul, tcoord_smul, kapW_smul, kapV_smul, hl]
  funext c
  fin_cases c <;>
  · simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
      Matrix.cons_val]
    ring

/-- `NLaw P Q = 0` when the base part of `P` vanishes (the boundary line `U = V = W = 0`). -/
theorem NLaw_zero_of_base (h : Pe P = 0) : NLaw g₂ g₃ i j k P Q = 0 := by
  have hX : Pe P = (0 : R) • Pe P := by rw [h, smul_zero]
  have hY : Pe Q = (1 : R) • Pe Q := (one_smul _ _).symm
  have hl : lawSel g₂ g₃ i (Pe P) (Pe Q) = 0 := by
    rw [hX, hY, lawSel_smul]; simp
  have hkW : kapW g₂ g₃ i j k (Pe P) (Pe Q) = 0 := by
    rw [hX, hY, kapW_smul]; simp
  have hkV : kapV g₂ g₃ i j k (Pe P) (Pe Q) = 0 := by
    rw [hX, hY, kapV_smul]; simp
  have hm : mult j (Pe P) = 0 := by rw [h]; fin_cases j <;> rfl
  simp only [NLaw, hl, hkW, hkV, hm]
  funext c
  fin_cases c <;> simp

/-! ### Equivariance under fibre translations -/

/-- The fibre direction at `P`: translation by `v` in the fibre is `P ↦ P + v • fibv P`
(`T₁ ↦ T₁ + vW`, `T₃ ↦ T₃ + vV`; `ptAff_add_fib`, `ptO_add_fib`). -/
def fibv (P : Fin 5 → R) : Fin 5 → R :=
  ![0, 0, 0, P 2, P 1]

lemma Pe_add_fibv (v : R) : Pe (P + v • fibv P) = Pe P := by
  funext c
  fin_cases c <;> simp [Pe, fibv]

lemma tcoord_add_fibv (v : R) :
    tcoord j (P + v • fibv P) = tcoord j P + v * mult j (Pe P) := by
  fin_cases j <;> simp [tcoord, fibv, mult, Pe]

/-- **Fibre equivariance** (left): translating `P` by `v` in the fibre translates the output
by `v`. -/
theorem NLaw_fib_left (v : R) :
    NLaw g₂ g₃ i j k (P + v • fibv P) Q =
      NLaw g₂ g₃ i j k P Q + v • fibv (NLaw g₂ g₃ i j k P Q) := by
  simp only [NLaw, Pe_add_fibv, tcoord_add_fibv]
  funext c
  fin_cases c <;> simp [fibv] <;> ring

/-- **Fibre equivariance** (right). -/
theorem NLaw_fib_right (v : R) :
    NLaw g₂ g₃ i j k P (Q + v • fibv Q) =
      NLaw g₂ g₃ i j k P Q + v • fibv (NLaw g₂ g₃ i j k P Q) := by
  simp only [NLaw, Pe_add_fibv, tcoord_add_fibv]
  funext c
  fin_cases c <;> simp [fibv] <;> ring

end LSG.Elliptic
