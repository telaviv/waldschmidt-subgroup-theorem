/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Elliptic.AdditionLawsGroup

/-!
# A projective model of the universal vector extension `E^♮`

`E : V²W = 4U³ − g₂UW² − g₃W³` (cone form `F`, `LSG.Elliptic.AdditionLaws`). The universal vector
extension `E^♮` (points `(P, t)`, `t = w − ζ(z)` analytically) is embedded in `ℙ⁴` with coordinates
`(U, V, W, T₁, T₃)`, all sections of `π^* O_E(3·O)`:
* over an affine point `P = (x, y)`: `(x : y : 1 : t : y t − 2x²)` (`ptAff`);
* over `O`: `(0 : 1 : 0 : 0 : w')` (`ptO`), `w' = lim (t − 2x²/y)` the regular fibre coordinate
  at `O` (`T₃/V`; analytically `w' = w − ζ(λ)` at `z = λ ∈ Λ`).

The image lies in `X = V(F, G)`, `G = W T₃ − V T₁ + 2U²` (`Gfib`), a complete intersection of
bidegree `(3, 2)`; `X ∖ E^♮` is the line `U = V = W = 0` (in the closure:
`(x : y : 1 : t : yt − 2x²) → (0 : 0 : 0 : 1 : y)` as `t → ∞`).

Main results:
* `Fn_ptAff`, `Gn_ptAff`, `Fn_ptO`, `Gn_ptO`: the points lie on `X`;
* **`eq_ptAff_or_ptO`**: every point of `X` with `(U, V, W) ≠ 0` is a multiple of exactly one of
  the two shapes, so `X ∖ {U = V = W = 0}` is `E^♮` (`ptAff_injective`, `ptO_injective`);
* `ptAff_add_fib`, `ptO_add_fib`: translation by `v` in the fibre is the linear map
  `T₁ ↦ T₁ + vW`, `T₃ ↦ T₃ + vV`;
* `slice_rel`: on the slice `V + αW = 1`, `T₁ = W t′ + 2U²` with `t′ = T₃ + αT₁` (modulo `G`);
* `G_law_shape`: the identity behind law preservation (`G` of a law-shaped vector).
-/

namespace LSG.Elliptic

variable {R : Type*} [CommRing R]

/-- The fibre relation `G = W T₃ − V T₁ + 2U²`. -/
def Gfib (U V W T₁ T₃ : R) : R :=
  W * T₃ - V * T₁ + 2 * U ^ 2

/-- The base (`E`) part `(U, V, W)` of a vector `(U, V, W, T₁, T₃)`. -/
def Pe (P : Fin 5 → R) : Fin 3 → R :=
  ![P 0, P 1, P 2]

/-- `F` on a vector of the model. -/
def Fn (g₂ g₃ : R) (P : Fin 5 → R) : R :=
  F g₂ g₃ (P 0) (P 1) (P 2)

/-- `G` on a vector of the model. -/
def Gn (P : Fin 5 → R) : R :=
  Gfib (P 0) (P 1) (P 2) (P 3) (P 4)

/-- The ideal `(F(P), G(P), F(Q), G(Q))` (law preservation is membership in it). -/
def Inat (g₂ g₃ : R) (P Q : Fin 5 → R) : Ideal R :=
  Ideal.span {Fn g₂ g₃ P, Gn P, Fn g₂ g₃ Q, Gn Q}

/-- The point `(P, t)` over an affine point `P = (x, y)`. -/
def ptAff (x y t : R) : Fin 5 → R :=
  ![x, y, 1, t, y * t - 2 * x ^ 2]

/-- The point `(O, w')` over the origin. -/
def ptO (w : R) : Fin 5 → R :=
  ![0, 1, 0, 0, w]

omit [CommRing R] in
@[simp] lemma Pe_apply (P : Fin 5 → R) (i : Fin 3) : Pe P i = P i.castSucc.castSucc := by
  fin_cases i <;> rfl

lemma Fn_eq_Fv (g₂ g₃ : R) (P : Fin 5 → R) : Fn g₂ g₃ P = Fv g₂ g₃ (Pe P) := rfl

theorem Fn_ptAff {g₂ g₃ x y : R} (t : R) (h : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃) :
    Fn g₂ g₃ (ptAff x y t) = 0 := by
  simp only [Fn, F, ptAff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination h

theorem Gn_ptAff (x y t : R) : Gn (ptAff x y t) = 0 := by
  simp only [Gn, Gfib, ptAff]
  simp

theorem Fn_ptO (g₂ g₃ w : R) : Fn g₂ g₃ (ptO w) = 0 := by
  simp [Fn, F, ptO]

theorem Gn_ptO (w : R) : Gn (ptO w) = 0 := by
  simp [Gn, Gfib, ptO]

lemma Pe_ptAff_ne_zero (x y t : R) [Nontrivial R] : Pe (ptAff x y t) ≠ 0 := by
  intro h
  have := congrFun h 2
  simp [Pe, ptAff] at this

lemma Pe_ptO_ne_zero (w : R) [Nontrivial R] : Pe (ptO w) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [Pe, ptO] at this

/-! ### Points of `X ∖ {U = V = W = 0}` are the points of `E^♮` -/

section Field

variable {K : Type*} [Field K]

set_option linter.flexible false in
/-- **Points of the model.** A vector on `X = V(F, G)` with `(U, V, W) ≠ 0` is a nonzero multiple
of `ptAff x y t` (if `W ≠ 0`) or of `ptO w` (if `W = 0`). -/
theorem eq_ptAff_or_ptO (h2 : (2 : K) ≠ 0) {g₂ g₃ : K} {P : Fin 5 → K}
    (hF : Fn g₂ g₃ P = 0) (hG : Gn P = 0) (hP : Pe P ≠ 0) :
    (P 2 ≠ 0 ∧ P = P 2 • ptAff (P 0 / P 2) (P 1 / P 2) (P 3 / P 2) ∧
        (P 1 / P 2) ^ 2 = 4 * (P 0 / P 2) ^ 3 - g₂ * (P 0 / P 2) - g₃) ∨
      (P 2 = 0 ∧ P 1 ≠ 0 ∧ P = P 1 • ptO (P 4 / P 1)) := by
  simp only [Fn, F, Gn, Gfib] at hF hG
  by_cases hW : P 2 = 0
  · right
    have hU : P 0 = 0 := by
      have h4 : (4 : K) ≠ 0 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      rw [hW] at hF
      have : 4 * P 0 ^ 3 = 0 := by linear_combination -hF
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left h4)
    have hV : P 1 ≠ 0 := by
      intro hV
      apply hP
      funext i
      fin_cases i <;> simp [Pe, hU, hV, hW]
    have hT : P 3 = 0 := by
      rw [hW, hU] at hG
      have : P 1 * P 3 = 0 := by linear_combination -hG
      exact (mul_eq_zero.mp this).resolve_left hV
    refine ⟨hW, hV, ?_⟩
    funext i
    fin_cases i <;> simp [ptO, hU, hW, hT, mul_div_cancel₀ _ hV]
  · left
    refine ⟨hW, ?_, ?_⟩
    · funext i
      fin_cases i <;> simp [ptAff]
      all_goals (try field_simp)
      all_goals linear_combination hG
    · field_simp
      linear_combination hF

theorem ptAff_injective {x y t x' y' t' : K} (h : ptAff x y t = ptAff x' y' t') :
    x = x' ∧ y = y' ∧ t = t' := by
  have h0 : x = x' := by simpa [ptAff] using congrFun h 0
  have h1 : y = y' := by simpa [ptAff] using congrFun h 1
  have h3 : t = t' := by simpa [ptAff] using congrFun h 3
  exact ⟨h0, h1, h3⟩

theorem ptO_injective {w w' : K} (h : ptO w = ptO w') : w = w' := by
  have := congrFun h 4
  simpa [ptO] using this

/-- Points over affine points and over `O` are never proportional. -/
theorem ptAff_ne_smul_ptO (x y t w c : K) : ptAff x y t ≠ c • ptO w := by
  intro h
  have := congrFun h 2
  simp [ptAff, ptO] at this

end Field

/-! ### Fibre translations and slices -/

/-- Translation by `v` in the fibre: `T₁ ↦ T₁ + vW`, `T₃ ↦ T₃ + vV`. -/
theorem ptAff_add_fib (x y t v : R) :
    ptAff x y (t + v) = ptAff x y t + v • ![0, 0, 0, 1, y] := by
  funext i
  fin_cases i <;> simp [ptAff]
  all_goals ring

theorem ptO_add_fib (w v : R) : ptO (w + v) = ptO w + v • ![0, 0, 0, 0, 1] := by
  funext i
  fin_cases i <;> simp [ptO]

/-- On the slice `ℓ = V + αW = 1`: `W t′ + 2U² = ℓ T₁ + G` with `t′ = T₃ + αT₁`, so modulo `G` and
`ℓ − 1` the coordinate ring of the slice is `(sliced E ring)[t′]`. -/
theorem slice_rel (α U V W T₁ T₃ : R) :
    W * (T₃ + α * T₁) + 2 * U ^ 2 = (V + α * W) * T₁ + Gfib U V W T₁ T₃ := by
  unfold Gfib
  ring

/-- `G` of a law-shaped vector: with `M = λμ`,
`G(2M lU, 2M lV, 2M lW, 2μ lW Tλ + 2λ lW Tμ − κᵂ, 2μ lV Tλ + 2λ lV Tμ − κⱽ)
  = 2M (lV κᵂ − lW κⱽ + 4M lU²)`: the `T`-terms cancel identically. -/
theorem G_law_shape (lU lV lW kW kV lam mu Tl Tm : R) :
    Gfib (2 * (lam * mu) * lU) (2 * (lam * mu) * lV) (2 * (lam * mu) * lW)
      (2 * mu * lW * Tl + 2 * lam * lW * Tm - kW) (2 * mu * lV * Tl + 2 * lam * lV * Tm - kV) =
      2 * (lam * mu) * (lV * kW - lW * kV + 4 * (lam * mu) * lU ^ 2) := by
  unfold Gfib
  ring

/-- `F` is a cubic form. -/
theorem F_smul (g₂ g₃ c U V W : R) :
    F g₂ g₃ (c * U) (c * V) (c * W) = c ^ 3 * F g₂ g₃ U V W := by
  unfold F
  ring

end LSG.Elliptic
