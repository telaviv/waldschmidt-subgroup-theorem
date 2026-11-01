import LSG.Elliptic.AdditionLaws
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# A complete system of two addition laws: comparison with Mathlib's group law

Let `K` be a field with `2 ≠ 0`, and `g₂, g₃ ∈ K` with `g₂³ − 27 g₃² ≠ 0`. The curve
`E : V²W = 4U³ − g₂UW² − g₃W³` is identified with Mathlib's Weierstrass curve
`curve g₂ g₃ : y² = x³ − (g₂/4) x − g₃/4` via `(U : V : W) ↦ (U : V/2 : W)` (i.e. affine
`(x, y) ↦ (x, y/2)`). `toPoint g₂ g₃ P` is the Mathlib point (`(curve g₂ g₃).toAffine.Point`)
represented by a cone vector `P`; it is defined through Mathlib's
`WeierstrassCurve.Projective.toAffine`.

Main results (for `P, Q` nonzero vectors with `F(P) = F(Q) = 0`):
* `toPoint_law₁`, `toPoint_law₂` (**(b)**): if `lawᵢ(P, Q) ≠ 0` then it represents
  `toPoint P + toPoint Q`;
* `law_complete` (**(c)**): `law₁(P, Q) ≠ 0 ∨ law₂(P, Q) ≠ 0`; more precisely
  `law₁(P, Q) = 0 ↔ P ∼ Q` (`law₁_eq_zero_iff`) and `law₂(P, P) ≠ 0` (`law₂_self_ne_zero`);
  `exists_law` packages (b) and (c);
* `toPoint_negv`: `(U : −V : W)` represents `−toPoint P`;
* `toPoint_law₁_O_right`, `toPoint_law₂_O_right`: `lawᵢ(P, O)` represents `P` when nonzero;
* `toPoint_eq_iff`: two nonzero cone vectors on `E` represent the same point iff proportional;
  `rep` is a section (`(x : 2y : 1)` and `(0 : 1 : 0)`) of `toPoint`.

`law₁` is Mathlib's `Projective.addXYZ` transported (`toW_law₁`), and `dbl` is Mathlib's
`Projective.dblXYZ` transported (`toW_dbl`), so (b) and (c) reduce to Mathlib's
`Projective.Point.toAffine_add` and `Projective.nonsingular_add`.
-/

namespace LSG.Elliptic

open WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K]

/-- Mathlib's model of `E`: `y² = x³ − (g₂/4) x − g₃/4`. -/
def curve (g₂ g₃ : K) : WeierstrassCurve K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -g₂ / 4, a₆ := -g₃ / 4 }

/-- `curve` as a projective Weierstrass curve. -/
abbrev curveP (g₂ g₃ : K) : WeierstrassCurve.Projective K :=
  (curve g₂ g₃).toProjective

variable {g₂ g₃ : K}

private theorem four_ne_zero' (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this]; exact mul_ne_zero h2 h2

theorem curve_Δ (h2 : (2 : K) ≠ 0) : (curve g₂ g₃).Δ = g₂ ^ 3 - 27 * g₃ ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve]
  have h4 := four_ne_zero' h2
  field_simp
  ring

/-- Our coordinates to Mathlib's: `(U, V, W) ↦ (U, V/2, W)`. -/
def toW (P : Fin 3 → K) : Fin 3 → K :=
  ![P 0, P 1 / 2, P 2]

/-- Mathlib's coordinates to ours: `(X, Y, Z) ↦ (X, 2Y, Z)`. -/
def ofW (P : Fin 3 → K) : Fin 3 → K :=
  ![P 0, 2 * P 1, P 2]

section Coordinates

variable (P Q : Fin 3 → K)

theorem toW_ofW (h2 : (2 : K) ≠ 0) : toW (ofW P) = P := by
  funext i
  fin_cases i <;> simp [toW, ofW, h2]

theorem ofW_toW (h2 : (2 : K) ≠ 0) : ofW (toW P) = P := by
  funext i
  fin_cases i <;> simp [toW, ofW]
  field_simp

theorem toW_smul (u : K) : toW (u • P) = u • toW P := by
  funext i
  fin_cases i <;> simp [toW, mul_div_assoc]

theorem toW_zero : toW (0 : Fin 3 → K) = 0 := by
  funext i
  fin_cases i <;> simp [toW]

theorem toW_ne_zero (h2 : (2 : K) ≠ 0) {P : Fin 3 → K} (hP : P ≠ 0) : toW P ≠ 0 := by
  intro h
  apply hP
  rw [← ofW_toW P h2, h]
  funext i
  fin_cases i <;> simp [ofW]

theorem toW_injective (h2 : (2 : K) ≠ 0) : Function.Injective (toW : (Fin 3 → K) → _) :=
  fun P Q h => by rw [← ofW_toW P h2, h, ofW_toW Q h2]

/-- Mathlib's equation for `toW P` is our `F(P) = 0`. -/
theorem equation_toW (h2 : (2 : K) ≠ 0) : (curveP g₂ g₃).Equation (toW P) ↔ Fv g₂ g₃ P = 0 := by
  have h4 := four_ne_zero' h2
  rw [equation_iff]
  simp only [toW, curve, Fv, F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, zero_mul, add_zero]
  constructor
  · intro h
    field_simp at h
    apply mul_left_cancel₀ h4
    linear_combination h
  · intro h
    field_simp
    linear_combination 4 * h

end Coordinates

/-- A nonzero cone vector on `E` gives a nonsingular point (here `Δ ≠ 0` is used). -/
theorem nonsingular_toW (h2 : (2 : K) ≠ 0) (hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) {P : Fin 3 → K}
    (hP : Fv g₂ g₃ P = 0) (hP0 : P ≠ 0) : (curveP g₂ g₃).Nonsingular (toW P) := by
  have heq := (equation_toW P h2).mpr hP
  by_cases hz : P 2 = 0
  · have hU : P 0 = 0 := by
      have h4 : (4 : K) ≠ 0 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      simp only [Fv, F, hz] at hP
      have : P 0 ^ 3 = 0 := by
        have := mul_eq_zero.mp (show (4 : K) * P 0 ^ 3 = 0 by linear_combination -hP)
        exact this.resolve_left h4
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this
    have hV : P 1 ≠ 0 := by
      intro hV
      apply hP0
      funext i
      fin_cases i <;> simp [hU, hV, hz]
    have : toW P = (P 1 / 2) • ![0, 1, 0] := by
      funext i
      fin_cases i <;> simp [toW, hU, hz]
    rw [this, nonsingular_smul _ (div_ne_zero hV h2).isUnit]
    exact nonsingular_zero
  · have hz' : toW P 2 ≠ 0 := by simpa [toW] using hz
    rw [nonsingular_of_Z_ne_zero hz']
    rw [equation_of_Z_ne_zero hz'] at heq
    refine (Affine.equation_iff_nonsingular_of_Δ_ne_zero ?_).mp heq
    change (curve g₂ g₃).Δ ≠ 0
    rwa [curve_Δ h2]

theorem ne_zero_of_nonsingular {W : WeierstrassCurve.Projective K} {P : Fin 3 → K}
    (h : W.Nonsingular P) : P ≠ 0 := by
  rintro rfl
  simp [nonsingular_iff] at h

/-- The point of `curve g₂ g₃` represented by a cone vector `P` (it is `0` unless `P` is a
nonsingular point of `E`). -/
noncomputable def toPoint (g₂ g₃ : K) (P : Fin 3 → K) : (curve g₂ g₃).toAffine.Point :=
  Point.toAffine (curveP g₂ g₃) (toW P)

theorem toPoint_smul (P : Fin 3 → K) {u : K} (hu : u ≠ 0) :
    toPoint g₂ g₃ (u • P) = toPoint g₂ g₃ P := by
  rw [toPoint, toW_smul, Point.toAffine_smul _ hu.isUnit, toPoint]

theorem toPoint_O : toPoint g₂ g₃ (O : Fin 3 → K) = 0 :=
  Point.toAffine_of_Z_eq_zero (by simp [toW, O])

theorem toPoint_some (x y : K) (h : (curve g₂ g₃).toAffine.Nonsingular x (y / 2)) :
    toPoint g₂ g₃ ![x, y, 1] = .some x (y / 2) h := by
  have : toW ![x, y, 1] = ![x, y / 2, 1] := by
    funext i
    fin_cases i <;> simp [toW]
  rw [toPoint, this, Point.toAffine_some ((nonsingular_some _ _).mpr h)]

/-- A cone representative of a point of `curve g₂ g₃`: `(x : 2y : 1)`, resp. `(0 : 1 : 0)`. -/
def rep : (curve g₂ g₃).toAffine.Point → Fin 3 → K
  | 0 => O
  | .some x y _ => ![x, 2 * y, 1]

theorem rep_ne_zero (p : (curve g₂ g₃).toAffine.Point) : rep p ≠ 0 := by
  intro h
  cases p with
  | zero => simpa [rep, O] using congrFun h 1
  | some => simpa [rep] using congrFun h 2

theorem Fv_rep (h2 : (2 : K) ≠ 0) (p : (curve g₂ g₃).toAffine.Point) : Fv g₂ g₃ (rep p) = 0 := by
  cases p with
  | zero => exact Fv_O g₂ g₃
  | some x y h =>
    have he := h.1
    rw [Affine.equation_iff] at he
    simp only [curve, zero_mul, add_zero] at he
    simp only [rep, Fv, F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have h4 := four_ne_zero' h2
    field_simp at he
    linear_combination he

theorem toPoint_rep (h2 : (2 : K) ≠ 0) (p : (curve g₂ g₃).toAffine.Point) :
    toPoint g₂ g₃ (rep p) = p := by
  cases p with
  | zero => exact toPoint_O
  | some x y h =>
    have h' : (curve g₂ g₃).toAffine.Nonsingular x (2 * y / 2) := by
      rwa [mul_div_cancel_left₀ _ h2]
    rw [rep, toPoint_some x (2 * y) h']
    simp [mul_div_cancel_left₀ _ h2]

/-! ### Transport of Mathlib's formulas -/

/-- `law₁` is Mathlib's chord law `addXYZ`, transported, times `4`. -/
theorem toW_law₁ (h2 : (2 : K) ≠ 0) (P Q : Fin 3 → K) :
    toW (law₁ g₂ g₃ P Q) = (4 : K) • (curveP g₂ g₃).addXYZ (toW P) (toW Q) := by
  funext i
  fin_cases i <;>
  · simp only [toW, law₁, law₁U, law₁V, law₁W, addXYZ, addX, addY, addZ, negAddY, negY, curve,
      Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    have h4 := four_ne_zero' h2
    field_simp
    ring

/-- `dbl` is Mathlib's doubling law `dblXYZ`, transported, times `32`. -/
theorem toW_dbl (h2 : (2 : K) ≠ 0) (P : Fin 3 → K) :
    toW (dbl g₂ g₃ P) = (32 : K) • (curveP g₂ g₃).dblXYZ (toW P) := by
  funext i
  fin_cases i <;>
  · simp only [toW, dbl, dblU, dblV, dblW, dblXYZ, Projective.dblX, Projective.dblY,
      Projective.dblZ, negDblY, negY, curve, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have h4 := four_ne_zero' h2
    field_simp
    ring

/-! ### (b) and (c) -/

section Main

variable [DecidableEq K] (h2 : (2 : K) ≠ 0) (hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) {P Q : Fin 3 → K}
  (hP : Fv g₂ g₃ P = 0) (hQ : Fv g₂ g₃ Q = 0) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)

omit [DecidableEq K] in
include h2 in
private theorem eq_smul_of_equiv (h : toW P ≈ toW Q) : ∃ u : K, u ≠ 0 ∧ P = u • Q := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u, u.ne_zero, toW_injective h2 ?_⟩
  rw [toW_smul]
  exact hu.symm

omit [DecidableEq K] in
private theorem thirtytwo_ne_zero (h2 : (2 : K) ≠ 0) : (32 : K) ≠ 0 := by
  have : (32 : K) = 2 ^ 5 := by norm_num
  rw [this]; exact pow_ne_zero 5 h2

omit [DecidableEq K] in
include h2 hΔ hP hP0 hQ hQ0 in
/-- `law₁(P, Q) = 0` exactly on the diagonal. -/
theorem law₁_eq_zero_iff : law₁ g₂ g₃ P Q = 0 ↔ ∃ u : K, u ≠ 0 ∧ P = u • Q := by
  constructor
  · intro h
    by_contra hne
    have hne' : ¬ toW P ≈ toW Q := fun h' => hne (eq_smul_of_equiv h2 h')
    have hns := nonsingular_add (nonsingular_toW h2 hΔ hP hP0) (nonsingular_toW h2 hΔ hQ hQ0)
    rw [add_of_not_equiv hne'] at hns
    apply ne_zero_of_nonsingular hns
    have := toW_law₁ (g₂ := g₂) (g₃ := g₃) h2 P Q
    rw [h, toW_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left (four_ne_zero' h2)
  · rintro ⟨u, -, rfl⟩
    have := law₁_smul g₂ g₃ Q Q u 1
    rw [one_smul, law₁_self, smul_zero] at this
    exact this

omit [DecidableEq K] in
include h2 hΔ hQ hQ0 in
/-- `law₂` does not vanish on the diagonal. -/
theorem law₂_self_ne_zero : law₂ g₂ g₃ Q Q ≠ 0 := by
  rw [law₂_self hQ]
  intro h
  have hns := nonsingular_add (nonsingular_toW h2 hΔ hQ hQ0) (nonsingular_toW h2 hΔ hQ hQ0)
  rw [add_self] at hns
  apply ne_zero_of_nonsingular hns
  have := toW_dbl (g₂ := g₂) (g₃ := g₃) h2 Q
  rw [h, toW_zero] at this
  exact (smul_eq_zero.mp this.symm).resolve_left (thirtytwo_ne_zero h2)

omit [DecidableEq K] in
include h2 hΔ hP hP0 hQ hQ0 in
/-- **(c) Completeness**: one of the two laws is nonzero at every pair of points of `E`. -/
theorem law_complete : law₁ g₂ g₃ P Q ≠ 0 ∨ law₂ g₂ g₃ P Q ≠ 0 := by
  by_cases h : ∃ u : K, u ≠ 0 ∧ P = u • Q
  · right
    obtain ⟨u, hu, rfl⟩ := h
    have := law₂_smul g₂ g₃ Q Q u 1
    rw [one_smul] at this
    rw [this, smul_ne_zero_iff]
    exact ⟨by simpa using hu, law₂_self_ne_zero h2 hΔ hQ hQ0⟩
  · left
    exact fun h0 => h ((law₁_eq_zero_iff h2 hΔ hP hQ hP0 hQ0).mp h0)

include h2 hΔ hP hP0 hQ hQ0 in
/-- **(b) for `law₁`**: if `law₁(P, Q) ≠ 0`, it represents `P + Q` (Mathlib's group law). -/
theorem toPoint_law₁ (h : law₁ g₂ g₃ P Q ≠ 0) :
    toPoint g₂ g₃ (law₁ g₂ g₃ P Q) = toPoint g₂ g₃ P + toPoint g₂ g₃ Q := by
  have hne' : ¬ toW P ≈ toW Q := fun h' =>
    h ((law₁_eq_zero_iff h2 hΔ hP hQ hP0 hQ0).mpr (eq_smul_of_equiv h2 h'))
  rw [toPoint, toW_law₁ h2, Point.toAffine_smul _ (four_ne_zero' h2).isUnit,
    ← add_of_not_equiv hne',
    Point.toAffine_add (nonsingular_toW h2 hΔ hP hP0) (nonsingular_toW h2 hΔ hQ hQ0)]
  rfl

omit [DecidableEq K] in
/-- Two nonzero vectors with vanishing `2 × 2` minors are proportional. -/
theorem exists_smul_of_cross {A B : Fin 3 → K} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ i j, A i * B j = A j * B i) : ∃ c : K, c ≠ 0 ∧ A = c • B := by
  obtain ⟨j, hj⟩ : ∃ j, B j ≠ 0 := by
    by_contra! h'
    exact hB (funext h')
  have hAB : A = (A j / B j) • B := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h i j
  refine ⟨A j / B j, fun hc => hA ?_, hAB⟩
  rw [hAB, hc, zero_smul]

include h2 hΔ hP hP0 hQ hQ0 in
/-- **(b) for `law₂`**: if `law₂(P, Q) ≠ 0`, it represents `P + Q` (Mathlib's group law). -/
theorem toPoint_law₂ (h : law₂ g₂ g₃ P Q ≠ 0) :
    toPoint g₂ g₃ (law₂ g₂ g₃ P Q) = toPoint g₂ g₃ P + toPoint g₂ g₃ Q := by
  by_cases hd : ∃ u : K, u ≠ 0 ∧ P = u • Q
  · obtain ⟨u, hu, rfl⟩ := hd
    have hl := law₂_smul g₂ g₃ Q Q u 1
    rw [one_smul] at hl
    have hQns := nonsingular_toW h2 hΔ hQ hQ0
    rw [hl, law₂_self hQ, toPoint_smul _ (by simpa using hu), toPoint_smul _ hu, toPoint,
      toW_dbl h2, Point.toAffine_smul _ (thirtytwo_ne_zero h2).isUnit, ← add_self,
      Point.toAffine_add hQns hQns]
    rfl
  · have h1 : law₁ g₂ g₃ P Q ≠ 0 := fun h0 =>
      hd ((law₁_eq_zero_iff h2 hΔ hP hQ hP0 hQ0).mp h0)
    obtain ⟨c, hc, hcA⟩ := exists_smul_of_cross h h1 fun i j => by
      have := law₁_cross_law₂ hP hQ i j
      linear_combination -this
    rw [hcA, toPoint_smul _ hc, toPoint_law₁ h2 hΔ hP hQ hP0 hQ0 h1]

include h2 hΔ hP hP0 hQ hQ0 in
/-- **(b) + (c)**: for all `P, Q` on `E`, some law is nonzero at `(P, Q)` and represents
`P + Q`. -/
theorem exists_law : ∃ i : Fin 2, ![law₁ g₂ g₃ P Q, law₂ g₂ g₃ P Q] i ≠ 0 ∧
    toPoint g₂ g₃ (![law₁ g₂ g₃ P Q, law₂ g₂ g₃ P Q] i) = toPoint g₂ g₃ P + toPoint g₂ g₃ Q := by
  rcases law_complete h2 hΔ hP hQ hP0 hQ0 with h | h
  · exact ⟨0, h, toPoint_law₁ h2 hΔ hP hQ hP0 hQ0 h⟩
  · exact ⟨1, h, toPoint_law₂ h2 hΔ hP hQ hP0 hQ0 h⟩

omit [DecidableEq K] in
include h2 hΔ hP hP0 in
/-- Negation: `(U : −V : W)` represents `−P`. -/
theorem toPoint_negv : toPoint g₂ g₃ (negv P) = -toPoint g₂ g₃ P := by
  have : toW (negv P) = (curveP g₂ g₃).neg (toW P) := by
    funext i
    fin_cases i <;> simp [toW, negv, Projective.neg, negY, curve, neg_div]
  rw [toPoint, this, Point.toAffine_neg (nonsingular_toW h2 hΔ hP hP0), toPoint]

omit [DecidableEq K] in
/-- `law₁(P, O)` represents `P` whenever it is nonzero (`law₁(P, O) = −W(P) · P`). -/
theorem toPoint_law₁_O_right (h : law₁ g₂ g₃ P O ≠ 0) :
    toPoint g₂ g₃ (law₁ g₂ g₃ P O) = toPoint g₂ g₃ P := by
  rw [law₁_O_right] at h ⊢
  exact toPoint_smul _ fun h0 => h (by rw [h0, zero_smul])

omit [DecidableEq K] in
/-- `law₂(P, O)` represents `P` whenever it is nonzero (`law₂(P, O) = 4V(P) · P`). -/
theorem toPoint_law₂_O_right (h : law₂ g₂ g₃ P O ≠ 0) :
    toPoint g₂ g₃ (law₂ g₂ g₃ P O) = toPoint g₂ g₃ P := by
  rw [law₂_O_right] at h ⊢
  exact toPoint_smul _ fun h0 => h (by rw [h0, zero_smul])

omit [DecidableEq K] in
include h2 hΔ hP hP0 hQ hQ0 in
/-- Two nonzero cone vectors on `E` represent the same point iff they are proportional. -/
theorem toPoint_eq_iff :
    toPoint g₂ g₃ P = toPoint g₂ g₃ Q ↔ ∃ u : K, u ≠ 0 ∧ P = u • Q := by
  classical
  constructor
  · intro h
    have hP' := (nonsingularLift_iff _).mpr (nonsingular_toW h2 hΔ hP hP0)
    have hQ' := (nonsingularLift_iff _).mpr (nonsingular_toW h2 hΔ hQ hQ0)
    have := (Point.toAffineAddEquiv (curveP g₂ g₃)).injective
      (a₁ := ⟨hP'⟩) (a₂ := ⟨hQ'⟩) h
    rw [Point.ext_iff] at this
    exact eq_smul_of_equiv h2 (Quotient.exact this)
  · rintro ⟨u, hu, rfl⟩
    exact toPoint_smul _ hu

end Main

end LSG.Elliptic
