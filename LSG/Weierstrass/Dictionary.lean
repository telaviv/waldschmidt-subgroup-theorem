/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.Addition

/-!
# The analytic–algebraic dictionary: `z ↦ (℘(z), ℘'(z)/2)` is a group homomorphism

Let `E` be the Weierstrass curve `y² = x³ - (g₂/4) x - g₃/4` in Mathlib's normalisation
(`a₁ = a₂ = a₃ = 0`, `a₄ = -g₂/4`, `a₆ = -g₃/4`); `(x, y) = (℘, ℘'/2)` turns
`℘'² = 4℘³ - g₂℘ - g₃` into its equation.

* `LSG.Weierstrass.discr_ne_zero`: `g₂³ - 27 g₃² ≠ 0` (the three half-period values are distinct
  roots of `4X³ - g₂X - g₃`, by `weierstrassP_eq_iff`), so every point of `E` is nonsingular.
* `LSG.Weierstrass.expE L : ℂ → E.Point`: `0` on `Λ`, `(℘(z), ℘'(z)/2)` otherwise.
* `expE_add`: `expE (z + w) = expE z + expE w` (Mathlib's group law); `expHom : ℂ →+ E.Point`;
  `expE_add_mem`: `Λ`-periodicity.
* `ratPoints K`: for a subfield `K ∋ g₂` (then also `g₃ ∈ K` on any `K`-point), the points with coordinates in `K` form a subgroup.
* `mem_of_intCast_mul`: if `℘(z), ℘'(z) ∈ K` then `℘(nz), ℘'(nz) ∈ K` (`nz ∉ Λ`), and
  `isAlgebraic_of_intCast_mul`: the same with "algebraic over `F`".
-/

open Module Filter Complex Set WeierstrassCurve WeierstrassCurve.Affine
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

/-- The curve `y² = x³ - (g₂/4) x - g₃/4`. -/
def curve : WeierstrassCurve ℂ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -L.g₂ / 4, a₆ := -L.g₃ / 4 }

/-- The curve in affine coordinates. -/
abbrev curveA : WeierstrassCurve.Affine ℂ := (curve L).toAffine

lemma curve_Δ : (curve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve]
  ring

/-! ### The discriminant -/

lemma half_comb_notMem {a b : ℤ} (h : ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b)) :
    ((a : ℂ) * L.ω₁ + b * L.ω₂) / 2 ∉ L.lattice := by
  intro hm
  obtain ⟨m, n, hmn⟩ := mem_lattice.mp hm
  have := int_coords_eq L (a := 2 * m) (b := 2 * n) (c := a) (d := b)
    (by push_cast; linear_combination 2 * hmn)
  exact h ⟨⟨m, by omega⟩, ⟨n, by omega⟩⟩

/-- `g₂³ - 27 g₃² ≠ 0`. -/
theorem discr_ne_zero : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
  have hn : ∀ a b : ℤ, ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b) →
      ((a : ℂ) * L.ω₁ + b * L.ω₂) / 2 ∉ L.lattice := fun a b h => half_comb_notMem L h
  have h1 : L.ω₁ / 2 ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have h2 : L.ω₂ / 2 ∉ L.lattice := L.ω₂_div_two_notMem_lattice
  have h3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice := by
    have := hn 1 1 (by omega); push_cast at this; simpa using this
  set e₁ := ℘[L] (L.ω₁ / 2)
  set e₂ := ℘[L] (L.ω₂ / 2)
  set e₃ := ℘[L] ((L.ω₁ + L.ω₂) / 2)
  have c₁ := weierstrassP_half_cubic L L.ω₁_mem_lattice h1
  have c₂ := weierstrassP_half_cubic L L.ω₂_mem_lattice h2
  have c₃ := weierstrassP_half_cubic L (add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice) h3
  have d₁₂ : e₁ ≠ e₂ := by
    intro h
    rcases (weierstrassP_eq_iff L h2 h1).mp h with h' | h'
    · exact hn 1 (-1) (by omega) (by push_cast; rw [show (1 * L.ω₁ + -1 * L.ω₂) / 2 =
        L.ω₁ / 2 - L.ω₂ / 2 by ring]; exact h')
    · exact hn 1 1 (by omega) (by push_cast; rw [show (1 * L.ω₁ + 1 * L.ω₂) / 2 =
        L.ω₁ / 2 + L.ω₂ / 2 by ring]; exact h')
  have d₁₃ : e₁ ≠ e₃ := by
    intro h
    rcases (weierstrassP_eq_iff L h3 h1).mp h with h' | h'
    · exact hn 0 (-1) (by omega) (by push_cast; rw [show (0 * L.ω₁ + -1 * L.ω₂) / 2 =
        L.ω₁ / 2 - (L.ω₁ + L.ω₂) / 2 by ring]; exact h')
    · exact hn 2 1 (by omega) (by push_cast; rw [show (2 * L.ω₁ + 1 * L.ω₂) / 2 =
        L.ω₁ / 2 + (L.ω₁ + L.ω₂) / 2 by ring]; exact h')
  have d₂₃ : e₂ ≠ e₃ := by
    intro h
    rcases (weierstrassP_eq_iff L h3 h2).mp h with h' | h'
    · exact hn (-1) 0 (by omega) (by push_cast; rw [show (-1 * L.ω₁ + 0 * L.ω₂) / 2 =
        L.ω₂ / 2 - (L.ω₁ + L.ω₂) / 2 by ring]; exact h')
    · exact hn 1 2 (by omega) (by push_cast; rw [show (1 * L.ω₁ + 2 * L.ω₂) / 2 =
        L.ω₂ / 2 + (L.ω₁ + L.ω₂) / 2 by ring]; exact h')
  have hs := vieta_three (a := 0) (b := -L.g₂) (c := -L.g₃) (by linear_combination c₁)
    (by linear_combination c₂) (by linear_combination c₃) d₁₂ d₁₃ d₂₃
  have hg₂ : L.g₂ = 4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) := by
    have : (e₁ - e₂) * (4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) - L.g₂) = 0 := by
      linear_combination c₁ - c₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) d₁₂
    · linear_combination -h
  have hg₃ : L.g₃ = 4 * e₁ ^ 3 - L.g₂ * e₁ := by linear_combination -c₁
  have he₃ : e₃ = -e₁ - e₂ := by linear_combination hs
  have key : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 =
      16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
    rw [hg₃, hg₂, he₃]
    ring
  rw [key]
  have : (e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr d₁₂) (sub_ne_zero.mpr d₁₃)) (sub_ne_zero.mpr d₂₃)
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 this)

lemma curve_Δ_ne_zero : (curveA L).Δ ≠ 0 := by
  rw [show (curveA L).Δ = (curve L).Δ from rfl, curve_Δ]
  exact discr_ne_zero L

lemma equation_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    (curveA L).Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [equation_iff]
  have := L.derivWeierstrassP_sq z hz
  simp only [curveA, curve]
  linear_combination this / 4

lemma nonsingular_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    (curveA L).Nonsingular (℘[L] z) (℘'[L] z / 2) :=
  (equation_iff_nonsingular_of_Δ_ne_zero (curve_Δ_ne_zero L)).mp (equation_weierstrassP L hz)

/-! ### The map `expE` -/

open Classical in
/-- `z ↦ (℘(z), ℘'(z)/2)`, sending `Λ` to the point at infinity. -/
def expE (z : ℂ) : (curveA L).Point :=
  if h : z ∈ L.lattice then 0 else .some _ _ (nonsingular_weierstrassP L h)

lemma expE_of_mem {z : ℂ} (h : z ∈ L.lattice) : expE L z = 0 := by
  simp [expE, h]

lemma expE_of_notMem {z : ℂ} (h : z ∉ L.lattice) :
    expE L z = .some _ _ (nonsingular_weierstrassP L h) := by
  simp [expE, h]

lemma some_eq_some {x y x' y' : ℂ} {h : (curveA L).Nonsingular x y}
    {h' : (curveA L).Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy; rfl

lemma expE_zero : expE L 0 = 0 := expE_of_mem L L.lattice.zero_mem

/-- `expE` is `Λ`-periodic. -/
lemma expE_add_mem (z : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) : expE L (z + ω) = expE L z := by
  by_cases hz : z ∈ L.lattice
  · rw [expE_of_mem L hz, expE_of_mem L (add_mem hz hω)]
  · have hz' : z + ω ∉ L.lattice := add_notMem_lattice L hz hω
    rw [expE_of_notMem L hz, expE_of_notMem L hz']
    exact some_eq_some L (weierstrassP_add_mem L z hω) (by rw [derivWeierstrassP_add_mem L z hω])

lemma expE_neg (z : ℂ) : expE L (-z) = -expE L z := by
  by_cases hz : z ∈ L.lattice
  · rw [expE_of_mem L hz, expE_of_mem L (neg_mem hz), Point.neg_zero]
  · have hz' : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
    rw [expE_of_notMem L hz, expE_of_notMem L hz', Point.neg_some]
    refine some_eq_some L (L.weierstrassP_neg z) ?_
    rw [L.derivWeierstrassP_neg, negY]
    simp [curveA, curve]
    ring

/-- **`expE` is additive**: `expE (z + w) = expE z + expE w` for Mathlib's group law. -/
theorem expE_add (z w : ℂ) : expE L (z + w) = expE L z + expE L w := by
  by_cases hz : z ∈ L.lattice
  · rw [expE_of_mem L hz, zero_add, add_comm, expE_add_mem L w hz]
  by_cases hw : w ∈ L.lattice
  · rw [expE_of_mem L hw, add_zero, expE_add_mem L z hw]
  rw [expE_of_notMem L hz, expE_of_notMem L hw]
  by_cases hzw : z + w ∈ L.lattice
  · -- `w ≡ -z`
    rw [expE_of_mem L hzw]
    have hP : ℘[L] z = ℘[L] w := (weierstrassP_eq_iff L hw hz).mpr (Or.inr hzw)
    have hP' : ℘'[L] z = -℘'[L] w := by
      have := derivWeierstrassP_add_mem L (-w) hzw
      rw [show -w + (z + w) = z by ring, L.derivWeierstrassP_neg] at this
      exact this
    refine (Point.add_of_Y_eq hP ?_).symm
    rw [negY, hP']
    simp [curveA, curve]
    ring
  rw [expE_of_notMem L hzw]
  by_cases hd : z - w ∈ L.lattice
  · -- doubling: `w ≡ z`
    have hP : ℘[L] z = ℘[L] w := (weierstrassP_eq_iff L hw hz).mpr (Or.inl hd)
    have hP' : ℘'[L] z = ℘'[L] w := by
      have := derivWeierstrassP_add_mem L w hd
      rwa [show w + (z - w) = z by ring] at this
    have h2 : 2 * z ∉ L.lattice := by
      intro h
      apply hzw
      have := sub_mem h hd
      rwa [show 2 * z - (z - w) = z + w by ring] at this
    have hne := derivWeierstrassP_ne_zero L h2
    have hy : ℘'[L] z / 2 ≠ (curveA L).negY (℘[L] w) (℘'[L] w / 2) := by
      rw [negY, ← hP']
      simp only [curveA, curve, zero_mul, sub_zero]
      intro h
      apply hne
      linear_combination h
    rw [Point.add_of_Y_ne hy]
    have hzw' : z + w = 2 * z + (w - z) := by ring
    have hwz : w - z ∈ L.lattice := by simpa using neg_mem hd
    have hsl : (curveA L).slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        tangentSlope L z / 2 := by
      rw [slope_of_Y_ne hP hy, negY]
      simp only [curveA, curve, zero_mul, sub_zero, mul_zero, add_zero]
      unfold tangentSlope
      field_simp
      ring
    have hx : ℘[L] (z + w) = ℘[L] (2 * z) := by rw [hzw', weierstrassP_add_mem L _ hwz]
    have hy' : ℘'[L] (z + w) = ℘'[L] (2 * z) := by rw [hzw', derivWeierstrassP_add_mem L _ hwz]
    have hdx := weierstrassP_two_mul L h2
    have hdy := derivWeierstrassP_two_mul L h2
    refine some_eq_some L ?_ ?_
    · rw [addX, hsl, hx, hdx, ← hP]
      simp only [curveA, curve]
      ring
    · rw [addY, negAddY, addX, negY, hsl, hy', hdy, hdx, ← hP]
      simp only [curveA, curve]
      ring
  · -- generic: `℘(z) ≠ ℘(w)`
    have hdw : z - w ∉ L.lattice := hd
    have hne := pdiff_ne L hz hw hzw hdw
    have hx : ℘[L] z ≠ ℘[L] w := sub_ne_zero.mp hne
    rw [Point.add_of_X_ne hx]
    have hsl : (curveA L).slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        chordSlope L z w / 2 := by
      rw [slope_of_X_ne hx]
      unfold chordSlope
      field_simp
    have hax := weierstrassP_add L hz hw hzw hdw
    have hay := derivWeierstrassP_add L hz hw hzw hdw
    refine some_eq_some L ?_ ?_
    · rw [addX, hsl, hax]
      simp only [curveA, curve]
      ring
    · rw [addY, negAddY, addX, negY, hsl, hay, hax]
      simp only [curveA, curve]
      ring

/-- `expE` as an additive group homomorphism `ℂ →+ E(ℂ)`. -/
def expHom : ℂ →+ (curveA L).Point where
  toFun := expE L
  map_zero' := expE_zero L
  map_add' := expE_add L

@[simp] lemma expHom_apply (z : ℂ) : expHom L z = expE L z := rfl

lemma expE_intCast_mul (n : ℤ) (z : ℂ) : expE L (n * z) = n • expE L z := by
  rw [← expHom_apply, ← zsmul_eq_mul, map_zsmul, expHom_apply]

/-! ### Rational points and multiples -/

section Rational

variable (K : Subfield ℂ) (h₂ : L.g₂ ∈ K)

/-- The points of `E` with coordinates in `K` (plus the point at infinity). -/
def ratPoints : AddSubgroup (curveA L).Point where
  carrier := {P | ∀ x y (h : (curveA L).Nonsingular x y), P = .some x y h → x ∈ K ∧ y ∈ K}
  zero_mem' := by
    intro x y h hP
    exact absurd hP.symm (Point.some_ne_zero h)
  add_mem' := by
    have h4 : (curveA L).a₄ ∈ K := by
      simp only [curveA, curve]; exact K.div_mem (K.neg_mem h₂) ((by simp))
    have h1 : (curveA L).a₁ = 0 := rfl
    have h2' : (curveA L).a₂ = 0 := rfl
    have h3' : (curveA L).a₃ = 0 := rfl
    rintro (_ | ⟨x₁, y₁, n₁⟩) (_ | ⟨x₂, y₂, n₂⟩) hP hQ x y h hPQ
    · exact absurd hPQ (by rw [← Point.zero_def, zero_add]; exact (Point.some_ne_zero h).symm)
    · rw [← Point.zero_def, zero_add] at hPQ; exact hQ x y h hPQ
    · rw [← Point.zero_def, add_zero] at hPQ; exact hP x y h hPQ
    · obtain ⟨hx₁, hy₁⟩ := hP x₁ y₁ n₁ rfl
      obtain ⟨hx₂, hy₂⟩ := hQ x₂ y₂ n₂ rfl
      by_cases hxy : x₁ = x₂ ∧ y₁ = (curveA L).negY x₂ y₂
      · rw [Point.add_of_Y_eq hxy.1 hxy.2] at hPQ
        exact absurd hPQ.symm (Point.some_ne_zero h)
      · rw [Point.add_some hxy] at hPQ
        simp only [Point.some.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        have hsl : (curveA L).slope x₁ x₂ y₁ y₂ ∈ K := by
          unfold WeierstrassCurve.Affine.slope
          split_ifs
          · exact K.zero_mem
          · rw [negY, h1, h2', h3']
            refine K.div_mem ?_ ?_
            · simpa using K.add_mem (K.mul_mem ((by simp)) (K.pow_mem hx₁ 2)) h4
            · simpa using K.sub_mem hy₁ (K.neg_mem hy₁)
          · exact K.div_mem (K.sub_mem hy₁ hy₂) (K.sub_mem hx₁ hx₂)
        have hX : (curveA L).addX x₁ x₂ ((curveA L).slope x₁ x₂ y₁ y₂) ∈ K := by
          rw [addX, h1, h2']
          simpa using K.sub_mem (K.sub_mem (K.pow_mem hsl 2) hx₁) hx₂
        refine ⟨hX, ?_⟩
        rw [addY, negY, negAddY, h1, h3']
        simpa using K.neg_mem (K.add_mem (K.mul_mem hsl (K.sub_mem hX hx₁)) hy₁)
  neg_mem' := by
    rintro (_ | ⟨x₁, y₁, n₁⟩) hP x y h hPQ
    · exact absurd hPQ (by rw [← Point.zero_def, Point.neg_zero]; exact (Point.some_ne_zero h).symm)
    · obtain ⟨hx₁, hy₁⟩ := hP x₁ y₁ n₁ rfl
      rw [Point.neg_some] at hPQ
      simp only [Point.some.injEq] at hPQ
      obtain ⟨rfl, rfl⟩ := hPQ
      refine ⟨hx₁, ?_⟩
      rw [negY]
      simpa [curveA, curve] using K.neg_mem hy₁

include h₂ in
/-- **Multiples of a `K`-point.** If `℘(z), ℘'(z) ∈ K ∋ g₂`, then `℘(nz), ℘'(nz) ∈ K`
for every `n : ℤ` with `nz ∉ Λ`. -/
theorem mem_of_intCast_mul {z : ℂ} (hz : z ∉ L.lattice) (hx : ℘[L] z ∈ K) (hy : ℘'[L] z ∈ K)
    (n : ℤ) (hn : (n : ℂ) * z ∉ L.lattice) :
    ℘[L] (n * z) ∈ K ∧ ℘'[L] (n * z) ∈ K := by
  have hP : expE L z ∈ ratPoints L K h₂ := by
    intro x y h hP
    rw [expE_of_notMem L hz] at hP
    simp only [Point.some.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    exact ⟨hx, K.div_mem hy ((by simp))⟩
  have hnP := (ratPoints L K h₂).zsmul_mem hP n
  rw [← expE_intCast_mul] at hnP
  obtain ⟨h1, h2⟩ := hnP _ _ (nonsingular_weierstrassP L hn) (expE_of_notMem L hn)
  refine ⟨h1, ?_⟩
  have := K.mul_mem h2 (show (2 : ℂ) ∈ K by simp)
  rwa [div_mul_cancel₀ _ two_ne_zero] at this

end Rational

/-- **Algebraicity of multiples.** If `g₂, ℘(z), ℘'(z)` are algebraic over `F`, so are
`℘(nz), ℘'(nz)` (`nz ∉ Λ`). -/
theorem isAlgebraic_of_intCast_mul {F : Type*} [Field F] [Algebra F ℂ]
    (hg₂ : IsAlgebraic F L.g₂) {z : ℂ} (hz : z ∉ L.lattice)
    (hx : IsAlgebraic F (℘[L] z)) (hy : IsAlgebraic F (℘'[L] z)) (n : ℤ)
    (hn : (n : ℂ) * z ∉ L.lattice) :
    IsAlgebraic F (℘[L] (n * z)) ∧ IsAlgebraic F (℘'[L] (n * z)) := by
  set K := (algebraicClosure F ℂ).toSubfield
  have hK : ∀ x : ℂ, x ∈ K ↔ IsAlgebraic F x := fun x => mem_algebraicClosure_iff
  have := mem_of_intCast_mul L K ((hK _).mpr hg₂) hz ((hK _).mpr hx)
    ((hK _).mpr hy) n hn
  exact ⟨(hK _).mp this.1, (hK _).mp this.2⟩

end LSG.Weierstrass
