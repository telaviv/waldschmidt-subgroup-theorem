/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Elliptic.NaturalLaws
import LSG.Elliptic.NaturalLawsAff
import LSG.Elliptic.NaturalZeta

/-!
# The addition laws of `E^♮`: comparison with the group law (b) and completeness (c)

Group law of `E^♮` (convention of `VECEXT.md`: `exp(z, w) = (exp_E z, w − ζ(z))`):
`(P₁, t₁) + (P₂, t₂) = (P₁ + P₂, t₁ + t₂ − c(P₁, P₂))`, `c = ½ (y₁ − y₂)/(x₁ − x₂)` for `x₁ ≠ x₂`
(the `ζ` addition formula, `NaturalZeta.zeta_add_formula`).

Main results:
* **`NLaw_ptAff` ((b), generic, algebraic)**: over a field of characteristic `0`, for affine points
  `P̂ᵢ = ptAff xᵢ yᵢ tᵢ` of `E^♮` with `x₁ ≠ x₂`, every law satisfies
  `NLaw P̂₁ P̂₂ = NLaw₂(P̂₁, P̂₂) • ptAff x₃ y₃ (t₁ + t₂ − m/2)`, `(x₃, y₃)` the chord sum,
  `m = (y₁ − y₂)/(x₁ − x₂)`;
* **`NLaw_expN` ((b), generic, analytic)**: for `z₁, z₂, z₁ ± z₂ ∉ Λ`,
  `NLaw (exp(z₁, w₁)) (exp(z₂, w₂)) = NLaw₂ • exp(z₁ + z₂, w₁ + w₂)`, where
  `expN z w = ptAff (℘ z) (℘' z) (w − ζ z)`: the laws are compatible with the analytic group law;
* `NLaw_expN_of_add`: the same for all `z₁, z₂, z₁ + z₂ ∉ Λ` (doubling included), by continuity;
* **`NLaw_complete` ((c))**: for every pair of points of `E^♮` (vectors on `X` with base part
  `≠ 0`) one of the eight laws is nonzero; its base part is `2M·lawᵢ` with `lawᵢ` representing the
  `E`-sum (`toPoint_NLaw`).
The remaining cases of (b) (some of `z₁, z₂, z₁ + z₂ ∈ Λ`: a point over `O`) are not formalised
here; see `VECEXT_SPIKE.md` for the argument.
-/

open PeriodPair LSG.Weierstrass

noncomputable section

namespace LSG.Elliptic

variable {K : Type*} [Field K]

/-! ### The chord sum -/

/-- The chord slope `m = (y₁ − y₂)/(x₁ − x₂)`. -/
def slopeA (x₁ y₁ x₂ y₂ : K) : K := (y₁ - y₂) / (x₁ - x₂)

/-- `x₃ = m²/4 − x₁ − x₂`. -/
def addXA (x₁ y₁ x₂ y₂ : K) : K := slopeA x₁ y₁ x₂ y₂ ^ 2 / 4 - x₁ - x₂

/-- `y₃ = −m (x₃ − x₁) − y₁`. -/
def addYA (x₁ y₁ x₂ y₂ : K) : K := -slopeA x₁ y₁ x₂ y₂ * (addXA x₁ y₁ x₂ y₂ - x₁) - y₁

section Chord

variable [CharZero K] {x₁ y₁ x₂ y₂ : K}

omit [CharZero K] in
lemma slopeA_mul (hx : x₁ ≠ x₂) : (x₁ - x₂) * slopeA x₁ y₁ x₂ y₂ = y₁ - y₂ := by
  unfold slopeA
  field_simp [sub_ne_zero.mpr hx]

lemma addXA_mul (hx : x₁ ≠ x₂) : 4 * (x₁ - x₂) ^ 2 * addXA x₁ y₁ x₂ y₂ = affN3 x₁ y₁ x₂ y₂ := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  unfold addXA slopeA affN3
  field_simp
  ring

lemma addYA_mul (hx : x₁ ≠ x₂) : 8 * (x₁ - x₂) ^ 3 * addYA x₁ y₁ x₂ y₂ = affY3 x₁ y₁ x₂ y₂ := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have h1 := addXA_mul (y₁ := y₁) (y₂ := y₂) hx
  have h2 := slopeA_mul (y₁ := y₁) (y₂ := y₂) hx
  unfold addYA affY3
  rw [← h1]
  linear_combination (-(8 : K) * (x₁ - x₂) ^ 2 * (addXA x₁ y₁ x₂ y₂ - x₁)) * h2

/-- The shape lemma: a law-shaped vector evaluated at affine points, given the four affine
identities, is `(2M lW) •` the point `(x₃, y₃, t₁ + t₂ − m/2)`. -/
lemma shape_ptAff {t₁ t₂ lU lV lW kW kV lam mu rl rm Tl Tm : K} (hx : x₁ ≠ x₂)
    (hTl : Tl = lam * t₁ - rl) (hTm : Tm = mu * t₂ - rm)
    (E1 : 4 * (x₁ - x₂) ^ 2 * lU = lW * affN3 x₁ y₁ x₂ y₂)
    (E2 : 8 * (x₁ - x₂) ^ 3 * lV = lW * affY3 x₁ y₁ x₂ y₂)
    (K1 : (x₁ - x₂) * (kW + 2 * mu * lW * rl + 2 * lam * lW * rm) = lam * mu * lW * (y₁ - y₂))
    (K3 : 16 * (x₁ - x₂) ^ 4 * (kV + 2 * mu * lV * rl + 2 * lam * lV * rm) =
      lam * mu * lW * (2 * affY3 x₁ y₁ x₂ y₂ * (y₁ - y₂) + 4 * affN3 x₁ y₁ x₂ y₂ ^ 2)) :
    ![2 * (lam * mu) * lU, 2 * (lam * mu) * lV, 2 * (lam * mu) * lW,
      2 * mu * lW * Tl + 2 * lam * lW * Tm - kW, 2 * mu * lV * Tl + 2 * lam * lV * Tm - kV] =
      (2 * (lam * mu) * lW) • ptAff (addXA x₁ y₁ x₂ y₂) (addYA x₁ y₁ x₂ y₂)
        (t₁ + t₂ - slopeA x₁ y₁ x₂ y₂ / 2) := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hx3 := addXA_mul (y₁ := y₁) (y₂ := y₂) hx
  have hy3 := addYA_mul (y₁ := y₁) (y₂ := y₂) hx
  have hm := slopeA_mul (y₁ := y₁) (y₂ := y₂) hx
  set x₃ := addXA x₁ y₁ x₂ y₂
  set y₃ := addYA x₁ y₁ x₂ y₂
  set m := slopeA x₁ y₁ x₂ y₂
  set N := affN3 x₁ y₁ x₂ y₂
  set Y := affY3 x₁ y₁ x₂ y₂
  set d := x₁ - x₂
  subst hTl hTm
  funext c
  fin_cases c <;> simp only [ptAff, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one,
    Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
  · apply mul_left_cancel₀
      (show (4 : K) * d ^ 2 ≠ 0 from mul_ne_zero (by norm_num) (pow_ne_zero 2 hd))
    linear_combination (2 * (lam * mu)) * E1 - 2 * (lam * mu) * lW * hx3
  · apply mul_left_cancel₀
      (show (8 : K) * d ^ 3 ≠ 0 from mul_ne_zero (by norm_num) (pow_ne_zero 3 hd))
    linear_combination (2 * (lam * mu)) * E2 - 2 * (lam * mu) * lW * hy3
  · ring
  · apply mul_left_cancel₀ hd
    linear_combination -K1 + lam * mu * lW * hm
  · apply mul_left_cancel₀
      (show (16 : K) * d ^ 4 ≠ 0 from mul_ne_zero (by norm_num) (pow_ne_zero 4 hd))
    linear_combination 4 * (lam * mu) * d * (t₁ + t₂) * E2 -
      4 * (lam * mu) * d * (t₁ + t₂) * lW * hy3 - K3 + 2 * (lam * mu) * lW * (d * m) * hy3 +
      2 * (lam * mu) * lW * Y * hm + 4 * (lam * mu) * lW * (4 * d ^ 2 * x₃ + N) * hx3

end Chord

lemma Pe_ptAff (x y t : K) : Pe (ptAff x y t) = ![x, y, 1] := by
  funext c
  fin_cases c <;> rfl

/-- **(b), generic case, algebraic.** For affine points of `E^♮` with `x₁ ≠ x₂`, every law
`NLaw i j k` equals its `W`-component times the point
`(x₃, y₃, t₁ + t₂ − m/2)` (`(x₃, y₃)` = chord sum on `E`, `m` = chord slope). -/
theorem NLaw_ptAff [CharZero K] {g₂ g₃ x₁ y₁ t₁ x₂ y₂ t₂ : K}
    (hP : y₁ ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃) (hQ : y₂ ^ 2 = 4 * x₂ ^ 3 - g₂ * x₂ - g₃)
    (hx : x₁ ≠ x₂) (i j k : Fin 2) :
    NLaw g₂ g₃ i j k (ptAff x₁ y₁ t₁) (ptAff x₂ y₂ t₂) =
      NLaw g₂ g₃ i j k (ptAff x₁ y₁ t₁) (ptAff x₂ y₂ t₂) 2 •
        ptAff (addXA x₁ y₁ x₂ y₂) (addYA x₁ y₁ x₂ y₂) (t₁ + t₂ - slopeA x₁ y₁ x₂ y₂ / 2) := by
  have hTV1 : tcoord 0 (ptAff x₁ y₁ t₁) = y₁ * t₁ - 2 * x₁ ^ 2 := rfl
  have hTW1 : tcoord 1 (ptAff x₁ y₁ t₁) = 1 * t₁ - 0 := by simp [tcoord, ptAff]
  have hTV2 : tcoord 0 (ptAff x₂ y₂ t₂) = y₂ * t₂ - 2 * x₂ ^ 2 := rfl
  have hTW2 : tcoord 1 (ptAff x₂ y₂ t₂) = 1 * t₂ - 0 := by simp [tcoord, ptAff]
  simp only [NLaw, Pe_ptAff]
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact shape_ptAff hx hTV1 hTV2 (affE1₁ hP hQ) (affE2₁ hP hQ) (affK1₁VV hP hQ) (affK3₁VV hP hQ)
  · exact shape_ptAff hx hTV1 hTW2 (affE1₁ hP hQ) (affE2₁ hP hQ) (affK1₁VW hP hQ) (affK3₁VW hP hQ)
  · exact shape_ptAff hx hTW1 hTV2 (affE1₁ hP hQ) (affE2₁ hP hQ) (affK1₁WV hP hQ) (affK3₁WV hP hQ)
  · exact shape_ptAff hx hTW1 hTW2 (affE1₁ hP hQ) (affE2₁ hP hQ) (affK1₁WW hP hQ) (affK3₁WW hP hQ)
  · exact shape_ptAff hx hTV1 hTV2 (affE1₂ hP hQ) (affE2₂ hP hQ) (affK1₂VV hP hQ) (affK3₂VV hP hQ)
  · exact shape_ptAff hx hTV1 hTW2 (affE1₂ hP hQ) (affE2₂ hP hQ) (affK1₂VW hP hQ) (affK3₂VW hP hQ)
  · exact shape_ptAff hx hTW1 hTV2 (affE1₂ hP hQ) (affE2₂ hP hQ) (affK1₂WV hP hQ) (affK3₂WV hP hQ)
  · exact shape_ptAff hx hTW1 hTW2 (affE1₂ hP hQ) (affE2₂ hP hQ) (affK1₂WW hP hQ) (affK3₂WW hP hQ)

/-! ### Compatibility with the analytic group law -/

section Analytic

variable (L : PeriodPair)

/-- The exponential map of `E^♮` into the model:
`exp(z, w) = (℘(z) : ℘'(z) : 1 : t : ℘'(z) t − 2℘(z)²)`, `t = w − ζ(z)`,
for `z ∉ Λ`; over `O` (`z ∈ Λ`) the point `(0 : 1 : 0 : 0 : w − ζ(z))`. -/
def expN (z w : ℂ) : Fin 5 → ℂ :=
  open Classical in
  if z ∈ L.lattice then ptO (w - zeta L z) else ptAff (℘[L] z) (℘'[L] z) (w - zeta L z)

lemma expN_of_notMem {z : ℂ} (hz : z ∉ L.lattice) (w : ℂ) :
    expN L z w = ptAff (℘[L] z) (℘'[L] z) (w - zeta L z) := by
  simp [expN, hz]

lemma Fn_expN (z w : ℂ) : Fn L.g₂ L.g₃ (expN L z w) = 0 := by
  unfold expN
  split_ifs with hz
  · exact Fn_ptO _ _ _
  · exact Fn_ptAff _ (L.derivWeierstrassP_sq z hz)

lemma Gn_expN (z w : ℂ) : Gn (expN L z w) = 0 := by
  unfold expN
  split_ifs
  · exact Gn_ptO _
  · exact Gn_ptAff _ _ _

/-- **(b), generic case, analytic.** For `z₁, z₂, z₁ ± z₂ ∉ Λ`, every law maps
`(exp(z₁, w₁), exp(z₂, w₂))` to a multiple of `exp(z₁ + z₂, w₁ + w₂)`. -/
theorem NLaw_expN {z₁ z₂ : ℂ} (h₁ : z₁ ∉ L.lattice) (h₂ : z₂ ∉ L.lattice)
    (hp : z₁ + z₂ ∉ L.lattice) (hm : z₁ - z₂ ∉ L.lattice) (w₁ w₂ : ℂ) (i j k : Fin 2) :
    NLaw L.g₂ L.g₃ i j k (expN L z₁ w₁) (expN L z₂ w₂) =
      NLaw L.g₂ L.g₃ i j k (expN L z₁ w₁) (expN L z₂ w₂) 2 • expN L (z₁ + z₂) (w₁ + w₂) := by
  have hne := pdiff_ne L h₁ h₂ hp hm
  have hx : ℘[L] z₁ ≠ ℘[L] z₂ := sub_ne_zero.mp hne
  rw [expN_of_notMem L h₁, expN_of_notMem L h₂, expN_of_notMem L hp]
  conv_lhs => rw [NLaw_ptAff (L.derivWeierstrassP_sq z₁ h₁) (L.derivWeierstrassP_sq z₂ h₂) hx]
  have hX : addXA (℘[L] z₁) (℘'[L] z₁) (℘[L] z₂) (℘'[L] z₂) = ℘[L] (z₁ + z₂) := by
    rw [weierstrassP_add L h₁ h₂ hp hm]
    unfold addXA slopeA chordSlope
    ring
  have hY : addYA (℘[L] z₁) (℘'[L] z₁) (℘[L] z₂) (℘'[L] z₂) = ℘'[L] (z₁ + z₂) := by
    rw [derivWeierstrassP_add L h₁ h₂ hp hm, addYA, hX]
    rfl
  have hT : w₁ - zeta L z₁ + (w₂ - zeta L z₂) - slopeA (℘[L] z₁) (℘'[L] z₁) (℘[L] z₂) (℘'[L] z₂) / 2
      = w₁ + w₂ - zeta L (z₁ + z₂) := by
    have := zeta_add_formula L h₁ h₂ hp hm
    unfold chordSlope at this
    unfold slopeA
    linear_combination this
  rw [hX, hY, hT]

/-- Each component of a law is a polynomial, hence continuous, in the second point. -/
lemma continuous_NLaw_right (g₂ g₃ : ℂ) (i j k : Fin 2) (P₀ : Fin 5 → ℂ) (c : Fin 5) :
    Continuous (fun Q : Fin 5 → ℂ => NLaw g₂ g₃ i j k P₀ Q c) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases c <;>
  simp only [NLaw, lawSel, kapW, kapV, mult, tcoord, Pe, law₁, law₂, law₁U, law₁V, law₁W, law₂U,
    law₂V, law₂W, kapW₁VV, kapW₁VW, kapW₁WV, kapW₁WW, kapW₂VV, kapW₂VW, kapW₂WV, kapW₂WW, kapV₁VV,
    kapV₁VW, kapV₁WV, kapV₁WW, kapV₂VV, kapV₂VW, kapV₂WV, kapV₂WW, Fin.zero_eta, Fin.mk_one,
    Fin.isValue, Fin.reduceFinMk, Matrix.cons_val] <;>
  fun_prop

lemma continuousAt_ptAff {f g h : ℂ → ℂ} {u : ℂ} (hf : ContinuousAt f u) (hg : ContinuousAt g u)
    (hh : ContinuousAt h u) : ContinuousAt (fun v => ptAff (f v) (g v) (h v)) u := by
  refine continuousAt_pi.2 fun c => ?_
  fin_cases c
  · simpa [ptAff] using hf
  · simpa [ptAff] using hg
  · simpa [ptAff] using continuousAt_const
  · simpa [ptAff] using hh
  · simp only [ptAff, Fin.reduceFinMk, Matrix.cons_val]
    exact (hg.mul hh).sub (continuousAt_const.mul (hf.pow 2))

/-- **(b) for `z₁, z₂, z₁ + z₂ ∉ Λ`** (including the doubling case `z₁ − z₂ ∈ Λ`): by continuity
in `z₂` from `NLaw_expN`. -/
theorem NLaw_expN_of_add {z₁ z₂ : ℂ} (h₁ : z₁ ∉ L.lattice) (h₂ : z₂ ∉ L.lattice)
    (hp : z₁ + z₂ ∉ L.lattice) (w₁ w₂ : ℂ) (i j k : Fin 2) :
    NLaw L.g₂ L.g₃ i j k (expN L z₁ w₁) (expN L z₂ w₂) =
      NLaw L.g₂ L.g₃ i j k (expN L z₁ w₁) (expN L z₂ w₂) 2 • expN L (z₁ + z₂) (w₁ + w₂) := by
  by_cases hm : z₁ - z₂ ∈ L.lattice
  swap
  · exact NLaw_expN L h₁ h₂ hp hm w₁ w₂ i j k
  set P₀ := expN L z₁ w₁
  set e : ℂ → Fin 5 → ℂ := fun v => ptAff (℘[L] v) (℘'[L] v) (w₂ - zeta L v) with he_def
  set s : ℂ → Fin 5 → ℂ := fun v =>
    ptAff (℘[L] (z₁ + v)) (℘'[L] (z₁ + v)) (w₁ + w₂ - zeta L (z₁ + v)) with hs_def
  have hzc : ∀ {u : ℂ}, u ∉ L.lattice → ContinuousAt (zeta L) u :=
    fun hu => (hasDerivAt_zeta L hu).continuousAt
  have he : ContinuousAt e z₂ :=
    continuousAt_ptAff (continuousAt_weierstrassP L h₂) (continuousAt_derivWeierstrassP L h₂)
      (continuousAt_const.sub (hzc h₂))
  have hadd : ContinuousAt (fun v : ℂ => z₁ + v) z₂ := continuousAt_const.add continuousAt_id
  have hs : ContinuousAt s z₂ :=
    continuousAt_ptAff ((continuousAt_weierstrassP L hp).comp hadd)
      ((continuousAt_derivWeierstrassP L hp).comp hadd)
      (continuousAt_const.sub ((hzc hp).comp hadd))
  rw [expN_of_notMem L h₂, expN_of_notMem L hp]
  funext c
  have c1 : ContinuousAt (fun v => NLaw L.g₂ L.g₃ i j k P₀ (e v) c) z₂ :=
    (continuous_NLaw_right L.g₂ L.g₃ i j k P₀ c).continuousAt.comp he
  have c2 : ContinuousAt (fun v => NLaw L.g₂ L.g₃ i j k P₀ (e v) 2 * s v c) z₂ :=
    ((continuous_NLaw_right L.g₂ L.g₃ i j k P₀ 2).continuousAt.comp he).mul
      ((continuous_apply c).continuousAt.comp hs)
  have key := eq_of_eventuallyEq_nhdsNE (F₁ := fun v => NLaw L.g₂ L.g₃ i j k P₀ (e v) c)
    (F₂ := fun v => NLaw L.g₂ L.g₃ i j k P₀ (e v) 2 * s v c) (u := z₂) c1 c2 (by
      filter_upwards [eventually_generic L z₁ z₂] with v ⟨hv, hpv, hmv, _, _⟩
      have := NLaw_expN L h₁ hv hpv hmv w₁ w₂ i j k
      rw [expN_of_notMem L hv, expN_of_notMem L hpv] at this
      exact congrFun this c)
  simp only [Pi.smul_apply, smul_eq_mul]
  exact key

end Analytic

/-! ### Completeness -/

section Complete

variable [DecidableEq K] {g₂ g₃ : K}

lemma exists_mult_ne_zero (h2 : (2 : K) ≠ 0) {P : Fin 3 → K} (hP : Fv g₂ g₃ P = 0) (hP0 : P ≠ 0) :
    ∃ j : Fin 2, mult j P ≠ 0 := by
  by_contra! h
  have hV : P 1 = 0 := h 0
  have hW : P 2 = 0 := h 1
  have hU : P 0 = 0 := by
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    simp only [Fv, F, hV, hW] at hP
    have : 4 * P 0 ^ 3 = 0 := by linear_combination -hP
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left h4)
  apply hP0
  funext c
  fin_cases c <;> simp [hU, hV, hW]

/-- **(c) Completeness.** For any two points of `E^♮ ⊂ X` (vectors with `F = 0` and base part
`≠ 0`; `G = 0` is not even needed) one of the eight laws is nonzero, with `E`-part `2M·lawᵢ ≠ 0`. -/
theorem NLaw_complete (h2 : (2 : K) ≠ 0) (hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) {P Q : Fin 5 → K}
    (hP : Fn g₂ g₃ P = 0) (hQ : Fn g₂ g₃ Q = 0) (hP0 : Pe P ≠ 0) (hQ0 : Pe Q ≠ 0) :
    ∃ i j k : Fin 2, lawSel g₂ g₃ i (Pe P) (Pe Q) ≠ 0 ∧ mult j (Pe P) ≠ 0 ∧ mult k (Pe Q) ≠ 0 ∧
      NLaw g₂ g₃ i j k P Q ≠ 0 := by
  rw [Fn_eq_Fv] at hP hQ
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, lawSel g₂ g₃ i (Pe P) (Pe Q) ≠ 0 := by
    rcases law_complete h2 hΔ hP hQ hP0 hQ0 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨j, hj⟩ := exists_mult_ne_zero h2 hP hP0
  obtain ⟨k, hk⟩ := exists_mult_ne_zero h2 hQ hQ0
  refine ⟨i, j, k, hi, hj, hk, fun h0 => hi ?_⟩
  funext c
  have hc := congrFun h0 c.castSucc.castSucc
  have hM : 2 * (mult j (Pe P) * mult k (Pe Q)) ≠ 0 := mul_ne_zero h2 (mul_ne_zero hj hk)
  fin_cases c <;>
  · simp only [NLaw, Pi.zero_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
      Fin.castSucc_zero, Fin.castSucc_one, Matrix.cons_val] at hc ⊢
    exact (mul_eq_zero.mp hc).resolve_left hM

/-- With (c): a nonzero law at `(P, Q)` has base part representing the `E`-sum (Mathlib's group
law on `curve g₂ g₃`). -/
theorem toPoint_NLaw (h2 : (2 : K) ≠ 0) (hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) {P Q : Fin 5 → K}
    (hP : Fn g₂ g₃ P = 0) (hQ : Fn g₂ g₃ Q = 0) (hP0 : Pe P ≠ 0) (hQ0 : Pe Q ≠ 0)
    {i j k : Fin 2} (hl : lawSel g₂ g₃ i (Pe P) (Pe Q) ≠ 0) (hj : mult j (Pe P) ≠ 0)
    (hk : mult k (Pe Q) ≠ 0) :
    toPoint g₂ g₃ (Pe (NLaw g₂ g₃ i j k P Q)) = toPoint g₂ g₃ (Pe P) + toPoint g₂ g₃ (Pe Q) := by
  rw [Fn_eq_Fv] at hP hQ
  have hM : 2 * (mult j (Pe P) * mult k (Pe Q)) ≠ 0 := mul_ne_zero h2 (mul_ne_zero hj hk)
  have he : Pe (NLaw g₂ g₃ i j k P Q) =
      (2 * (mult j (Pe P) * mult k (Pe Q))) • lawSel g₂ g₃ i (Pe P) (Pe Q) := by
    funext c
    fin_cases c <;> rfl
  rw [he, toPoint_smul _ hM]
  fin_cases i
  · exact toPoint_law₁ h2 hΔ hP hQ hP0 hQ0 hl
  · exact toPoint_law₂ h2 hΔ hP hQ hP0 hQ0 hl

end Complete

end LSG.Elliptic
