/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Elliptic.NaturalGroup
import LSG.Elliptic.NaturalLawsSpecial

/-!
# (b) in all cases: the laws represent the group law of `E^♮` everywhere

Points of `E^♮ ⊂ X` are `ptAff x y t` (over affine points) and `ptO w` (over `O`)
(`eq_ptAff_or_ptO`). In these coordinates the group law of `E^♮` is
* generic (`x₁ ≠ x₂`): `(x₁, y₁, t₁) + (x₂, y₂, t₂) = (P₁ + P₂, t₁ + t₂ − m/2)`, `m` the chord slope
  (`NLaw_ptAff`, file `NaturalGroup`);
* doubling (`y ≠ 0`): `(x, y, t₁) + (x, y, t₂) = (2P, t₁ + t₂ − m/2)`, `m = (12x² − g₂)/(2y)`
  (`NLaw_dbl`);
* opposite points: `(x, y, t₁) + (x, −y, t₂) = (O, t₁ + t₂)` (`NLaw_neg`);
* points over `O`: `(O, w) + (x, y, t) = (x, y, t + w)` (`NLaw_ptO_left`, `NLaw_ptO_right`),
  `(O, w₁) + (O, w₂) = (O, w₁ + w₂)` (`NLaw_ptO_ptO`).
Each law `NLaw i j k` maps the pair to a scalar multiple of the sum. Analytically
(`NLaw_expN_all`): for **all** `(z₁, w₁), (z₂, w₂) ∈ ℂ²`,
`NLaw (exp(z₁, w₁)) (exp(z₂, w₂)) = c • exp(z₁ + z₂, w₁ + w₂)` for some `c`, where `exp = expN`.
With `NLaw_complete` (some law is nonzero, file `NaturalGroup`) this is a complete system of
addition laws for `E^♮` compatible with the analytic group law.
-/

open PeriodPair LSG.Weierstrass

noncomputable section

namespace LSG.Elliptic

section Shapes

variable {R : Type*} [CommRing R]

lemma Pe_ptO (w : R) : Pe (ptO w) = ![0, 1, 0] := by
  funext c
  fin_cases c <;> rfl

lemma Pe_ptAff' (x y t : R) : Pe (ptAff x y t) = ![x, y, 1] := by
  funext c
  fin_cases c <;> rfl

lemma shape_Oleft {x y t w s lam mu rho Tl Tm l0 l1 l2 kW kV : R}
    (hl0 : l0 = s * x) (hl1 : l1 = s * y) (hl2 : l2 = s * 1) (hTl : Tl = lam * w)
    (hTm : Tm = mu * t - rho) (hkW : kW = lam * (-2 * s * rho))
    (hkV : kV = lam * (4 * mu * s * x ^ 2 - 2 * s * y * rho)) :
    ![2 * (lam * mu) * l0, 2 * (lam * mu) * l1, 2 * (lam * mu) * l2,
      2 * mu * l2 * Tl + 2 * lam * l2 * Tm - kW, 2 * mu * l1 * Tl + 2 * lam * l1 * Tm - kV] =
      (2 * (lam * mu) * l2) • ptAff x y (t + w) := by
  subst hl0 hl1 hl2 hTl hTm hkW hkV
  funext c
  fin_cases c <;> simp [ptAff]
  all_goals ring

lemma shape_Oright {x y t w s lam mu rho Tl Tm l0 l1 l2 kW kV : R}
    (hl0 : l0 = s * x) (hl1 : l1 = s * y) (hl2 : l2 = s * 1) (hTl : Tl = lam * t - rho)
    (hTm : Tm = mu * w) (hkW : kW = mu * (-2 * s * rho))
    (hkV : kV = mu * (4 * lam * s * x ^ 2 - 2 * s * y * rho)) :
    ![2 * (lam * mu) * l0, 2 * (lam * mu) * l1, 2 * (lam * mu) * l2,
      2 * mu * l2 * Tl + 2 * lam * l2 * Tm - kW, 2 * mu * l1 * Tl + 2 * lam * l1 * Tm - kV] =
      (2 * (lam * mu) * l2) • ptAff x y (t + w) := by
  subst hl0 hl1 hl2 hTl hTm hkW hkV
  funext c
  fin_cases c <;> simp [ptAff]
  all_goals ring

lemma shape_OO {w₁ w₂ s lam mu Tl Tm l0 l1 l2 kW kV : R}
    (hl0 : l0 = s * 0) (hl1 : l1 = s * 1) (hl2 : l2 = s * 0) (hTl : Tl = lam * w₁)
    (hTm : Tm = mu * w₂) (hkW : kW = 0) (hkV : kV = 0) :
    ![2 * (lam * mu) * l0, 2 * (lam * mu) * l1, 2 * (lam * mu) * l2,
      2 * mu * l2 * Tl + 2 * lam * l2 * Tm - kW, 2 * mu * l1 * Tl + 2 * lam * l1 * Tm - kV] =
      (2 * (lam * mu) * l1) • ptO (w₁ + w₂) := by
  subst hl0 hl1 hl2 hTl hTm hkW hkV
  funext c
  fin_cases c <;> simp [ptO]
  all_goals ring

lemma shape_neg {t₁ t₂ lam mu rl rm Tl Tm l0 l1 l2 kW kV : R}
    (hl0 : l0 = 0) (hl2 : l2 = 0) (hTl : Tl = lam * t₁ - rl) (hTm : Tm = mu * t₂ - rm)
    (hkW : kW = 0) (hkV : kV = -2 * l1 * (mu * rl + lam * rm)) :
    ![2 * (lam * mu) * l0, 2 * (lam * mu) * l1, 2 * (lam * mu) * l2,
      2 * mu * l2 * Tl + 2 * lam * l2 * Tm - kW, 2 * mu * l1 * Tl + 2 * lam * l1 * Tm - kV] =
      (2 * (lam * mu) * l1) • ptO (t₁ + t₂) := by
  subst hl0 hl2 hTl hTm hkW hkV
  funext c
  fin_cases c <;> simp [ptO]
  all_goals ring

end Shapes

/-! ### Points over `O` -/

section Special

variable {R : Type*} [CommRing R] {g₂ g₃ x y : R}

lemma tcoord_ptO (j : Fin 2) (w : R) : tcoord j (ptO w) = mult j ![0, 1, 0] * w := by
  fin_cases j <;> simp [tcoord, ptO, mult]

lemma tcoord_ptAff_V (x y t : R) : tcoord 0 (ptAff x y t) = mult 0 ![x, y, 1] * t - 2 * x ^ 2 :=
  rfl

lemma tcoord_ptAff_W (x y t : R) : tcoord 1 (ptAff x y t) = mult 1 ![x, y, 1] * t - 0 := by
  simp [tcoord, ptAff, mult]

/-- `(O, w) + (P, t) = (P, t + w)`. -/
theorem NLaw_ptO_left (hP : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃) (w t : R) (i j k : Fin 2) :
    NLaw g₂ g₃ i j k (ptO w) (ptAff x y t) =
      NLaw g₂ g₃ i j k (ptO w) (ptAff x y t) 2 • ptAff x y (t + w) := by
  have hV := tcoord_ptAff_V x y t
  have hW := tcoord_ptAff_W x y t
  have hO0 := tcoord_ptO 0 w
  have hO1 := tcoord_ptO 1 w
  simp only [NLaw, Pe_ptO, Pe_ptAff']
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact shape_Oleft (lawVal₁U_OA hP) (lawVal₁V_OA hP) (lawVal₁W_OA hP) hO0 hV
      (kapWVal₁VV_OA hP) (kapVVal₁VV_OA hP)
  · exact shape_Oleft (lawVal₁U_OA hP) (lawVal₁V_OA hP) (lawVal₁W_OA hP) hO0 hW
      (kapWVal₁VW_OA hP) (kapVVal₁VW_OA hP)
  · exact shape_Oleft (lawVal₁U_OA hP) (lawVal₁V_OA hP) (lawVal₁W_OA hP) hO1 hV
      (kapWVal₁WV_OA hP) (kapVVal₁WV_OA hP)
  · exact shape_Oleft (lawVal₁U_OA hP) (lawVal₁V_OA hP) (lawVal₁W_OA hP) hO1 hW
      (kapWVal₁WW_OA hP) (kapVVal₁WW_OA hP)
  · exact shape_Oleft (lawVal₂U_OA hP) (lawVal₂V_OA hP) (lawVal₂W_OA hP) hO0 hV
      (kapWVal₂VV_OA hP) (kapVVal₂VV_OA hP)
  · exact shape_Oleft (lawVal₂U_OA hP) (lawVal₂V_OA hP) (lawVal₂W_OA hP) hO0 hW
      (kapWVal₂VW_OA hP) (kapVVal₂VW_OA hP)
  · exact shape_Oleft (lawVal₂U_OA hP) (lawVal₂V_OA hP) (lawVal₂W_OA hP) hO1 hV
      (kapWVal₂WV_OA hP) (kapVVal₂WV_OA hP)
  · exact shape_Oleft (lawVal₂U_OA hP) (lawVal₂V_OA hP) (lawVal₂W_OA hP) hO1 hW
      (kapWVal₂WW_OA hP) (kapVVal₂WW_OA hP)

/-- `(P, t) + (O, w) = (P, t + w)`. -/
theorem NLaw_ptO_right (hP : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃) (t w : R) (i j k : Fin 2) :
    NLaw g₂ g₃ i j k (ptAff x y t) (ptO w) =
      NLaw g₂ g₃ i j k (ptAff x y t) (ptO w) 2 • ptAff x y (t + w) := by
  have hV := tcoord_ptAff_V x y t
  have hW := tcoord_ptAff_W x y t
  have hO0 := tcoord_ptO 0 w
  have hO1 := tcoord_ptO 1 w
  simp only [NLaw, Pe_ptO, Pe_ptAff']
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact shape_Oright (lawVal₁U_AO hP) (lawVal₁V_AO hP) (lawVal₁W_AO hP) hV hO0
      (kapWVal₁VV_AO hP) (kapVVal₁VV_AO hP)
  · exact shape_Oright (lawVal₁U_AO hP) (lawVal₁V_AO hP) (lawVal₁W_AO hP) hV hO1
      (kapWVal₁VW_AO hP) (kapVVal₁VW_AO hP)
  · exact shape_Oright (lawVal₁U_AO hP) (lawVal₁V_AO hP) (lawVal₁W_AO hP) hW hO0
      (kapWVal₁WV_AO hP) (kapVVal₁WV_AO hP)
  · exact shape_Oright (lawVal₁U_AO hP) (lawVal₁V_AO hP) (lawVal₁W_AO hP) hW hO1
      (kapWVal₁WW_AO hP) (kapVVal₁WW_AO hP)
  · exact shape_Oright (lawVal₂U_AO hP) (lawVal₂V_AO hP) (lawVal₂W_AO hP) hV hO0
      (kapWVal₂VV_AO hP) (kapVVal₂VV_AO hP)
  · exact shape_Oright (lawVal₂U_AO hP) (lawVal₂V_AO hP) (lawVal₂W_AO hP) hV hO1
      (kapWVal₂VW_AO hP) (kapVVal₂VW_AO hP)
  · exact shape_Oright (lawVal₂U_AO hP) (lawVal₂V_AO hP) (lawVal₂W_AO hP) hW hO0
      (kapWVal₂WV_AO hP) (kapVVal₂WV_AO hP)
  · exact shape_Oright (lawVal₂U_AO hP) (lawVal₂V_AO hP) (lawVal₂W_AO hP) hW hO1
      (kapWVal₂WW_AO hP) (kapVVal₂WW_AO hP)

/-- `(O, w₁) + (O, w₂) = (O, w₁ + w₂)`. -/
theorem NLaw_ptO_ptO (w₁ w₂ : R) (i j k : Fin 2) :
    NLaw g₂ g₃ i j k (ptO w₁) (ptO w₂) =
      NLaw g₂ g₃ i j k (ptO w₁) (ptO w₂) 1 • ptO (w₁ + w₂) := by
  have hO0 := tcoord_ptO 0 w₁
  have hO1 := tcoord_ptO 1 w₁
  have hO0' := tcoord_ptO 0 w₂
  have hO1' := tcoord_ptO 1 w₂
  simp only [NLaw, Pe_ptO]
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact shape_OO (lawVal₁U_OO g₂ g₃) (lawVal₁V_OO g₂ g₃) (lawVal₁W_OO g₂ g₃) hO0 hO0'
      (kapWVal₁VV_OO g₂ g₃) (kapVVal₁VV_OO g₂ g₃)
  · exact shape_OO (lawVal₁U_OO g₂ g₃) (lawVal₁V_OO g₂ g₃) (lawVal₁W_OO g₂ g₃) hO0 hO1'
      (kapWVal₁VW_OO g₂ g₃) (kapVVal₁VW_OO g₂ g₃)
  · exact shape_OO (lawVal₁U_OO g₂ g₃) (lawVal₁V_OO g₂ g₃) (lawVal₁W_OO g₂ g₃) hO1 hO0'
      (kapWVal₁WV_OO g₂ g₃) (kapVVal₁WV_OO g₂ g₃)
  · exact shape_OO (lawVal₁U_OO g₂ g₃) (lawVal₁V_OO g₂ g₃) (lawVal₁W_OO g₂ g₃) hO1 hO1'
      (kapWVal₁WW_OO g₂ g₃) (kapVVal₁WW_OO g₂ g₃)
  · exact shape_OO (lawVal₂U_OO g₂ g₃) (lawVal₂V_OO g₂ g₃) (lawVal₂W_OO g₂ g₃) hO0 hO0'
      (kapWVal₂VV_OO g₂ g₃) (kapVVal₂VV_OO g₂ g₃)
  · exact shape_OO (lawVal₂U_OO g₂ g₃) (lawVal₂V_OO g₂ g₃) (lawVal₂W_OO g₂ g₃) hO0 hO1'
      (kapWVal₂VW_OO g₂ g₃) (kapVVal₂VW_OO g₂ g₃)
  · exact shape_OO (lawVal₂U_OO g₂ g₃) (lawVal₂V_OO g₂ g₃) (lawVal₂W_OO g₂ g₃) hO1 hO0'
      (kapWVal₂WV_OO g₂ g₃) (kapVVal₂WV_OO g₂ g₃)
  · exact shape_OO (lawVal₂U_OO g₂ g₃) (lawVal₂V_OO g₂ g₃) (lawVal₂W_OO g₂ g₃) hO1 hO1'
      (kapWVal₂WW_OO g₂ g₃) (kapVVal₂WW_OO g₂ g₃)

/-- Opposite points: `(P, t₁) + (−P, t₂) = (O, t₁ + t₂)`. -/
theorem NLaw_neg (hP : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃) (t₁ t₂ : R) (i j k : Fin 2) :
    NLaw g₂ g₃ i j k (ptAff x y t₁) (ptAff x (-y) t₂) =
      NLaw g₂ g₃ i j k (ptAff x y t₁) (ptAff x (-y) t₂) 1 • ptO (t₁ + t₂) := by
  have hV := tcoord_ptAff_V x y t₁
  have hW := tcoord_ptAff_W x y t₁
  have hV' := tcoord_ptAff_V x (-y) t₂
  have hW' := tcoord_ptAff_W x (-y) t₂
  simp only [NLaw, Pe_ptAff']
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact shape_neg (lawVal₁U_AAn hP) (lawVal₁W_AAn hP) hV hV'
      (kapWVal₁VV_AAn hP) (kapVVal₁VV_AAn hP)
  · exact shape_neg (lawVal₁U_AAn hP) (lawVal₁W_AAn hP) hV hW'
      (kapWVal₁VW_AAn hP) (kapVVal₁VW_AAn hP)
  · exact shape_neg (lawVal₁U_AAn hP) (lawVal₁W_AAn hP) hW hV'
      (kapWVal₁WV_AAn hP) (kapVVal₁WV_AAn hP)
  · exact shape_neg (lawVal₁U_AAn hP) (lawVal₁W_AAn hP) hW hW'
      (kapWVal₁WW_AAn hP) (kapVVal₁WW_AAn hP)
  · exact shape_neg (lawVal₂U_AAn hP) (lawVal₂W_AAn hP) hV hV'
      (kapWVal₂VV_AAn hP) (kapVVal₂VV_AAn hP)
  · exact shape_neg (lawVal₂U_AAn hP) (lawVal₂W_AAn hP) hV hW'
      (kapWVal₂VW_AAn hP) (kapVVal₂VW_AAn hP)
  · exact shape_neg (lawVal₂U_AAn hP) (lawVal₂W_AAn hP) hW hV'
      (kapWVal₂WV_AAn hP) (kapVVal₂WV_AAn hP)
  · exact shape_neg (lawVal₂U_AAn hP) (lawVal₂W_AAn hP) hW hW'
      (kapWVal₂WW_AAn hP) (kapVVal₂WW_AAn hP)

end Special

/-! ### Doubling -/

section Doubling

variable {K : Type*} [Field K] [CharZero K]

/-- The general shape lemma (`d`, `e` abstract; `shape_ptAff` is the case `d = x₁ − x₂`,
`e = y₁ − y₂`). -/
lemma shape_gen {d e m x₃ y₃ N Y t₁ t₂ lU lV lW kW kV lam mu rl rm Tl Tm : K} (hd : d ≠ 0)
    (hm : d * m = e) (hx3 : 4 * d ^ 2 * x₃ = N) (hy3 : 8 * d ^ 3 * y₃ = Y)
    (hTl : Tl = lam * t₁ - rl) (hTm : Tm = mu * t₂ - rm)
    (E1 : 4 * d ^ 2 * lU = lW * N) (E2 : 8 * d ^ 3 * lV = lW * Y)
    (K1 : d * (kW + 2 * mu * lW * rl + 2 * lam * lW * rm) = lam * mu * lW * e)
    (K3 : 16 * d ^ 4 * (kV + 2 * mu * lV * rl + 2 * lam * lV * rm) =
      lam * mu * lW * (2 * Y * e + 4 * N ^ 2)) :
    ![2 * (lam * mu) * lU, 2 * (lam * mu) * lV, 2 * (lam * mu) * lW,
      2 * mu * lW * Tl + 2 * lam * lW * Tm - kW, 2 * mu * lV * Tl + 2 * lam * lV * Tm - kV] =
      (2 * (lam * mu) * lW) • ptAff x₃ y₃ (t₁ + t₂ - m / 2) := by
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

/-- The tangent slope `m = (12x² − g₂)/(2y)` (`= ℘''/℘'`). -/
def dblSlope (g₂ x y : K) : K := (12 * x ^ 2 - g₂) / (2 * y)

/-- `x(2P) = m²/4 − 2x`. -/
def dblX (g₂ x y : K) : K := dblSlope g₂ x y ^ 2 / 4 - 2 * x

/-- `y(2P) = −m (x(2P) − x) − y`. -/
def dblY (g₂ x y : K) : K := -dblSlope g₂ x y * (dblX g₂ x y - x) - y

variable {g₂ g₃ x y : K}

lemma dblSlope_mul (hy : y ≠ 0) : 2 * y * dblSlope g₂ x y = 12 * x ^ 2 - g₂ := by
  unfold dblSlope
  field_simp

lemma dblX_mul (hy : y ≠ 0) : 4 * (2 * y) ^ 2 * dblX g₂ x y = dblN3 g₂ x y := by
  have h := dblSlope_mul (g₂ := g₂) (x := x) hy
  unfold dblX dblN3
  rw [← h]
  ring

lemma dblY_mul (hy : y ≠ 0) : 8 * (2 * y) ^ 3 * dblY g₂ x y = dblY3 g₂ x y := by
  have h := dblSlope_mul (g₂ := g₂) (x := x) hy
  have h1 := dblX_mul (g₂ := g₂) (x := x) hy
  unfold dblY dblY3
  rw [← h1]
  linear_combination (-(8 : K) * (2 * y) ^ 2 * (dblX g₂ x y - x)) * h

/-- **Doubling**: `(P, t₁) + (P, t₂) = (2P, t₁ + t₂ − m/2)` for `y ≠ 0`. -/
theorem NLaw_dbl (hP : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃) (hy : y ≠ 0) (t₁ t₂ : K)
    (i j k : Fin 2) :
    NLaw g₂ g₃ i j k (ptAff x y t₁) (ptAff x y t₂) =
      NLaw g₂ g₃ i j k (ptAff x y t₁) (ptAff x y t₂) 2 •
        ptAff (dblX g₂ x y) (dblY g₂ x y) (t₁ + t₂ - dblSlope g₂ x y / 2) := by
  have hd : (2 : K) * y ≠ 0 := mul_ne_zero two_ne_zero hy
  have hm := dblSlope_mul (g₂ := g₂) (x := x) hy
  have hx3 := dblX_mul (g₂ := g₂) (x := x) hy
  have hy3 := dblY_mul (g₂ := g₂) (x := x) hy
  have hV := tcoord_ptAff_V x y t₁
  have hW := tcoord_ptAff_W x y t₁
  have hV' := tcoord_ptAff_V x y t₂
  have hW' := tcoord_ptAff_W x y t₂
  simp only [NLaw, Pe_ptAff']
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact shape_gen hd hm hx3 hy3 hV hV' (dblE1₁ hP) (dblE2₁ hP) (dblK1₁VV hP) (dblK3₁VV hP)
  · exact shape_gen hd hm hx3 hy3 hV hW' (dblE1₁ hP) (dblE2₁ hP) (dblK1₁VW hP) (dblK3₁VW hP)
  · exact shape_gen hd hm hx3 hy3 hW hV' (dblE1₁ hP) (dblE2₁ hP) (dblK1₁WV hP) (dblK3₁WV hP)
  · exact shape_gen hd hm hx3 hy3 hW hW' (dblE1₁ hP) (dblE2₁ hP) (dblK1₁WW hP) (dblK3₁WW hP)
  · exact shape_gen hd hm hx3 hy3 hV hV' (dblE1₂ hP) (dblE2₂ hP) (dblK1₂VV hP) (dblK3₂VV hP)
  · exact shape_gen hd hm hx3 hy3 hV hW' (dblE1₂ hP) (dblE2₂ hP) (dblK1₂VW hP) (dblK3₂VW hP)
  · exact shape_gen hd hm hx3 hy3 hW hV' (dblE1₂ hP) (dblE2₂ hP) (dblK1₂WV hP) (dblK3₂WV hP)
  · exact shape_gen hd hm hx3 hy3 hW hW' (dblE1₂ hP) (dblE2₂ hP) (dblK1₂WW hP) (dblK3₂WW hP)

end Doubling

/-! ### (b) analytically, in all cases -/

section Analytic

variable (L : PeriodPair)

lemma zeta_zero' : zeta L 0 = 0 := by
  have h := zeta_neg L 0
  rw [neg_zero] at h
  linear_combination h / 2

lemma zeta_of_mem' {l : ℂ} (hl : l ∈ L.lattice) : zeta L l = eta L l := by
  have h := zeta_add L hl 0
  rwa [zero_add, zeta_zero', zero_add] at h

lemma expN_of_mem {z : ℂ} (hz : z ∈ L.lattice) (w : ℂ) : expN L z w = ptO (w - zeta L z) := by
  simp [expN, hz]

/-- **(b) for all pairs** (analytic form): for all `(z₁, w₁), (z₂, w₂)`, every law maps
`(exp(z₁, w₁), exp(z₂, w₂))` to a scalar multiple of `exp(z₁ + z₂, w₁ + w₂)`. -/
theorem NLaw_expN_all (z₁ w₁ z₂ w₂ : ℂ) (i j k : Fin 2) :
    ∃ c : ℂ, NLaw L.g₂ L.g₃ i j k (expN L z₁ w₁) (expN L z₂ w₂) =
      c • expN L (z₁ + z₂) (w₁ + w₂) := by
  by_cases h₁ : z₁ ∈ L.lattice <;> by_cases h₂ : z₂ ∈ L.lattice
  · -- both over `O`
    have ht : w₁ - zeta L z₁ + (w₂ - zeta L z₂) = w₁ + w₂ - zeta L (z₁ + z₂) := by
      rw [zeta_add L h₂ z₁, zeta_of_mem' L h₂]; ring
    rw [expN_of_mem L h₁, expN_of_mem L h₂, expN_of_mem L (add_mem h₁ h₂), NLaw_ptO_ptO, ht]
    exact ⟨_, rfl⟩
  · -- `z₁ ∈ Λ`
    have hp : z₁ + z₂ ∉ L.lattice := fun h => h₂ (by simpa using sub_mem h h₁)
    have ht : w₂ - zeta L z₂ + (w₁ - zeta L z₁) = w₁ + w₂ - zeta L (z₂ + z₁) := by
      rw [zeta_add L h₁ z₂, zeta_of_mem' L h₁]; ring
    rw [expN_of_mem L h₁, expN_of_notMem L h₂, expN_of_notMem L hp,
      NLaw_ptO_left (L.derivWeierstrassP_sq z₂ h₂), add_comm z₁ z₂,
      weierstrassP_add_mem L z₂ h₁, derivWeierstrassP_add_mem L z₂ h₁, ht]
    exact ⟨_, rfl⟩
  · -- `z₂ ∈ Λ`
    have hp : z₁ + z₂ ∉ L.lattice := fun h => h₁ (by simpa using sub_mem h h₂)
    have ht : w₁ - zeta L z₁ + (w₂ - zeta L z₂) = w₁ + w₂ - zeta L (z₁ + z₂) := by
      rw [zeta_add L h₂ z₁, zeta_of_mem' L h₂]; ring
    rw [expN_of_notMem L h₁, expN_of_mem L h₂, expN_of_notMem L hp,
      NLaw_ptO_right (L.derivWeierstrassP_sq z₁ h₁), weierstrassP_add_mem L z₁ h₂,
      derivWeierstrassP_add_mem L z₁ h₂, ht]
    exact ⟨_, rfl⟩
  · by_cases hp : z₁ + z₂ ∈ L.lattice
    · -- opposite points
      have hz₂ : z₂ = -z₁ + (z₁ + z₂) := by ring
      have hP2 : ℘[L] z₂ = ℘[L] z₁ := by
        rw [hz₂, weierstrassP_add_mem L _ hp, L.weierstrassP_neg]
      have hD2 : ℘'[L] z₂ = -℘'[L] z₁ := by
        rw [hz₂, derivWeierstrassP_add_mem L _ hp, L.derivWeierstrassP_neg]
      have hZ2 : zeta L z₂ = -zeta L z₁ + zeta L (z₁ + z₂) := by
        rw [zeta_of_mem' L hp]
        conv_lhs => rw [hz₂]
        rw [zeta_add L hp, zeta_neg]
      have ht : w₁ - zeta L z₁ + (w₂ - zeta L z₂) = w₁ + w₂ - zeta L (z₁ + z₂) := by
        rw [hZ2]; ring
      rw [expN_of_notMem L h₁, expN_of_notMem L h₂, expN_of_mem L hp, hP2, hD2,
        NLaw_neg (L.derivWeierstrassP_sq z₁ h₁), ht]
      exact ⟨_, rfl⟩
    · exact ⟨_, NLaw_expN_of_add L h₁ h₂ hp w₁ w₂ i j k⟩

end Analytic

end LSG.Elliptic
