/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Elliptic.NaturalLawsPoly

/-!
# Identities for the special configurations of (b)

Values of the `E`-laws and of the fibre corrections `κ` at the special pairs
`(O, A)`, `(A, O)`, `(O, O)`, `(A, −A)`, `(A, A)` with `A = (x : y : 1)`, `−A = (x : −y : 1)`,
`O = (0 : 1 : 0)`, modulo `y² = 4x³ − g₂x − g₃`. Generated and checked by `gen_special.py` (sympy).
Used in `NaturalGroupFull`.
-/

namespace LSG.Elliptic

variable {R : Type*} [CommRing R] {g₂ g₃ x y : R} (hP : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃)

/-- `4(2y)² x₃` at the doubling point. -/
def dblN3 (g₂ x y : R) : R := (12 * x ^ 2 - g₂) ^ 2 - 8 * x * (2 * y) ^ 2

/-- `8(2y)³ y₃` at the doubling point. -/
def dblY3 (g₂ x y : R) : R :=
  -2 * (12 * x ^ 2 - g₂) * (dblN3 g₂ x y - 4 * (2 * y) ^ 2 * x) - 8 * (2 * y) ^ 3 * y

include hP in
theorem lawVal₁U_OA :
    law₁U g₂ g₃ 0 1 0 x y 1 =
      1 * x := by
  linear_combination (norm := (simp only [law₁U]; ring)) 0 * hP

include hP in
theorem lawVal₁V_OA :
    law₁V g₂ g₃ 0 1 0 x y 1 =
      1 * y := by
  linear_combination (norm := (simp only [law₁V]; ring)) 0 * hP

include hP in
theorem lawVal₁W_OA :
    law₁W g₂ g₃ 0 1 0 x y 1 =
      1 * 1 := by
  linear_combination (norm := (simp only [law₁W]; ring)) 0 * hP

include hP in
theorem lawVal₂U_OA :
    law₂U g₂ g₃ 0 1 0 x y 1 =
      (4 * y) * x := by
  linear_combination (norm := (simp only [law₂U]; ring)) 0 * hP

include hP in
theorem lawVal₂V_OA :
    law₂V g₂ g₃ 0 1 0 x y 1 =
      (4 * y) * y := by
  linear_combination (norm := (simp only [law₂V]; ring)) 0 * hP

include hP in
theorem lawVal₂W_OA :
    law₂W g₂ g₃ 0 1 0 x y 1 =
      (4 * y) * 1 := by
  linear_combination (norm := (simp only [law₂W]; ring)) 0 * hP

include hP in
theorem lawVal₁U_AO :
    law₁U g₂ g₃ x y 1 0 1 0 =
      (-1) * x := by
  linear_combination (norm := (simp only [law₁U]; ring)) 0 * hP

include hP in
theorem lawVal₁V_AO :
    law₁V g₂ g₃ x y 1 0 1 0 =
      (-1) * y := by
  linear_combination (norm := (simp only [law₁V]; ring)) 0 * hP

include hP in
theorem lawVal₁W_AO :
    law₁W g₂ g₃ x y 1 0 1 0 =
      (-1) * 1 := by
  linear_combination (norm := (simp only [law₁W]; ring)) 0 * hP

include hP in
theorem lawVal₂U_AO :
    law₂U g₂ g₃ x y 1 0 1 0 =
      (4 * y) * x := by
  linear_combination (norm := (simp only [law₂U]; ring)) 0 * hP

include hP in
theorem lawVal₂V_AO :
    law₂V g₂ g₃ x y 1 0 1 0 =
      (4 * y) * y := by
  linear_combination (norm := (simp only [law₂V]; ring)) 0 * hP

include hP in
theorem lawVal₂W_AO :
    law₂W g₂ g₃ x y 1 0 1 0 =
      (4 * y) * 1 := by
  linear_combination (norm := (simp only [law₂W]; ring)) 0 * hP

theorem lawVal₁U_OO (g₂ g₃ : R) :
    law₁U g₂ g₃ 0 1 0 0 1 0 =
      0 * 0 := by
  simp only [law₁U]
  ring

theorem lawVal₁V_OO (g₂ g₃ : R) :
    law₁V g₂ g₃ 0 1 0 0 1 0 =
      0 * 1 := by
  simp only [law₁V]
  ring

theorem lawVal₁W_OO (g₂ g₃ : R) :
    law₁W g₂ g₃ 0 1 0 0 1 0 =
      0 * 0 := by
  simp only [law₁W]
  ring

theorem lawVal₂U_OO (g₂ g₃ : R) :
    law₂U g₂ g₃ 0 1 0 0 1 0 =
      4 * 0 := by
  simp only [law₂U]
  ring

theorem lawVal₂V_OO (g₂ g₃ : R) :
    law₂V g₂ g₃ 0 1 0 0 1 0 =
      4 * 1 := by
  simp only [law₂V]
  ring

theorem lawVal₂W_OO (g₂ g₃ : R) :
    law₂W g₂ g₃ 0 1 0 0 1 0 =
      4 * 0 := by
  simp only [law₂W]
  ring

include hP in
theorem lawVal₁U_AAn :
    law₁U g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [law₁U]; ring)) 0 * hP

include hP in
theorem lawVal₁W_AAn :
    law₁W g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [law₁W]; ring)) 0 * hP

include hP in
theorem lawVal₂U_AAn :
    law₂U g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [law₂U]; ring)) 0 * hP

include hP in
theorem lawVal₂W_AAn :
    law₂W g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [law₂W]; ring)) 0 * hP

include hP in
theorem kapWVal₁VV_OA :
    kapW₁VV g₂ g₃ 0 1 0 x y 1 =
      1 * (-2 * 1 * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapW₁VV]; ring)) 0 * hP

include hP in
theorem kapVVal₁VV_OA :
    kapV₁VV g₂ g₃ 0 1 0 x y 1 =
      1 * (4 * y * 1 * x ^ 2 - 2 * 1 * y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₁VV]; ring)) 0 * hP

include hP in
theorem kapWVal₁VV_AO :
    kapW₁VV g₂ g₃ x y 1 0 1 0 =
      1 * (-2 * (-1) * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapW₁VV]; ring)) 0 * hP

include hP in
theorem kapVVal₁VV_AO :
    kapV₁VV g₂ g₃ x y 1 0 1 0 =
      1 * (4 * y * (-1) * x ^ 2 - 2 * (-1) * y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₁VV]; ring)) 0 * hP

theorem kapWVal₁VV_OO (g₂ g₃ : R) :
    kapW₁VV g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapW₁VV]
  ring

theorem kapVVal₁VV_OO (g₂ g₃ : R) :
    kapV₁VV g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapV₁VV]
  ring

include hP in
theorem kapWVal₁VV_AAn :
    kapW₁VV g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [kapW₁VV]; ring))
    (2*g₂*y) * hP

include hP in
theorem kapVVal₁VV_AAn :
    kapV₁VV g₂ g₃ x y 1 x (-y) 1 =
      -2 * law₁V g₂ g₃ x y 1 x (-y) 1 * ((-y) * (2 * x ^ 2) + y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₁VV, law₁V]; ring)) 0 * hP

include hP in
theorem kapWVal₁VW_OA :
    kapW₁VW g₂ g₃ 0 1 0 x y 1 =
      1 * (-2 * 1 * 0) := by
  linear_combination (norm := (simp only [kapW₁VW]; ring)) 0 * hP

include hP in
theorem kapVVal₁VW_OA :
    kapV₁VW g₂ g₃ 0 1 0 x y 1 =
      1 * (4 * 1 * 1 * x ^ 2 - 2 * 1 * y * 0) := by
  linear_combination (norm := (simp only [kapV₁VW]; ring)) 0 * hP

include hP in
theorem kapWVal₁VW_AO :
    kapW₁VW g₂ g₃ x y 1 0 1 0 =
      0 * (-2 * (-1) * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapW₁VW]; ring)) 0 * hP

include hP in
theorem kapVVal₁VW_AO :
    kapV₁VW g₂ g₃ x y 1 0 1 0 =
      0 * (4 * y * (-1) * x ^ 2 - 2 * (-1) * y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₁VW]; ring)) 0 * hP

theorem kapWVal₁VW_OO (g₂ g₃ : R) :
    kapW₁VW g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapW₁VW]
  ring

theorem kapVVal₁VW_OO (g₂ g₃ : R) :
    kapV₁VW g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapV₁VW]
  ring

include hP in
theorem kapWVal₁VW_AAn :
    kapW₁VW g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [kapW₁VW]; ring))
    (-g₂) * hP

include hP in
theorem kapVVal₁VW_AAn :
    kapV₁VW g₂ g₃ x y 1 x (-y) 1 =
      -2 * law₁V g₂ g₃ x y 1 x (-y) 1 * (1 * (2 * x ^ 2) + y * 0) := by
  linear_combination (norm := (simp only [kapV₁VW, law₁V]; ring))
    (-3*g₂*y + 24*x^2*y) * hP

include hP in
theorem kapWVal₁WV_OA :
    kapW₁WV g₂ g₃ 0 1 0 x y 1 =
      0 * (-2 * 1 * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapW₁WV]; ring)) 0 * hP

include hP in
theorem kapVVal₁WV_OA :
    kapV₁WV g₂ g₃ 0 1 0 x y 1 =
      0 * (4 * y * 1 * x ^ 2 - 2 * 1 * y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₁WV]; ring)) 0 * hP

include hP in
theorem kapWVal₁WV_AO :
    kapW₁WV g₂ g₃ x y 1 0 1 0 =
      1 * (-2 * (-1) * 0) := by
  linear_combination (norm := (simp only [kapW₁WV]; ring)) 0 * hP

include hP in
theorem kapVVal₁WV_AO :
    kapV₁WV g₂ g₃ x y 1 0 1 0 =
      1 * (4 * 1 * (-1) * x ^ 2 - 2 * (-1) * y * 0) := by
  linear_combination (norm := (simp only [kapV₁WV]; ring)) 0 * hP

theorem kapWVal₁WV_OO (g₂ g₃ : R) :
    kapW₁WV g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapW₁WV]
  ring

theorem kapVVal₁WV_OO (g₂ g₃ : R) :
    kapV₁WV g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapV₁WV]
  ring

include hP in
theorem kapWVal₁WV_AAn :
    kapW₁WV g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [kapW₁WV]; ring))
    (g₂) * hP

include hP in
theorem kapVVal₁WV_AAn :
    kapV₁WV g₂ g₃ x y 1 x (-y) 1 =
      -2 * law₁V g₂ g₃ x y 1 x (-y) 1 * ((-y) * 0 + 1 * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₁WV, law₁V]; ring))
    (-3*g₂*y + 24*x^2*y) * hP

include hP in
theorem kapWVal₁WW_OA :
    kapW₁WW g₂ g₃ 0 1 0 x y 1 =
      0 * (-2 * 1 * 0) := by
  linear_combination (norm := (simp only [kapW₁WW]; ring)) 0 * hP

include hP in
theorem kapVVal₁WW_OA :
    kapV₁WW g₂ g₃ 0 1 0 x y 1 =
      0 * (4 * 1 * 1 * x ^ 2 - 2 * 1 * y * 0) := by
  linear_combination (norm := (simp only [kapV₁WW]; ring)) 0 * hP

include hP in
theorem kapWVal₁WW_AO :
    kapW₁WW g₂ g₃ x y 1 0 1 0 =
      0 * (-2 * (-1) * 0) := by
  linear_combination (norm := (simp only [kapW₁WW]; ring)) 0 * hP

include hP in
theorem kapVVal₁WW_AO :
    kapV₁WW g₂ g₃ x y 1 0 1 0 =
      0 * (4 * 1 * (-1) * x ^ 2 - 2 * (-1) * y * 0) := by
  linear_combination (norm := (simp only [kapV₁WW]; ring)) 0 * hP

theorem kapWVal₁WW_OO (g₂ g₃ : R) :
    kapW₁WW g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapW₁WW]
  ring

theorem kapVVal₁WW_OO (g₂ g₃ : R) :
    kapV₁WW g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapV₁WW]
  ring

include hP in
theorem kapWVal₁WW_AAn :
    kapW₁WW g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [kapW₁WW]; ring)) 0 * hP

include hP in
theorem kapVVal₁WW_AAn :
    kapV₁WW g₂ g₃ x y 1 x (-y) 1 =
      -2 * law₁V g₂ g₃ x y 1 x (-y) 1 * (1 * 0 + 1 * 0) := by
  linear_combination (norm := (simp only [kapV₁WW, law₁V]; ring)) 0 * hP

include hP in
theorem kapWVal₂VV_OA :
    kapW₂VV g₂ g₃ 0 1 0 x y 1 =
      1 * (-2 * (4 * y) * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapW₂VV]; ring)) 0 * hP

include hP in
theorem kapVVal₂VV_OA :
    kapV₂VV g₂ g₃ 0 1 0 x y 1 =
      1 * (4 * y * (4 * y) * x ^ 2 - 2 * (4 * y) * y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₂VV]; ring)) 0 * hP

include hP in
theorem kapWVal₂VV_AO :
    kapW₂VV g₂ g₃ x y 1 0 1 0 =
      1 * (-2 * (4 * y) * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapW₂VV]; ring)) 0 * hP

include hP in
theorem kapVVal₂VV_AO :
    kapV₂VV g₂ g₃ x y 1 0 1 0 =
      1 * (4 * y * (4 * y) * x ^ 2 - 2 * (4 * y) * y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₂VV]; ring)) 0 * hP

theorem kapWVal₂VV_OO (g₂ g₃ : R) :
    kapW₂VV g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapW₂VV]
  ring

theorem kapVVal₂VV_OO (g₂ g₃ : R) :
    kapV₂VV g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapV₂VV]
  ring

include hP in
theorem kapWVal₂VV_AAn :
    kapW₂VV g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [kapW₂VV]; ring))
    (8*g₂*y^2) * hP

include hP in
theorem kapVVal₂VV_AAn :
    kapV₂VV g₂ g₃ x y 1 x (-y) 1 =
      -2 * law₂V g₂ g₃ x y 1 x (-y) 1 * ((-y) * (2 * x ^ 2) + y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₂VV, law₂V]; ring)) 0 * hP

include hP in
theorem kapWVal₂VW_OA :
    kapW₂VW g₂ g₃ 0 1 0 x y 1 =
      1 * (-2 * (4 * y) * 0) := by
  linear_combination (norm := (simp only [kapW₂VW]; ring)) 0 * hP

include hP in
theorem kapVVal₂VW_OA :
    kapV₂VW g₂ g₃ 0 1 0 x y 1 =
      1 * (4 * 1 * (4 * y) * x ^ 2 - 2 * (4 * y) * y * 0) := by
  linear_combination (norm := (simp only [kapV₂VW]; ring)) 0 * hP

include hP in
theorem kapWVal₂VW_AO :
    kapW₂VW g₂ g₃ x y 1 0 1 0 =
      0 * (-2 * (4 * y) * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapW₂VW]; ring)) 0 * hP

include hP in
theorem kapVVal₂VW_AO :
    kapV₂VW g₂ g₃ x y 1 0 1 0 =
      0 * (4 * y * (4 * y) * x ^ 2 - 2 * (4 * y) * y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₂VW]; ring)) 0 * hP

theorem kapWVal₂VW_OO (g₂ g₃ : R) :
    kapW₂VW g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapW₂VW]
  ring

theorem kapVVal₂VW_OO (g₂ g₃ : R) :
    kapV₂VW g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapV₂VW]
  ring

include hP in
theorem kapWVal₂VW_AAn :
    kapW₂VW g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [kapW₂VW]; ring))
    (-4*g₂*y) * hP

include hP in
theorem kapVVal₂VW_AAn :
    kapV₂VW g₂ g₃ x y 1 x (-y) 1 =
      -2 * law₂V g₂ g₃ x y 1 x (-y) 1 * (1 * (2 * x ^ 2) + y * 0) := by
  linear_combination (norm := (simp only [kapV₂VW, law₂V]; ring))
    (20*g₂^2*x + 12*g₂*g₃ + 48*g₂*x^3 + 288*g₃*x^2) * hP

include hP in
theorem kapWVal₂WV_OA :
    kapW₂WV g₂ g₃ 0 1 0 x y 1 =
      0 * (-2 * (4 * y) * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapW₂WV]; ring)) 0 * hP

include hP in
theorem kapVVal₂WV_OA :
    kapV₂WV g₂ g₃ 0 1 0 x y 1 =
      0 * (4 * y * (4 * y) * x ^ 2 - 2 * (4 * y) * y * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₂WV]; ring)) 0 * hP

include hP in
theorem kapWVal₂WV_AO :
    kapW₂WV g₂ g₃ x y 1 0 1 0 =
      1 * (-2 * (4 * y) * 0) := by
  linear_combination (norm := (simp only [kapW₂WV]; ring)) 0 * hP

include hP in
theorem kapVVal₂WV_AO :
    kapV₂WV g₂ g₃ x y 1 0 1 0 =
      1 * (4 * 1 * (4 * y) * x ^ 2 - 2 * (4 * y) * y * 0) := by
  linear_combination (norm := (simp only [kapV₂WV]; ring)) 0 * hP

theorem kapWVal₂WV_OO (g₂ g₃ : R) :
    kapW₂WV g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapW₂WV]
  ring

theorem kapVVal₂WV_OO (g₂ g₃ : R) :
    kapV₂WV g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapV₂WV]
  ring

include hP in
theorem kapWVal₂WV_AAn :
    kapW₂WV g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [kapW₂WV]; ring))
    (4*g₂*y) * hP

include hP in
theorem kapVVal₂WV_AAn :
    kapV₂WV g₂ g₃ x y 1 x (-y) 1 =
      -2 * law₂V g₂ g₃ x y 1 x (-y) 1 * ((-y) * 0 + 1 * (2 * x ^ 2)) := by
  linear_combination (norm := (simp only [kapV₂WV, law₂V]; ring))
    (20*g₂^2*x + 12*g₂*g₃ + 48*g₂*x^3 + 288*g₃*x^2) * hP

include hP in
theorem kapWVal₂WW_OA :
    kapW₂WW g₂ g₃ 0 1 0 x y 1 =
      0 * (-2 * (4 * y) * 0) := by
  linear_combination (norm := (simp only [kapW₂WW]; ring)) 0 * hP

include hP in
theorem kapVVal₂WW_OA :
    kapV₂WW g₂ g₃ 0 1 0 x y 1 =
      0 * (4 * 1 * (4 * y) * x ^ 2 - 2 * (4 * y) * y * 0) := by
  linear_combination (norm := (simp only [kapV₂WW]; ring)) 0 * hP

include hP in
theorem kapWVal₂WW_AO :
    kapW₂WW g₂ g₃ x y 1 0 1 0 =
      0 * (-2 * (4 * y) * 0) := by
  linear_combination (norm := (simp only [kapW₂WW]; ring)) 0 * hP

include hP in
theorem kapVVal₂WW_AO :
    kapV₂WW g₂ g₃ x y 1 0 1 0 =
      0 * (4 * 1 * (4 * y) * x ^ 2 - 2 * (4 * y) * y * 0) := by
  linear_combination (norm := (simp only [kapV₂WW]; ring)) 0 * hP

theorem kapWVal₂WW_OO (g₂ g₃ : R) :
    kapW₂WW g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapW₂WW]
  ring

theorem kapVVal₂WW_OO (g₂ g₃ : R) :
    kapV₂WW g₂ g₃ 0 1 0 0 1 0 =
      0 := by
  simp only [kapV₂WW]
  ring

include hP in
theorem kapWVal₂WW_AAn :
    kapW₂WW g₂ g₃ x y 1 x (-y) 1 =
      0 := by
  linear_combination (norm := (simp only [kapW₂WW]; ring)) 0 * hP

include hP in
theorem kapVVal₂WW_AAn :
    kapV₂WW g₂ g₃ x y 1 x (-y) 1 =
      -2 * law₂V g₂ g₃ x y 1 x (-y) 1 * (1 * 0 + 1 * 0) := by
  linear_combination (norm := (simp only [kapV₂WW, law₂V]; ring)) 0 * hP

include hP in
theorem dblE1₁ :
    4 * (2 * y) ^ 2 * law₁U g₂ g₃ x y 1 x y 1 =
      law₁W g₂ g₃ x y 1 x y 1 * dblN3 g₂ x y := by
  linear_combination (norm := (simp only [law₁U, law₁W, dblN3]; ring)) 0 * hP

include hP in
theorem dblE2₁ :
    8 * (2 * y) ^ 3 * law₁V g₂ g₃ x y 1 x y 1 =
      law₁W g₂ g₃ x y 1 x y 1 * dblY3 g₂ x y := by
  linear_combination (norm := (simp only [law₁V, law₁W, dblY3, dblN3]; ring)) 0 * hP

include hP in
theorem dblE1₂ :
    4 * (2 * y) ^ 2 * law₂U g₂ g₃ x y 1 x y 1 =
      law₂W g₂ g₃ x y 1 x y 1 * dblN3 g₂ x y := by
  linear_combination (norm := (simp only [law₂U, law₂W, dblN3]; ring))
    (24*g₂^2*y - 576*g₂*x^2*y + 3456*x^4*y + 384*x*y^3) * hP

include hP in
theorem dblE2₂ :
    8 * (2 * y) ^ 3 * law₂V g₂ g₃ x y 1 x y 1 =
      law₂W g₂ g₃ x y 1 x y 1 * dblY3 g₂ x y := by
  linear_combination (norm := (simp only [law₂V, law₂W, dblY3, dblN3]; ring))
    (48*g₂^3*y - 1728*g₂^2*x^2*y + 20736*g₂*x^4*y - 1536*g₂*x*y^3 - 2304*g₃*y^3
      - 82944*x^6*y + 768*y^5) * hP

include hP in
theorem dblK1₁VV :
    (2 * y) *
      (kapW₁VV g₂ g₃ x y 1 x y 1 + 2 * y * law₁W g₂ g₃ x y 1 x y 1 * (2 * x ^ 2) +
        2 * y * law₁W g₂ g₃ x y 1 x y 1 * (2 * x ^ 2)) =
      y * y * law₁W g₂ g₃ x y 1 x y 1 * (12 * x ^ 2 - g₂) := by
  linear_combination (norm := (simp only [kapW₁VV, law₁W]; ring)) 0 * hP

include hP in
theorem dblK3₁VV :
    16 * (2 * y) ^ 4 *
      (kapV₁VV g₂ g₃ x y 1 x y 1 + 2 * y * law₁V g₂ g₃ x y 1 x y 1 * (2 * x ^ 2) +
        2 * y * law₁V g₂ g₃ x y 1 x y 1 * (2 * x ^ 2)) =
      y * y * law₁W g₂ g₃ x y 1 x y 1 *
        (2 * dblY3 g₂ x y * (12 * x ^ 2 - g₂) + 4 * dblN3 g₂ x y ^ 2) := by
  linear_combination (norm := (simp only [kapV₁VV, law₁V, law₁W, dblY3, dblN3]; ring)) 0 * hP

include hP in
theorem dblK1₁VW :
    (2 * y) *
      (kapW₁VW g₂ g₃ x y 1 x y 1 + 2 * 1 * law₁W g₂ g₃ x y 1 x y 1 * (2 * x ^ 2) +
        2 * y * law₁W g₂ g₃ x y 1 x y 1 * 0) =
      y * 1 * law₁W g₂ g₃ x y 1 x y 1 * (12 * x ^ 2 - g₂) := by
  linear_combination (norm := (simp only [kapW₁VW, law₁W]; ring))
    (-2*g₂*y) * hP

include hP in
theorem dblK3₁VW :
    16 * (2 * y) ^ 4 *
      (kapV₁VW g₂ g₃ x y 1 x y 1 + 2 * 1 * law₁V g₂ g₃ x y 1 x y 1 * (2 * x ^ 2) +
        2 * y * law₁V g₂ g₃ x y 1 x y 1 * 0) =
      y * 1 * law₁W g₂ g₃ x y 1 x y 1 *
        (2 * dblY3 g₂ x y * (12 * x ^ 2 - g₂) + 4 * dblN3 g₂ x y ^ 2) := by
  linear_combination (norm := (simp only [kapV₁VW, law₁V, law₁W, dblY3, dblN3]; ring))
    (256*g₂*y^5) * hP

include hP in
theorem dblK1₁WV :
    (2 * y) *
      (kapW₁WV g₂ g₃ x y 1 x y 1 + 2 * y * law₁W g₂ g₃ x y 1 x y 1 * 0 +
        2 * 1 * law₁W g₂ g₃ x y 1 x y 1 * (2 * x ^ 2)) =
      1 * y * law₁W g₂ g₃ x y 1 x y 1 * (12 * x ^ 2 - g₂) := by
  linear_combination (norm := (simp only [kapW₁WV, law₁W]; ring))
    (2*g₂*y) * hP

include hP in
theorem dblK3₁WV :
    16 * (2 * y) ^ 4 *
      (kapV₁WV g₂ g₃ x y 1 x y 1 + 2 * y * law₁V g₂ g₃ x y 1 x y 1 * 0 +
        2 * 1 * law₁V g₂ g₃ x y 1 x y 1 * (2 * x ^ 2)) =
      1 * y * law₁W g₂ g₃ x y 1 x y 1 *
        (2 * dblY3 g₂ x y * (12 * x ^ 2 - g₂) + 4 * dblN3 g₂ x y ^ 2) := by
  linear_combination (norm := (simp only [kapV₁WV, law₁V, law₁W, dblY3, dblN3]; ring))
    (-256*g₂*y^5) * hP

include hP in
theorem dblK1₁WW :
    (2 * y) *
      (kapW₁WW g₂ g₃ x y 1 x y 1 + 2 * 1 * law₁W g₂ g₃ x y 1 x y 1 * 0 +
        2 * 1 * law₁W g₂ g₃ x y 1 x y 1 * 0) =
      1 * 1 * law₁W g₂ g₃ x y 1 x y 1 * (12 * x ^ 2 - g₂) := by
  linear_combination (norm := (simp only [kapW₁WW, law₁W]; ring)) 0 * hP

include hP in
theorem dblK3₁WW :
    16 * (2 * y) ^ 4 *
      (kapV₁WW g₂ g₃ x y 1 x y 1 + 2 * 1 * law₁V g₂ g₃ x y 1 x y 1 * 0 +
        2 * 1 * law₁V g₂ g₃ x y 1 x y 1 * 0) =
      1 * 1 * law₁W g₂ g₃ x y 1 x y 1 *
        (2 * dblY3 g₂ x y * (12 * x ^ 2 - g₂) + 4 * dblN3 g₂ x y ^ 2) := by
  linear_combination (norm := (simp only [kapV₁WW, law₁V, law₁W, dblY3, dblN3]; ring)) 0 * hP

include hP in
theorem dblK1₂VV :
    (2 * y) *
      (kapW₂VV g₂ g₃ x y 1 x y 1 + 2 * y * law₂W g₂ g₃ x y 1 x y 1 * (2 * x ^ 2) +
        2 * y * law₂W g₂ g₃ x y 1 x y 1 * (2 * x ^ 2)) =
      y * y * law₂W g₂ g₃ x y 1 x y 1 * (12 * x ^ 2 - g₂) := by
  linear_combination (norm := (simp only [kapW₂VV, law₂W]; ring))
    (24*g₂*y^3 - 96*x^2*y^3) * hP

include hP in
theorem dblK3₂VV :
    16 * (2 * y) ^ 4 *
      (kapV₂VV g₂ g₃ x y 1 x y 1 + 2 * y * law₂V g₂ g₃ x y 1 x y 1 * (2 * x ^ 2) +
        2 * y * law₂V g₂ g₃ x y 1 x y 1 * (2 * x ^ 2)) =
      y * y * law₂W g₂ g₃ x y 1 x y 1 *
        (2 * dblY3 g₂ x y * (12 * x ^ 2 - g₂) + 4 * dblN3 g₂ x y ^ 2) := by
  linear_combination (norm := (simp only [kapV₂VV, law₂V, law₂W, dblY3, dblN3]; ring))
    (8704*g₂^2*x*y^5 + 6144*g₂*g₃*y^5 + 61440*g₂*x^3*y^5 - 1024*g₂*y^7 + 147456*g₃*x^2*y^5
      - 221184*x^5*y^5 - 12288*x^2*y^7) * hP

include hP in
theorem dblK1₂VW :
    (2 * y) *
      (kapW₂VW g₂ g₃ x y 1 x y 1 + 2 * 1 * law₂W g₂ g₃ x y 1 x y 1 * (2 * x ^ 2) +
        2 * y * law₂W g₂ g₃ x y 1 x y 1 * 0) =
      y * 1 * law₂W g₂ g₃ x y 1 x y 1 * (12 * x ^ 2 - g₂) := by
  linear_combination (norm := (simp only [kapW₂VW, law₂W]; ring))
    (96*x^2*y^2) * hP

include hP in
theorem dblK3₂VW :
    16 * (2 * y) ^ 4 *
      (kapV₂VW g₂ g₃ x y 1 x y 1 + 2 * 1 * law₂V g₂ g₃ x y 1 x y 1 * (2 * x ^ 2) +
        2 * y * law₂V g₂ g₃ x y 1 x y 1 * 0) =
      y * 1 * law₂W g₂ g₃ x y 1 x y 1 *
        (2 * dblY3 g₂ x y * (12 * x ^ 2 - g₂) + 4 * dblN3 g₂ x y ^ 2) := by
  linear_combination (norm := (simp only [kapV₂VW, law₂V, law₂W, dblY3, dblN3]; ring))
    (3584*g₂^2*x*y^4 + 3072*g₂*g₃*y^4 + 49152*g₂*x^3*y^4 - 1024*g₂*y^6 + 73728*g₃*x^2*y^4
      - 221184*x^5*y^4 - 12288*x^2*y^6) * hP

include hP in
theorem dblK1₂WV :
    (2 * y) *
      (kapW₂WV g₂ g₃ x y 1 x y 1 + 2 * y * law₂W g₂ g₃ x y 1 x y 1 * 0 +
        2 * 1 * law₂W g₂ g₃ x y 1 x y 1 * (2 * x ^ 2)) =
      1 * y * law₂W g₂ g₃ x y 1 x y 1 * (12 * x ^ 2 - g₂) := by
  linear_combination (norm := (simp only [kapW₂WV, law₂W]; ring))
    (96*x^2*y^2) * hP

include hP in
theorem dblK3₂WV :
    16 * (2 * y) ^ 4 *
      (kapV₂WV g₂ g₃ x y 1 x y 1 + 2 * y * law₂V g₂ g₃ x y 1 x y 1 * 0 +
        2 * 1 * law₂V g₂ g₃ x y 1 x y 1 * (2 * x ^ 2)) =
      1 * y * law₂W g₂ g₃ x y 1 x y 1 *
        (2 * dblY3 g₂ x y * (12 * x ^ 2 - g₂) + 4 * dblN3 g₂ x y ^ 2) := by
  linear_combination (norm := (simp only [kapV₂WV, law₂V, law₂W, dblY3, dblN3]; ring))
    (3584*g₂^2*x*y^4 + 3072*g₂*g₃*y^4 + 49152*g₂*x^3*y^4 - 1024*g₂*y^6 + 73728*g₃*x^2*y^4
      - 221184*x^5*y^4 - 12288*x^2*y^6) * hP

include hP in
theorem dblK1₂WW :
    (2 * y) *
      (kapW₂WW g₂ g₃ x y 1 x y 1 + 2 * 1 * law₂W g₂ g₃ x y 1 x y 1 * 0 +
        2 * 1 * law₂W g₂ g₃ x y 1 x y 1 * 0) =
      1 * 1 * law₂W g₂ g₃ x y 1 x y 1 * (12 * x ^ 2 - g₂) := by
  linear_combination (norm := (simp only [kapW₂WW, law₂W]; ring))
    (-24*g₂*y + 288*x^2*y) * hP

include hP in
theorem dblK3₂WW :
    16 * (2 * y) ^ 4 *
      (kapV₂WW g₂ g₃ x y 1 x y 1 + 2 * 1 * law₂V g₂ g₃ x y 1 x y 1 * 0 +
        2 * 1 * law₂V g₂ g₃ x y 1 x y 1 * 0) =
      1 * 1 * law₂W g₂ g₃ x y 1 x y 1 *
        (2 * dblY3 g₂ x y * (12 * x ^ 2 - g₂) + 4 * dblN3 g₂ x y ^ 2) := by
  linear_combination (norm := (simp only [kapV₂WW, law₂V, law₂W, dblY3, dblN3]; ring))
    (-1536*g₂^2*x*y^3 + 36864*g₂*x^3*y^3 - 1024*g₂*y^5 - 221184*x^5*y^3 - 12288*x^2*y^5) * hP

end LSG.Elliptic
