/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.A1Facts

/-!
# M2.2 (N1, algebra): the eight Lemma-K♮ quadric identities

For `k ∈ {4, 8}` and `i, j ∈ Fin 2` (A1's `1, 2`), with `m(i, j) = i + j + 1` (`℘₁₁ = X₁/X₀`, `℘₁₂ = X₂/X₀`,
`℘₂₂ = X₃/X₀`), the degree-4 form

  `kP k i j X = −X_k · DW_j(X)[W_i(X)]_k + W_i(X)_k W_j(X)_k + 3 X_m X₀ X_k² − X₀² Q_{k,ij}(X)`

(`W = flowW`, `DW_j(X)[Y] = W_j(X + Y) − W_j(X) − W_j(Y)`) lies in the ideal of the nine quadrics `quadA`
(the quadrics `Q_{k,ij}` are those of the spike `scripts/m2_spike/kleinK.*`, M2.md §2.2 N1). The ideal-membership
coefficients were found by exact linear algebra (sympy) and are checked here by `linear_combination`, so no
certificate is needed. `kQ 0 i j X = 3 X_m X₀` is the chart-0 term.
-/

noncomputable section

namespace LSG.JacAnV

open LSG.JacAn

/-- `m(i, j)`: the index of `℘_ij = X_m / X₀`. -/
def mIdx (i j : Fin 2) : Fin 9 := ![![1, 2], ![2, 3]] i j

/-- The chart quadrics `Q_{c,ij}` for `c ∈ {0, 4, 8}` (`Q_{0,ij} = 3 X_m X₀`). -/
def kQ (k : Fin 9) (i j : Fin 2) (X : P9) : ℂ :=
  if k = 0 then 3 * X (mIdx i j) * X 0
  else if k = 4 then
    ![![-(9/4) * X 0 * X 2 - (9/2) * X 1 * X 8 + (9/2) * X 3 ^ 2 + (3/4) * X 4 * X 6,
        3 * X 0 * X 3 + 3 * X 1 ^ 2 - (9/2) * X 2 * X 8 - (3/4) * X 4 * X 7],
      ![3 * X 0 * X 3 + 3 * X 1 ^ 2 - (9/2) * X 2 * X 8 - (3/4) * X 4 * X 7,
        X 0 ^ 2 - 3 * X 1 * X 2 + (9/2) * X 3 * X 8 + (9/4) * X 5 * X 7]] i j
  else
    ![![9 * X 1 ^ 2 + (9/2) * X 2 * X 8 + (9/4) * X 4 * X 7, 3 * X 1 * X 2 - (3/2) * X 5 * X 7],
      ![3 * X 1 * X 2 - (3/2) * X 5 * X 7,
        -(1/2) * X 0 * X 8 + 6 * X 1 * X 3 + X 4 ^ 2 + (3/4) * X 6 * X 7]] i j

/-- The degree-4 form of Lemma K♮ in chart `k`. -/
def kP (k : Fin 9) (i j : Fin 2) (X : P9) : ℂ :=
  -X k * (flowW j (X + flowW i X) k - flowW j X k - flowW j (flowW i X) k) + flowW i X k * flowW j X k +
    3 * X (mIdx i j) * X 0 * X k ^ 2 - X 0 ^ 2 * kQ k i j X

lemma kQ_smul (k : Fin 9) (i j : Fin 2) (a : ℂ) (X : P9) : kQ k i j (a • X) = a ^ 2 * kQ k i j X := by
  unfold kQ
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [mIdx] <;> ring

lemma kP_4_0_0 (X : P9) (hq : ∀ r, quadA X r = 0) : kP 4 0 0 X = 0 := by
  have q0 := hq 0; have q1 := hq 1; have q2 := hq 2; have q3 := hq 3; have q4 := hq 4
  have q5 := hq 5; have q6 := hq 6; have q7 := hq 7; have q8 := hq 8
  simp only [quadA, Matrix.cons_val] at q0 q1 q2 q3 q4 q5 q6 q7 q8
  simp only [kP, kQ, mIdx, flowW, Matrix.cons_val, Pi.add_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination ((72/5)*X 0*X 1 + (9)*X 4*X 5 + (36/5)*X 8^2) * q0 + ((9/2)*X 1*X 6 + (-9/2)*X 2*X 5 + (9/5)*X 7*X 8) * q1 + ((63/20)*X 0*X 7 + (-9)*X 1*X 5 + (-9/5)*X 6*X 8) * q2 + ((-9/5)*X 0*X 6 + (9)*X 1*X 4) * q3 + ((9/20)*X 0*X 5 + (9/5)*X 4*X 8) * q4 + ((-9/20)*X 0^2) * q5 + ((63/20)*X 0*X 3 + (-9)*X 1^2 + (9/5)*X 2*X 8) * q6 + ((-9/5)*X 0*X 2 + (-18/5)*X 1*X 8) * q7 + ((9/5)*X 0*X 8) * q8

lemma kP_4_0_1 (X : P9) (hq : ∀ r, quadA X r = 0) : kP 4 0 1 X = 0 := by
  have q0 := hq 0; have q1 := hq 1; have q2 := hq 2; have q3 := hq 3; have q4 := hq 4
  have q5 := hq 5; have q6 := hq 6; have q7 := hq 7; have q8 := hq 8
  simp only [quadA, Matrix.cons_val] at q0 q1 q2 q3 q4 q5 q6 q7 q8
  simp only [kP, kQ, mIdx, flowW, Matrix.cons_val, Pi.add_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination ((-36/5)*X 1*X 8 + (-9/10)*X 4*X 6 + (9/10)*X 5^2) * q0 + ((-3/2)*X 0*X 4 + (-9/4)*X 1*X 7 + (9/20)*X 2*X 6 + (9/20)*X 3*X 5) * q1 + ((9/5)*X 1*X 6 + (-9/10)*X 2*X 5) * q2 + ((-9/10)*X 0*X 7 + (9/10)*X 1*X 5) * q3 + ((27/20)*X 0*X 6 + (-27/10)*X 1*X 4) * q4 + ((9/10)*X 0*X 8) * q5 + ((-27/20)*X 0^2 + (-9/5)*X 1*X 2) * q6 + ((-27/20)*X 0*X 3 + (18/5)*X 1^2) * q7 + ((-27/20)*X 0*X 1) * q8

lemma kP_4_1_0 (X : P9) (hq : ∀ r, quadA X r = 0) : kP 4 1 0 X = 0 := by
  have q0 := hq 0; have q1 := hq 1; have q2 := hq 2; have q3 := hq 3; have q4 := hq 4
  have q5 := hq 5; have q6 := hq 6; have q7 := hq 7; have q8 := hq 8
  simp only [quadA, Matrix.cons_val] at q0 q1 q2 q3 q4 q5 q6 q7 q8
  simp only [kP, kQ, mIdx, flowW, Matrix.cons_val, Pi.add_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination ((-36/5)*X 1*X 8 + (-9/10)*X 4*X 6 + (9/10)*X 5^2) * q0 + ((3/2)*X 0*X 4 + (-9/4)*X 1*X 7 + (9/20)*X 2*X 6 + (9/20)*X 3*X 5) * q1 + ((9/5)*X 1*X 6 + (-9/10)*X 2*X 5) * q2 + ((-9/10)*X 0*X 7 + (9/10)*X 1*X 5) * q3 + ((27/20)*X 0*X 6 + (-27/10)*X 1*X 4) * q4 + ((9/10)*X 0*X 8) * q5 + ((-27/20)*X 0^2 + (-9/5)*X 1*X 2) * q6 + ((-27/20)*X 0*X 3 + (18/5)*X 1^2) * q7 + ((-27/20)*X 0*X 1) * q8

lemma kP_4_1_1 (X : P9) (hq : ∀ r, quadA X r = 0) : kP 4 1 1 X = 0 := by
  have q0 := hq 0; have q1 := hq 1; have q2 := hq 2; have q3 := hq 3; have q4 := hq 4
  have q5 := hq 5; have q6 := hq 6; have q7 := hq 7; have q8 := hq 8
  simp only [quadA, Matrix.cons_val] at q0 q1 q2 q3 q4 q5 q6 q7 q8
  simp only [kP, kQ, mIdx, flowW, Matrix.cons_val, Pi.add_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination ((18/5)*X 0*X 3 + (36/5)*X 1^2 + (9/10)*X 4*X 7 + (-9/10)*X 5*X 6) * q0 + ((-27/10)*X 0*X 5 + (-9/20)*X 2*X 7 + (-9/20)*X 3*X 6) * q1 + ((3)*X 0*X 4 + (-9/10)*X 1*X 7 + (9/10)*X 2*X 6) * q2 + ((9/5)*X 1*X 6) * q3 + ((9/20)*X 0*X 7 + (-18/5)*X 1*X 5) * q4 + ((-9/5)*X 0*X 1) * q5 + ((-9/10)*X 0*X 8 + (-9/5)*X 1*X 3) * q6 + ((18/5)*X 1*X 2) * q7 + ((-9/10)*X 0*X 2) * q8

lemma kP_8_0_0 (X : P9) (hq : ∀ r, quadA X r = 0) : kP 8 0 0 X = 0 := by
  have q0 := hq 0; have q1 := hq 1; have q2 := hq 2; have q3 := hq 3; have q4 := hq 4
  have q5 := hq 5; have q6 := hq 6; have q7 := hq 7; have q8 := hq 8
  simp only [quadA, Matrix.cons_val] at q0 q1 q2 q3 q4 q5 q6 q7 q8
  simp only [kP, kQ, mIdx, flowW, Matrix.cons_val, Pi.add_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination ((-18)*X 1*X 8 + (-27/10)*X 4*X 6 + (27/10)*X 5^2) * q0 + ((9/10)*X 1*X 7 + (27/20)*X 2*X 6 + (-63/20)*X 3*X 5) * q1 + ((-9/2)*X 1*X 6 + (63/10)*X 2*X 5) * q2 + ((9/5)*X 0*X 7 + (-9/5)*X 1*X 5) * q3 + ((-9/20)*X 0*X 6 + (9/5)*X 1*X 4) * q4 + ((-3/10)*X 0*X 8) * q5 + ((9/20)*X 0^2) * q6 + ((9/20)*X 0*X 3) * q7 + ((-9/10)*X 0*X 1) * q8

lemma kP_8_0_1 (X : P9) (hq : ∀ r, quadA X r = 0) : kP 8 0 1 X = 0 := by
  have q0 := hq 0; have q1 := hq 1; have q2 := hq 2; have q3 := hq 3; have q4 := hq 4
  have q5 := hq 5; have q6 := hq 6; have q7 := hq 7; have q8 := hq 8
  simp only [quadA, Matrix.cons_val] at q0 q1 q2 q3 q4 q5 q6 q7 q8
  simp only [kP, kQ, mIdx, flowW, Matrix.cons_val, Pi.add_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination ((9/5)*X 0*X 3 + (-9/5)*X 4*X 7 + (9/5)*X 5*X 6) * q0 + ((3/20)*X 0*X 5 + (9/10)*X 2*X 7 + (-27/20)*X 3*X 6) * q1 + ((-9/5)*X 1*X 7 + (27/10)*X 2*X 6) * q2 + ((-9/10)*X 1*X 6) * q3 + ((27/20)*X 0*X 7 + (9/10)*X 1*X 5) * q4 + ((-3/5)*X 0*X 1) * q5 + ((3/10)*X 0*X 8) * q6 + ((-9/20)*X 0*X 2) * q8

lemma kP_8_1_0 (X : P9) (hq : ∀ r, quadA X r = 0) : kP 8 1 0 X = 0 := by
  have q0 := hq 0; have q1 := hq 1; have q2 := hq 2; have q3 := hq 3; have q4 := hq 4
  have q5 := hq 5; have q6 := hq 6; have q7 := hq 7; have q8 := hq 8
  simp only [quadA, Matrix.cons_val] at q0 q1 q2 q3 q4 q5 q6 q7 q8
  simp only [kP, kQ, mIdx, flowW, Matrix.cons_val, Pi.add_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination ((9/5)*X 0*X 3 + (-9/5)*X 4*X 7 + (9/5)*X 5*X 6) * q0 + ((3/20)*X 0*X 5 + (9/10)*X 2*X 7 + (-27/20)*X 3*X 6) * q1 + ((-9/5)*X 1*X 7 + (27/10)*X 2*X 6) * q2 + ((-9/10)*X 1*X 6) * q3 + ((27/20)*X 0*X 7 + (9/10)*X 1*X 5) * q4 + ((-3/5)*X 0*X 1) * q5 + ((9/5)*X 0*X 8) * q6 + ((-9/20)*X 0*X 2) * q8

lemma kP_8_1_1 (X : P9) (hq : ∀ r, quadA X r = 0) : kP 8 1 1 X = 0 := by
  have q0 := hq 0; have q1 := hq 1; have q2 := hq 2; have q3 := hq 3; have q4 := hq 4
  have q5 := hq 5; have q6 := hq 6; have q7 := hq 7; have q8 := hq 8
  simp only [quadA, Matrix.cons_val] at q0 q1 q2 q3 q4 q5 q6 q7 q8
  simp only [kP, kQ, mIdx, flowW, Matrix.cons_val, Pi.add_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  linear_combination ((-6/5)*X 0^2 + (-9)*X 3*X 8 + (-27/10)*X 5*X 7 + (27/10)*X 6^2) * q0 + ((-3/4)*X 0*X 6 + (-9/10)*X 3*X 7) * q1 + ((21/10)*X 0*X 5 + (9/5)*X 2*X 7) * q2 + ((3/4)*X 0*X 4 + (-9/4)*X 1*X 7 + (9/20)*X 2*X 6) * q3 + ((27/10)*X 1*X 6 + (-9/10)*X 2*X 5) * q4 + ((-6/5)*X 0*X 2) * q5 + ((6/5)*X 0*X 8) * q7 + ((-9/10)*X 0*X 3) * q8

/-- **The eight Lemma-K♮ identities** (charts 4 and 8). -/
theorem kP_zero {k : Fin 9} (hk : k = 4 ∨ k = 8) (i j : Fin 2) {X : P9} (hq : ∀ r, quadA X r = 0) :
    kP k i j X = 0 := by
  rcases hk with rfl | rfl <;> fin_cases i <;> fin_cases j
  · exact kP_4_0_0 X hq
  · exact kP_4_0_1 X hq
  · exact kP_4_1_0 X hq
  · exact kP_4_1_1 X hq
  · exact kP_8_0_0 X hq
  · exact kP_8_0_1 X hq
  · exact kP_8_1_0 X hq
  · exact kP_8_1_1 X hq

end LSG.JacAnV
