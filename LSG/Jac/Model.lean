/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.TableFacts

/-!
# The P⁸ model of `J = Jac(y² = 4x⁵ + 1)` and the Mumford chart (Stage A1, ABVAR §A0.1)

**Curve.** `C : y² = f(x) = 4x⁵ + 1` (Baker–Grant normal form, `λ₀ = 1`); it is `u² = 1 − 4y⁵`, i.e. the curve
`y⁵ = x(1 − x)` of lean_mstar, after `x ↦ −y` (ABVAR §2.0, `LSG.JacAn.Beta`).

**Mumford chart** (`J ∖ Θ`). A point is `p = (s₁, s₂, b₁, b₀) : Fin 4 → K` (the order of `LSG.JacAn.mumford`),
standing for `a = x² − s₁x + s₂`, `b = b₁x + b₀` with `a ∣ f − b²`. Since `f − b² = a·q + (r₁ x + r₀)` (`mumford_div`),
the chart is the affine variety `r₁ = r₀ = 0` (`mumford_dvd_iff`).

**Grant's P⁸ coordinates** (3Θ basis, `X₀ … X₈ = 1, ℘₁₁, ℘₁₂, ℘₂₂, ℘₁₁₁, ℘₁₁₂, ℘₁₂₂, ℘₂₂₂, ℘₁₂² − ℘₁₁℘₂₂`):
`grantZ p = 4 · X(p)` has integer coefficients (`grant p = X(p)` over a field, `X₀ = 1`). The 9 quadrics `quad X j`
(the partial derivatives of the Coble cubic) cut out the model; `grantZ_onQ`: **the chart lands in `V(Q)`**.

**Symmetries.** `[−1]` is `negP = diag(1,1,1,1,−1,−1,−1,−1,1)` (chart: `b ↦ −b`); `μ₁₀` acts by
`X_k ↦ t^{w_k} X_k`, `w = (0,6,4,2,9,7,5,3,8)` (chart: `(s₁,s₂,b₁,b₀) ↦ (t²s₁, t⁴s₂, t³b₁, t⁵b₀)`), for `t¹⁰ = 1`.
Both preserve the chart, the quadrics and commute with `grantZ`. The origin is `O = e₄` (`origin_onQ`).
-/

namespace LSG.Jac

open Polynomial

section Quadrics

variable {R : Type*} [CommRing R]

/-- The 9 quadrics of the P⁸ model (ABVAR A0.1, `ideal.json`). -/
def quad (X : Fin 9 → R) : Fin 9 → R :=
  ![-X 0 * X 8 - X 1 * X 3 + X 2 ^ 2,
    X 0 * X 7 - 2 * X 1 * X 5 + 2 * X 2 * X 4,
    -2 * X 1 * X 6 + X 2 * X 5 + X 3 * X 4,
    -X 0 * X 4 - X 1 * X 7 - X 2 * X 6 + 2 * X 3 * X 5,
    X 0 * X 5 - X 2 * X 7 + X 3 * X 6,
    -X 0 * X 2 - 2 * X 1 * X 8 - 3 * X 3 ^ 2 - X 4 * X 6 + X 5 ^ 2,
    X 0 * X 3 - 4 * X 1 ^ 2 - 4 * X 2 * X 8 - X 4 * X 7 + X 5 * X 6,
    -X 0 ^ 2 + 8 * X 1 * X 2 - 2 * X 3 * X 8 - X 5 * X 7 + X 6 ^ 2,
    8 * X 0 * X 1 + 4 * X 2 * X 3 + 4 * X 4 * X 5 - X 7 ^ 2 + 4 * X 8 ^ 2]

/-- The data quadrics `Qe` are the explicit ones. -/
theorem Qe_eq (j : Fin 9) (x : Fin 9 → R) : Qe j x = quad x j := by
  fin_cases j <;> simp [Qe, Data.Qd, evalRow, sval, xmono, digit, Fin.prod_univ_succ, quad] <;> ring

theorem onQ_iff (x : Fin 9 → R) : OnQ x ↔ ∀ j, quad x j = 0 := by
  simp [OnQ, Qe_eq]

/-- The origin `O = e₄`. -/
def origin : Fin 9 → R := Pi.single 4 1

theorem origin_onQ : OnQ (origin : Fin 9 → R) := by
  rw [onQ_iff]; intro j; fin_cases j <;> simp [quad, origin]

/-- `[−1]` on P⁸. -/
def negP (X : Fin 9 → R) : Fin 9 → R := ![X 0, X 1, X 2, X 3, -X 4, -X 5, -X 6, -X 7, X 8]

theorem negP_onQ {X : Fin 9 → R} (h : OnQ X) : OnQ (negP X) := by
  rw [onQ_iff] at h ⊢
  intro j
  have := h j
  fin_cases j <;> simp [quad, negP] at this ⊢ <;> first | linear_combination this | linear_combination -this

/-- The `μ₁₀`-weights of the coordinates. -/
def wt : Fin 9 → ℕ := ![0, 6, 4, 2, 9, 7, 5, 3, 8]

/-- `μ₁₀` on P⁸: `X_k ↦ t^{w_k} X_k`. -/
def muP (t : R) (X : Fin 9 → R) : Fin 9 → R := fun k => t ^ wt k * X k

theorem muP_onQ {t : R} (ht : t ^ 10 = 1) {X : Fin 9 → R} (h : OnQ X) : OnQ (muP t X) := by
  rw [onQ_iff] at h ⊢
  intro j
  have hj := h j
  fin_cases j <;> simp [quad, muP, wt] at hj ⊢
  · linear_combination t ^ 8 * hj
  · linear_combination t ^ 3 * hj - 2 * t ^ 3 * (X 1 * X 5 - X 2 * X 4) * ht
  · linear_combination t ^ 11 * hj
  · linear_combination t ^ 9 * hj
  · linear_combination t ^ 7 * hj
  · linear_combination t ^ 4 * hj - t ^ 4 * (2 * X 1 * X 8 + X 4 * X 6 - X 5 ^ 2) * ht
  · linear_combination t ^ 2 * hj - t ^ 2 * (4 * X 1 ^ 2 + 4 * X 2 * X 8 + X 4 * X 7 - X 5 * X 6) * ht
  · linear_combination hj + (8 * X 1 * X 2 - 2 * X 3 * X 8 - X 5 * X 7 + X 6 ^ 2) * ht
  · linear_combination t ^ 6 * hj + 4 * t ^ 6 * (X 4 * X 5 + X 8 ^ 2) * ht

end Quadrics

/-! ## The Mumford chart -/

section Chart

variable {R : Type*} [CommRing R]

/-- First chart relation (coefficient of `x` in `f − b² mod a`). -/
def chartR1 (p : Fin 4 → R) : R :=
  -2 * p 3 * p 2 - p 2 ^ 2 * p 0 + 4 * p 0 ^ 4 - 12 * p 0 ^ 2 * p 1 + 4 * p 1 ^ 2

/-- Second chart relation (constant term of `f − b² mod a`). -/
def chartR0 (p : Fin 4 → R) : R :=
  -p 3 ^ 2 + p 2 ^ 2 * p 1 - 4 * p 0 ^ 3 * p 1 + 8 * p 0 * p 1 ^ 2 + 1

/-- The Mumford chart `J ∖ Θ`: `r₁ = r₀ = 0`. -/
def OnChart (p : Fin 4 → R) : Prop := chartR1 p = 0 ∧ chartR0 p = 0

/-- The curve polynomial `f = 4x⁵ + 1`. -/
noncomputable def fC : R[X] := C 4 * X ^ 5 + 1

/-- `a = x² − s₁x + s₂`. -/
noncomputable def aPoly (p : Fin 4 → R) : R[X] := X ^ 2 - C (p 0) * X + C (p 1)

/-- `b = b₁x + b₀`. -/
noncomputable def bPoly (p : Fin 4 → R) : R[X] := C (p 2) * X + C (p 3)

/-- Division with remainder: `f − b² = a·q + (r₁ x + r₀)`. -/
theorem mumford_div (p : Fin 4 → R) :
    fC - bPoly p ^ 2 = aPoly p * (C 4 * X ^ 3 + C (4 * p 0) * X ^ 2 + C (4 * p 0 ^ 2 - 4 * p 1) * X +
      C (4 * p 0 ^ 3 - 8 * p 0 * p 1 - p 2 ^ 2)) + (C (chartR1 p) * X + C (chartR0 p)) := by
  simp only [fC, aPoly, bPoly, chartR1, chartR0, map_add, map_sub, map_mul, map_neg, map_pow, map_one,
    map_ofNat]
  ring

/-- **The chart is the affine variety `r₁ = r₀ = 0`**: `a ∣ f − b² ↔ OnChart p` (over a field). -/
theorem mumford_dvd_iff {K : Type*} [Field K] (p : Fin 4 → K) : aPoly p ∣ fC - bPoly p ^ 2 ↔ OnChart p := by
  rw [mumford_div]
  constructor
  · intro h
    have h2 : aPoly p ∣ C (chartR1 p) * X + C (chartR0 p) := (dvd_add_right (dvd_mul_right _ _)).mp h
    have hdeg : (aPoly p).degree = 2 := by unfold aPoly; compute_degree!
    have hlt : (C (chartR1 p) * X + C (chartR0 p)).degree < (aPoly p).degree := by
      rw [hdeg]; exact (degree_linear_le).trans_lt (by decide)
    have h0 := eq_zero_of_dvd_of_degree_lt h2 hlt
    have e1 := congrArg (fun q => coeff q 1) h0
    have e0 := congrArg (fun q => coeff q 0) h0
    simp at e1 e0
    exact ⟨e1, e0⟩
  · rintro ⟨h1, h0⟩
    rw [h1, h0]; simp

/-- Grant's coordinates, scaled by 4 (integer coefficients): `grantZ p = 4 · (X₀, …, X₈)(p)`. -/
def grantZ (p : Fin 4 → R) : Fin 9 → R :=
  ![4, p 2 ^ 2 - 4 * p 0 ^ 3 + 4 * p 0 * p 1, -4 * p 1, 4 * p 0,
    -8 * p 3 * p 0 ^ 2 + 4 * p 3 * p 1 - p 2 ^ 3 + 4 * p 2 * p 0 ^ 3 - 12 * p 2 * p 0 * p 1,
    -4 * p 3 * p 0 - 4 * p 2 * p 1, 4 * p 3, 4 * p 2, 2 * p 3 * p 2 + 8 * p 0 ^ 2 * p 1]

/-- **The Mumford chart lands in the model**: `grantZ p ∈ V(Q)`. -/
theorem grantZ_onQ {p : Fin 4 → R} (hp : OnChart p) : OnQ (grantZ p) := by
  obtain ⟨h1, h0⟩ := hp
  unfold chartR1 at h1; unfold chartR0 at h0
  rw [onQ_iff]; intro j
  fin_cases j <;> simp [quad, grantZ]
  · linear_combination 4 * h1
  · linear_combination (-8 * p 3) * h1 + 16 * p 2 * h0
  · linear_combination 4 * p 2 * h1
  · ring
  · ring
  · linear_combination (-32 * p 0 * p 1) * h1 + 16 * (-3 * p 0 ^ 2 + p 1) * h0
  · linear_combination (-16 * p 0 ^ 2) * h1 + 16 * p 0 * h0
  · linear_combination -16 * h0
  · linear_combination 16 * (-p 3 * p 2 - 8 * p 0 ^ 2 * p 1) * h1 + 16 * (p 2 ^ 2 - 8 * p 0 ^ 3 + 4 * p 0 * p 1) * h0

/-- Grant's coordinates over a field, `X₀ = 1`. -/
noncomputable def grant {K : Type*} [Field K] (p : Fin 4 → K) : Fin 9 → K := fun k => grantZ p k / 4

theorem grant_onQ {K : Type*} [Field K] [CharZero K] {p : Fin 4 → K} (hp : OnChart p) : OnQ (grant p) := by
  have h := grantZ_onQ hp
  rw [onQ_iff] at h ⊢
  intro j
  have hj := h j
  have e : grant p = fun k => (1 / 4 : K) * grantZ p k := by funext k; simp [grant]; ring
  rw [e]
  fin_cases j <;> simp only [quad] at hj ⊢ <;> simp at hj ⊢ <;> linear_combination (1 / 16 : K) * hj

theorem grant_zero {K : Type*} [Field K] [CharZero K] (p : Fin 4 → K) : grant p 0 = 1 := by
  simp [grant, grantZ]

/-- The chart coordinates are linear in Grant's: `s₁ = X₃`, `s₂ = −X₂`, `b₁ = X₇`, `b₀ = X₆`. -/
theorem grant_chart {K : Type*} [Field K] [CharZero K] (p : Fin 4 → K) :
    grant p 3 = p 0 ∧ -grant p 2 = p 1 ∧ grant p 7 = p 2 ∧ grant p 6 = p 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [grant, grantZ] <;> ring

/-- `[−1]` on the chart: `b ↦ −b`. -/
def negC (p : Fin 4 → R) : Fin 4 → R := ![p 0, p 1, -p 2, -p 3]

theorem negC_onChart {p : Fin 4 → R} (hp : OnChart p) : OnChart (negC p) := by
  obtain ⟨h1, h0⟩ := hp
  unfold chartR1 at h1; unfold chartR0 at h0
  refine ⟨?_, ?_⟩ <;> simp [chartR1, chartR0, negC]
  · linear_combination h1
  · linear_combination h0

theorem grantZ_negC (p : Fin 4 → R) : grantZ (negC p) = negP (grantZ p) := by
  funext k; fin_cases k <;> simp [grantZ, negC, negP] <;> ring

/-- `μ₁₀` on the chart. -/
def muC (t : R) (p : Fin 4 → R) : Fin 4 → R := ![t ^ 2 * p 0, t ^ 4 * p 1, t ^ 3 * p 2, t ^ 5 * p 3]

theorem muC_onChart {t : R} (ht : t ^ 10 = 1) {p : Fin 4 → R} (hp : OnChart p) : OnChart (muC t p) := by
  obtain ⟨h1, h0⟩ := hp
  unfold chartR1 at h1; unfold chartR0 at h0
  refine ⟨?_, ?_⟩ <;> simp [chartR1, chartR0, muC]
  · linear_combination t ^ 8 * h1
  · linear_combination h0 + (-p 3 ^ 2 + p 2 ^ 2 * p 1 - 4 * p 0 ^ 3 * p 1 + 8 * p 0 * p 1 ^ 2) * ht

theorem grantZ_muC (t : R) (p : Fin 4 → R) : grantZ (muC t p) = muP t (grantZ p) := by
  funext k; fin_cases k <;> simp [grantZ, muC, muP, wt] <;> ring

end Chart

end LSG.Jac
