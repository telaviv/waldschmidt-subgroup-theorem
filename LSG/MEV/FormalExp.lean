import Mathlib
import LSG.MEV.Transl
import LSG.ME.FormalExp

/-!
# The formal exponential of `E^♮` (VECEXT_SPIKE §7.5)

For a direction `(a, b)` of `Lie E^♮ = ℂ²` (base `a`, fibre `b`), the formal curve
`z ↦ exp(z (a, b))` in the `V`-chart of the model `X ⊂ ℙ⁴` is
`(s(z) : 1 : t(z) : t(z) u(z) + 2 s(z)² : u(z))`, where `(s, t, u)` solves the polynomial ODE
```
s' = a (−1/2 − g₂ s t − (3/2) g₃ t²),   t' = a (−6 s² + (g₂/2) t²),   u' = b + a (2 g₂ s² + 3 g₃ s t),
```
`s(0) = t(0) = u(0) = 0`. The base part is the abelian `V`-chart flow (`s = ℘/℘'`, `t = 1/℘'`
along `z ↦ a z`). The fibre coordinate `u = T₃/V = t_aff − 2x²/y` (`t_aff = b z − ζ(a z)`) has
`u' = b + a(−3x + (12x⁴ − g₂x²)/y²)`, which reduces to the polynomial above modulo the curve
equation `t = 4s³ − g₂ s t² − g₃ t³` (for `b = 0`: `u = −(ζ + 2℘²/℘') = g₂z³/6 + 3g₃z⁵/20 + ⋯`;
checked against the Laurent expansions of `℘, ζ` to order `z¹¹`, `scripts`-free sympy check).
`T₁ = t u + 2s²` makes `G = W T₃ − V T₁ + 2U²` vanish identically.

* `vfV`, `stu` (the solution, by `LSG.ME.solve`), `ExpBlock`.
* **`Fn_ExpBlock`**, **`Gn_ExpBlock`**: the formal curve lies on `X` (the Lie derivative of the
  `V`-chart cubic `t − 4s³ + g₂st² + g₃t³` along the field vanishes identically).
* `constantCoeff_ExpBlock`: the curve starts at `ptO 0`, the identity of `E^♮`.
* `ExpBlock_fib`: for `a = 0` the curve is `ptO (b z)` (the fibre direction is exact and linear).
* `LieV`, **`ExpV w`**: the formal exponential of `G̃` (`x ↦ ξ z`, `y ↦ e^{η z}`, `z ↦ e^{−η z}`,
  blocks `ExpBlock`), on `G̃` (`ExpV_YZ`, `ExpV_F`, `ExpV_G`).
-/

open MvPolynomial LSG.Elliptic

namespace LSG.MEV

section Block

variable {K : Type*} [Field K] [CharZero K]

local notation "dz" => (PowerSeries.derivative (R := K))

/-- The vector field on `(s, t, u)`. -/
noncomputable def vfV (g₂ g₃ a b : K) : Fin 3 → MvPolynomial (Fin 3) K :=
  ![C a * (C (-1 / 2) - C g₂ * X 0 * X 1 - C (3 / 2 * g₃) * X 1 ^ 2),
    C a * (C (-6) * X 0 ^ 2 + C (g₂ / 2) * X 1 ^ 2),
    C b + C a * (C (2 * g₂) * X 0 ^ 2 + C (3 * g₃) * X 0 * X 1)]

/-- The solution `(s, t, u)` with initial value `0`. -/
noncomputable def stu (g₂ g₃ a b : K) : Fin 3 → PowerSeries K :=
  LSG.ME.solve (vfV g₂ g₃ a b) (0 : Fin 3 → K)

/-- **The formal exponential of one `E^♮` factor**, `V`-chart: `(s : 1 : t : t u + 2s² : u)`. -/
noncomputable def ExpBlock (g₂ g₃ a b : K) : Fin 5 → PowerSeries K :=
  ![stu g₂ g₃ a b 0, 1, stu g₂ g₃ a b 1,
    stu g₂ g₃ a b 1 * stu g₂ g₃ a b 2 + 2 * stu g₂ g₃ a b 0 ^ 2, stu g₂ g₃ a b 2]

/-- The `V`-chart cubic `t − 4s³ + g₂ s t² + g₃ t³`. -/
noncomputable def Fchart (g₂ g₃ : K) : MvPolynomial (Fin 3) K :=
  X 1 - C 4 * X 0 ^ 3 + C g₂ * X 0 * X 1 ^ 2 + C g₃ * X 1 ^ 3

/-- The Lie derivative of the chart cubic along the field vanishes identically. -/
theorem lieDeriv_Fchart (g₂ g₃ a b : K) :
    ∑ v, pderiv v (Fchart g₂ g₃) * vfV g₂ g₃ a b v = 0 := by
  apply MvPolynomial.funext
  intro x
  simp [Fin.sum_univ_three, Fchart, vfV, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X,
    Pi.single_apply]
  ring

theorem stu_deriv (g₂ g₃ a b : K) (v : Fin 3) :
    dz (stu g₂ g₃ a b v) = aeval (stu g₂ g₃ a b) (vfV g₂ g₃ a b v) :=
  LSG.ME.solve_deriv (K := K) _ _ v

theorem stu_const (g₂ g₃ a b : K) (v : Fin 3) :
    PowerSeries.constantCoeff (stu g₂ g₃ a b v) = 0 :=
  LSG.ME.solve_const (K := K) _ _ v

/-- The formal curve stays on the chart cubic. -/
theorem aeval_Fchart (g₂ g₃ a b : K) : aeval (stu g₂ g₃ a b) (Fchart g₂ g₃) = 0 := by
  have hd : dz (aeval (stu g₂ g₃ a b) (Fchart g₂ g₃)) = 0 := by
    rw [LSG.ME.derivative_aeval]
    simp only [stu_deriv, ← map_mul, ← map_sum, lieDeriv_Fchart, map_zero]
  rw [LSG.ME.eq_C_of_derivative_eq_zero (K := K) hd, LSG.ME.constantCoeff_aeval]
  simp only [stu_const]
  simp [Fchart]

theorem Fn_ExpBlock (g₂ g₃ a b : K) :
    Fn (algebraMap K (PowerSeries K) g₂) (algebraMap K (PowerSeries K) g₃) (ExpBlock g₂ g₃ a b) =
      0 := by
  have h := aeval_Fchart g₂ g₃ a b
  simp only [Fchart, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_ofNat] at h
  simp only [Fn, F, ExpBlock, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination h

theorem Gn_ExpBlock (g₂ g₃ a b : K) : Gn (ExpBlock g₂ g₃ a b) = 0 := by
  simp only [Gn, Gfib, ExpBlock, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  show stu g₂ g₃ a b 1 * stu g₂ g₃ a b 2 -
      1 * (stu g₂ g₃ a b 1 * stu g₂ g₃ a b 2 + 2 * stu g₂ g₃ a b 0 ^ 2) +
      2 * stu g₂ g₃ a b 0 ^ 2 = 0
  ring

theorem constantCoeff_ExpBlock (g₂ g₃ a b : K) (i : Fin 5) :
    PowerSeries.constantCoeff (ExpBlock g₂ g₃ a b i) = ptO 0 i := by
  fin_cases i <;> simp [ExpBlock, ptO, stu_const]

/-- **The fibre direction is exact**: for `a = 0`, `ExpBlock = ptO (b z)`. -/
theorem stu_fib (g₂ g₃ b : K) :
    stu g₂ g₃ 0 b = ![0, 0, PowerSeries.C b * PowerSeries.X] := by
  symm
  apply LSG.ME.eq_solve
  · intro v
    fin_cases v <;> simp [vfV]
  · intro v
    fin_cases v <;> simp

theorem ExpBlock_fib (g₂ g₃ b : K) :
    ExpBlock g₂ g₃ 0 b = ptO (PowerSeries.C b * PowerSeries.X) := by
  funext i
  fin_cases i <;> simp [ExpBlock, stu_fib, ptO]

end Block

/-! ### The formal exponential of `G̃` -/

section Full

variable {K : Type*} [Field K] [CharZero K] {d₀ d₁ m : ℕ}

/-- The Lie algebra of `G̃`: `K^{d₀} × K^{d₁} × (K²)^m` (each `E^♮` factor: base, fibre). -/
abbrev LieV (K : Type*) (d₀ d₁ m : ℕ) : Type _ := (Fin d₀ → K) × (Fin d₁ → K) × (Fin m → K × K)

variable (g₂ g₃ : Fin m → K)

/-- **The formal exponential** `z ↦ exp(z w)` of `G̃` (identity at `z = 0`). -/
noncomputable def ExpV (w : LieV K d₀ d₁ m) : Var d₀ d₁ m → PowerSeries K
  | .x i => PowerSeries.C (w.1 i) * PowerSeries.X
  | .y j => PowerSeries.rescale (w.2.1 j) (PowerSeries.exp K)
  | .z j => PowerSeries.rescale (-w.2.1 j) (PowerSeries.exp K)
  | .e k c => ExpBlock (g₂ k) (g₃ k) (w.2.2 k).1 (w.2.2 k).2 c

theorem ExpV_YZ (w : LieV K d₀ d₁ m) (j : Fin d₁) :
    ExpV g₂ g₃ w (.y j) * ExpV g₂ g₃ w (.z j) = 1 := by
  simp only [ExpV]
  rw [PowerSeries.exp_mul_exp_eq_exp_add, add_neg_cancel]
  ext n
  rcases n with _ | n <;> simp [PowerSeries.coeff_rescale]

theorem ExpV_F (w : LieV K d₀ d₁ m) (k : Fin m) :
    Fn (algebraMap K (PowerSeries K) (g₂ k)) (algebraMap K (PowerSeries K) (g₃ k))
      (fun c => ExpV g₂ g₃ w (.e k c)) = 0 :=
  Fn_ExpBlock _ _ _ _

theorem ExpV_G (w : LieV K d₀ d₁ m) (k : Fin m) : Gn (fun c => ExpV g₂ g₃ w (.e k c)) = 0 :=
  Gn_ExpBlock _ _ _ _

end Full

end LSG.MEV
