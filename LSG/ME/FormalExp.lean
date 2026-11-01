import Mathlib
import LSG.ME.Order

/-!
# Formal exponentials on the multi-cone model (STAGE2 §10)

Formal power series in one variable `z` over a commutative `K`-algebra `R` (`K` a field of
characteristic `0`); `R = K` for points of `G`, `R = K⟦z⟧` for two-parameter families.

* **Polynomial ODEs** (`solve`): for a polynomial vector field `F : σ → K[σ]` and an initial value
  `x₀ : σ → R` there is a unique `Γ : σ → R⟦z⟧` with `Γ' = F(Γ)` and `Γ(0) = x₀` (Picard
  iteration; `solve_deriv`, `solve_const`, `eq_solve`).
* **Flows** (`IsFlow b w Γ`): `Γ' = Dw_{b,w}(X)(Γ)` (the chart derivations of `LSG.ME.Deriv`, i.e.
  `x ↦ ξ`, `y ↦ η y`, `z ↦ −η z`, `(U,V,W) ↦ ζ · chartPoly_b`). Then
  `(Q ∘ Γ)' = (Dw_{b,w} Q) ∘ Γ` (`deriv_aeval_flow`). A flow is **normalized** (`IsNFlow`) if
  `b k ∈ {V, W}` and the chart coordinate of every elliptic block is `1`; then also
  `(Q ∘ Γ)' = (Dh_{b,w} Q) ∘ Γ` and the **Taylor formula** `n! · [zⁿ](Q ∘ Γ) = (Dh^n Q)(Γ(0))`
  holds (`taylor`).
* `fflow b w x₀`: the flow with initial value `x₀`; it is normalized, stays on `G`
  (`fflow_Fk`, `fflow_YZ`) if `x₀` is.
* **The formal exponential** `Exp w = fflow V w 0` (`V`-charts): `x ↦ ξ z`, `y ↦ exp(η z)`, and in
  each elliptic block the cone point `P(ζ z) = (s(ζ z), 1, t(ζ z))` with
  `s′ = −1/2 − g₂ s t − (3/2) g₃ t²`, `t′ = −6 s² + (g₂/2) t²`, `s(0) = t(0) = 0`, and
  `F(P(z)) = 0` (`Exp_*`).
* `fexp p w = fflow (chartAt p) w (coords p 1)`: the point `p + exp(z w)` (canonical charts).
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (DL DL_cons)

namespace LSG.ME

/-! ### Formal integration and polynomial ODEs -/

section ODE

variable {K : Type u} [Field K] [CharZero K] {R : Type*} [CommRing R] [Algebra K R]

local notation "Xz" => (PowerSeries.X : PowerSeries R)
local notation "dz" => (PowerSeries.derivative (R := R))

/-- The formal integral `∫₀ f`. -/
noncomputable def integ (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else algebraMap K R ((n : K)⁻¹) * PowerSeries.coeff (n - 1) f

theorem natCast_inv_mul (n : ℕ) : algebraMap K R ((n + 1 : ℕ) : K)⁻¹ * ((n : R) + 1) = 1 := by
  have h : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [show ((n : R) + 1) = algebraMap K R ((n + 1 : ℕ) : K) by push_cast; simp, ← map_mul,
    inv_mul_cancel₀ h, map_one]

include K in
theorem mul_succ_cancel {a b : R} (n : ℕ) (h : a * ((n : R) + 1) = b * ((n : R) + 1)) :
    a = b := by
  have := congrArg (· * algebraMap K R ((n + 1 : ℕ) : K)⁻¹) h
  rwa [mul_assoc, mul_assoc, mul_comm ((n : R) + 1), natCast_inv_mul, mul_one, mul_one] at this

theorem derivative_integ (f : PowerSeries R) : dz (integ (K := K) f) = f := by
  ext n
  rw [PowerSeries.coeff_derivative, integ, PowerSeries.coeff_mk,
    ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero n)),
    Nat.add_sub_cancel, mul_comm, ← mul_assoc, mul_comm _ (algebraMap K R _),
    natCast_inv_mul, one_mul]

omit [CharZero K] in
theorem dvd_integ {n : ℕ} {f : PowerSeries R} (hf : Xz ^ n ∣ f) :
    Xz ^ (n + 1) ∣ integ (K := K) f := by
  rw [PowerSeries.X_pow_dvd_iff] at hf ⊢
  intro i hi
  rw [integ, PowerSeries.coeff_mk]
  split_ifs with h
  · rfl
  · rw [hf (i - 1) (by omega), mul_zero]

include K in
/-- A power series with vanishing derivative is constant. -/
theorem eq_C_of_derivative_eq_zero {f : PowerSeries R} (hf : dz f = 0) :
    f = PowerSeries.C (PowerSeries.constantCoeff f) := by
  ext n
  rcases n with _ | n
  · simp
  · have h := congrArg (PowerSeries.coeff n) hf
    rw [PowerSeries.coeff_derivative, map_zero] at h
    have := mul_succ_cancel (K := K) n (h.trans (zero_mul _).symm)
    rw [this, PowerSeries.coeff_C, ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero n))]

include K in
/-- `f' = a f` and `f(0) = 0` imply `f = 0`. -/
theorem eq_zero_of_derivative_eq_mul {f a : PowerSeries R}
    (hf : dz f = a * f) (h0 : PowerSeries.constantCoeff f = 0) : f = 0 := by
  have key : ∀ n, ∀ i ≤ n, PowerSeries.coeff i f = 0 := by
    intro n
    induction n with
    | zero => intro i hi; rw [Nat.le_zero.mp hi, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    | succ n ih =>
      intro i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact ih i (by omega)
      · have hi' : i = n + 1 := by omega
        subst hi'
        have h1 := congrArg (PowerSeries.coeff n) hf
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
          Finset.sum_eq_zero (fun p hp => by
            rw [ih p.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega),
              mul_zero])] at h1
        exact mul_succ_cancel (K := K) n (h1.trans (zero_mul _).symm)
  ext n; simpa using key n n le_rfl

variable {σ : Type*}

omit [CharZero K] in
/-- Substitutions agreeing modulo `zⁿ` agree modulo `zⁿ` on all polynomials. -/
theorem aeval_dvd_sub {n : ℕ} {Γ Γ' : σ → PowerSeries R} (h : ∀ v, Xz ^ n ∣ Γ v - Γ' v)
    (Q : MvPolynomial σ K) : Xz ^ n ∣ aeval Γ Q - aeval Γ' Q := by
  set I : Ideal (PowerSeries R) := Ideal.span {Xz ^ n}
  have hext : (Ideal.Quotient.mkₐ K I).comp (aeval Γ) =
      (Ideal.Quotient.mkₐ K I).comp (aeval Γ') := by
    refine MvPolynomial.algHom_ext fun v => ?_
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (h v))
  have := congrArg (fun φ => φ Q) hext
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp this)

variable (F : σ → MvPolynomial σ K) (x₀ : σ → R)

/-- Picard iterates. -/
noncomputable def pic : ℕ → σ → PowerSeries R
  | 0 => fun v => PowerSeries.C (x₀ v)
  | n + 1 => fun v => PowerSeries.C (x₀ v) + integ (K := K) (aeval (pic n) (F v))

omit [CharZero K] in
theorem pic_succ_sub (n : ℕ) (v : σ) : Xz ^ (n + 1) ∣ pic F x₀ (n + 1) v - pic F x₀ n v := by
  induction n generalizing v with
  | zero =>
    simp only [pic]
    rw [add_sub_cancel_left]
    exact dvd_integ (n := 0) (by simp)
  | succ n ih =>
    have e : pic F x₀ (n + 2) v - pic F x₀ (n + 1) v =
        integ (K := K) (aeval (pic F x₀ (n + 1)) (F v) - aeval (pic F x₀ n) (F v)) := by
      simp only [pic, add_sub_add_left_eq_sub, integ]
      ext i
      simp only [map_sub, PowerSeries.coeff_mk]
      split_ifs <;> ring
    rw [e]
    exact dvd_integ (aeval_dvd_sub ih _)

omit [CharZero K] in
theorem pic_sub (n : ℕ) : ∀ k, ∀ v, Xz ^ (n + 1) ∣ pic F x₀ (n + k) v - pic F x₀ n v := by
  intro k
  induction k with
  | zero => intro v; simp
  | succ k ih =>
    intro v
    have h1 := pic_succ_sub F x₀ (n + k) v
    have h2 : Xz ^ (n + 1) ∣ Xz ^ (n + k + 1) := pow_dvd_pow _ (by omega)
    have := dvd_add (h2.trans h1) (ih v)
    rw [sub_add_sub_cancel] at this
    rwa [show n + (k + 1) = n + k + 1 by ring]

/-- **The solution** of `Γ' = F(Γ)`, `Γ(0) = x₀`. -/
noncomputable def solve (v : σ) : PowerSeries R :=
  PowerSeries.mk fun n => PowerSeries.coeff n (pic F x₀ n v)

omit [CharZero K] in
theorem solve_sub_pic (n : ℕ) (v : σ) : Xz ^ (n + 1) ∣ solve F x₀ v - pic F x₀ n v := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  rw [map_sub, solve, PowerSeries.coeff_mk]
  have := pic_sub F x₀ i (n - i) v
  rw [PowerSeries.X_pow_dvd_iff] at this
  have h := this i (by omega)
  rw [map_sub, show i + (n - i) = n by omega] at h
  exact (sub_eq_zero.mp h).symm ▸ sub_self _

omit [CharZero K] in
theorem solve_const (v : σ) : PowerSeries.constantCoeff (solve F x₀ v) = x₀ v := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, solve, PowerSeries.coeff_mk]
  simp [pic]

theorem solve_deriv (v : σ) :
    dz (solve F x₀ v) = aeval (solve F x₀) (F v) := by
  ext n
  rw [PowerSeries.coeff_derivative]
  have h1 := solve_sub_pic F x₀ (n + 1) v
  rw [PowerSeries.X_pow_dvd_iff] at h1
  have e1 := sub_eq_zero.mp (by simpa using h1 (n + 1) (by omega))
  have h2 := aeval_dvd_sub (fun u => solve_sub_pic F x₀ n u) (F v)
  rw [PowerSeries.X_pow_dvd_iff] at h2
  have e2 := sub_eq_zero.mp (by simpa using h2 n (by omega))
  rw [e1, e2]
  simp only [pic, map_add, PowerSeries.coeff_C,
    ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero n)), zero_add, integ,
    PowerSeries.coeff_mk, Nat.add_sub_cancel]
  rw [mul_comm, ← mul_assoc, mul_comm _ (algebraMap K R _), natCast_inv_mul, one_mul]

variable {F x₀} in
/-- **Uniqueness** of solutions. -/
theorem eq_solve {Γ : σ → PowerSeries R}
    (hd : ∀ v, dz (Γ v) = aeval Γ (F v))
    (h0 : ∀ v, PowerSeries.constantCoeff (Γ v) = x₀ v) : Γ = solve F x₀ := by
  have key : ∀ n, ∀ v, Xz ^ (n + 1) ∣ Γ v - solve F x₀ v := by
    intro n
    induction n with
    | zero =>
      intro v
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff, map_sub, h0, solve_const, sub_self]
    | succ n ih =>
      intro v
      rw [PowerSeries.X_pow_dvd_iff]
      intro i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact (PowerSeries.X_pow_dvd_iff.mp (ih v)) i h
      · have hi' : i = n + 1 := by omega
        subst hi'
        have h2 := aeval_dvd_sub ih (F v)
        rw [PowerSeries.X_pow_dvd_iff] at h2
        have e := h2 n (by omega)
        rw [← hd, ← solve_deriv, ← map_sub, PowerSeries.coeff_derivative] at e
        exact mul_succ_cancel (K := K) n (e.trans (zero_mul _).symm)
  funext v
  ext n
  have := PowerSeries.X_pow_dvd_iff.mp (key n v) n (by omega)
  rwa [map_sub, sub_eq_zero] at this

omit [CharZero K] in
/-- A `K`-compatible ring hom commutes with substitution. -/
theorem ringHom_aeval {A B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →+* B) (hf : ∀ a : K, f (algebraMap K A a) = algebraMap K B a) (Γ : σ → A)
    (Q : MvPolynomial σ K) : f (aeval Γ Q) = aeval (fun v => f (Γ v)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [hf]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

omit [CharZero K] in
theorem constantCoeff_aeval (Γ : σ → PowerSeries R) (Q : MvPolynomial σ K) :
    PowerSeries.constantCoeff (aeval Γ Q) = aeval (fun v => PowerSeries.constantCoeff (Γ v)) Q :=
  ringHom_aeval _ (fun a => by simp [PowerSeries.algebraMap_apply]) Γ Q

omit [CharZero K] in
/-- **Chain rule** for the formal derivative. -/
theorem derivative_aeval [Fintype σ] (Γ : σ → PowerSeries R)
    (Q : MvPolynomial σ K) :
    dz (aeval Γ Q) = ∑ v, aeval Γ (pderiv v Q) * dz (Γ v) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [PowerSeries.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p v hp =>
    have e : ∀ x, pderiv x (p * X v) =
        p * (Pi.single x (1 : MvPolynomial σ K) : σ → _) v + X v * pderiv x p := by
      intro x; rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
    simp_rw [e]
    rw [map_mul, aeval_X, Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul]
    have e1 : ∑ x, aeval Γ (p * (Pi.single x (1 : MvPolynomial σ K) : σ → _) v) * dz (Γ x) =
        aeval Γ p * dz (Γ v) := by
      rw [Finset.sum_eq_single v (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb)]; simp)
        (by simp)]
      simp
    have e2 : ∑ x, aeval Γ (X v * pderiv x p) * dz (Γ x) =
        Γ v * ∑ x, aeval Γ (pderiv x p) * dz (Γ x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by rw [map_mul, aeval_X]; ring
    simp only [map_add, add_mul, Finset.sum_add_distrib, e1, e2]

end ODE

/-! ### Flows of the invariant derivations -/

section Flow

variable {K : Type u} [Field K] [CharZero K] {R : Type*} [CommRing R] [Algebra K R]
  {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

local notation "dz" => (PowerSeries.derivative (R := R))

variable (g₂ g₃) in
/-- `Γ` is a **flow** of `D_w` in the charts `b`: `Γ' = D_w(X)(Γ)`. -/
def IsFlow (b : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (Γ : Var d₀ d₁ m → PowerSeries R) : Prop :=
  ∀ v, dz (Γ v) = aeval Γ (dval g₂ g₃ b w v)

variable (g₂ g₃) in
/-- A **normalized flow**: charts in `{V, W}`, chart coordinates `≡ 1`. -/
structure IsNFlow (b : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (Γ : Var d₀ d₁ m → PowerSeries R) :
    Prop where
  flow : IsFlow g₂ g₃ b w Γ
  chart : ∀ k, b k ≠ 0
  norm : ∀ k, Γ (.e k (b k)) = 1

omit [CharZero K] in
/-- `(Q ∘ Γ)' = (D_w Q) ∘ Γ` along a flow. -/
theorem deriv_aeval_flow {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m}
    {Γ : Var d₀ d₁ m → PowerSeries R} (hΓ : IsFlow g₂ g₃ b w Γ) (Q : MvPolynomial (Var d₀ d₁ m) K) :
    dz (aeval Γ Q) = aeval Γ (Dw g₂ g₃ b w Q) := by
  classical
  rw [derivative_aeval, Dw_apply, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hΓ v, map_mul, mul_comm]

omit [CharZero K] in
theorem aeval_mult {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m} {Γ : Var d₀ d₁ m → PowerSeries R}
    (hΓ : IsNFlow g₂ g₃ b w Γ) (v : Var d₀ d₁ m) : aeval Γ (mult (K := K) b v) = 1 := by
  cases v with
  | e k c => simp [mult, Lo, hΓ.norm]
  | _ => simp [mult, Lc, hΓ.norm]

omit [CharZero K] in
theorem aeval_Dh {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m} {Γ : Var d₀ d₁ m → PowerSeries R}
    (hΓ : IsNFlow g₂ g₃ b w Γ) (Q : MvPolynomial (Var d₀ d₁ m) K) :
    aeval Γ (Dh g₂ g₃ b w Q) = aeval Γ (Dw g₂ g₃ b w Q) := by
  rw [Dh_eq_sum, Dw_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [dvalh, map_mul, aeval_mult hΓ, one_mul]

omit [CharZero K] in
/-- `(Q ∘ Γ)' = (Dh_w Q) ∘ Γ` along a normalized flow. -/
theorem deriv_aeval_nflow {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m}
    {Γ : Var d₀ d₁ m → PowerSeries R} (hΓ : IsNFlow g₂ g₃ b w Γ)
    (Q : MvPolynomial (Var d₀ d₁ m) K) : dz (aeval Γ Q) = aeval Γ (Dh g₂ g₃ b w Q) := by
  rw [deriv_aeval_flow hΓ.flow, aeval_Dh hΓ]

omit [CharZero K] in
theorem iterate_deriv_aeval {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m}
    {Γ : Var d₀ d₁ m → PowerSeries R} (hΓ : IsNFlow g₂ g₃ b w Γ) (n : ℕ)
    (Q : MvPolynomial (Var d₀ d₁ m) K) :
    dz^[n] (aeval Γ Q) = aeval Γ (DL (Dh g₂ g₃ b) (List.replicate n w) Q) := by
  induction n generalizing Q with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, deriv_aeval_nflow hΓ, ih, List.replicate_succ, DL_cons]

omit [CharZero K] in
/-- **Taylor formula** along a normalized flow. -/
theorem taylor {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m} {Γ : Var d₀ d₁ m → PowerSeries R}
    (hΓ : IsNFlow g₂ g₃ b w Γ) (n : ℕ) (Q : MvPolynomial (Var d₀ d₁ m) K) :
    (n.factorial : R) * PowerSeries.coeff n (aeval Γ Q) =
      aeval (fun v => PowerSeries.constantCoeff (Γ v))
        (DL (Dh g₂ g₃ b) (List.replicate n w) Q) := by
  rw [← PowerSeries.constantCoeff_iterate_derivative, iterate_deriv_aeval hΓ, constantCoeff_aeval]

/-- If `D_w G = a · G`, then `G ∘ Γ = 0` along a flow whenever `G(Γ(0)) = 0`. -/
theorem aeval_eq_zero_of_Dw {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m}
    {Γ : Var d₀ d₁ m → PowerSeries R} (hΓ : IsFlow g₂ g₃ b w Γ) {G a : MvPolynomial (Var d₀ d₁ m) K}
    (hG : Dw g₂ g₃ b w G = a * G) (h0 : aeval (fun v => PowerSeries.constantCoeff (Γ v)) G = 0) :
    aeval Γ G = 0 := by
  refine eq_zero_of_derivative_eq_mul (K := K) (a := aeval Γ a) ?_ ?_
  · rw [deriv_aeval_flow hΓ, hG, map_mul]
  · rw [constantCoeff_aeval, h0]

variable (g₂ g₃) in
/-- **The flow** of `D_w` (charts `b`) with initial value `x₀`. -/
noncomputable def fflow (b : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (x₀ : Var d₀ d₁ m → R) :
    Var d₀ d₁ m → PowerSeries R :=
  solve (dval g₂ g₃ b w) x₀

theorem fflow_isFlow (b : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (x₀ : Var d₀ d₁ m → R) :
    IsFlow g₂ g₃ b w (fflow g₂ g₃ b w x₀) :=
  solve_deriv _ _

omit [CharZero K] in
theorem fflow_const (b : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (x₀ : Var d₀ d₁ m → R)
    (v : Var d₀ d₁ m) : PowerSeries.constantCoeff (fflow g₂ g₃ b w x₀ v) = x₀ v :=
  solve_const _ _ v

/-- Flows are determined by their initial values. -/
theorem eq_fflow {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m} {Γ : Var d₀ d₁ m → PowerSeries R}
    (hΓ : IsFlow g₂ g₃ b w Γ) : Γ = fflow g₂ g₃ b w (fun v => PowerSeries.constantCoeff (Γ v)) :=
  eq_solve hΓ fun _ => rfl

omit [CharZero K] in
theorem chartPoly_self {ch : Fin 3} (hch : ch ≠ 0) (k : Fin m) :
    chartPoly g₂ g₃ d₀ d₁ ch k ch = 0 := by
  fin_cases ch
  · exact absurd rfl hch
  · simp [chartPoly, chartV]
  · simp [chartPoly, chartW]

theorem fflow_norm {b : Fin m → Fin 3} (hb : ∀ k, b k ≠ 0) (w : LieE K d₀ d₁ m)
    {x₀ : Var d₀ d₁ m → R} (hx₀ : ∀ k, x₀ (.e k (b k)) = 1) (k : Fin m) :
    fflow g₂ g₃ b w x₀ (.e k (b k)) = 1 := by
  have hd : dz (fflow g₂ g₃ b w x₀ (.e k (b k))) = 0 := by
    rw [fflow_isFlow b w x₀ (.e k (b k))]
    simp [dval, chartPoly_self (hb k)]
  rw [eq_C_of_derivative_eq_zero (K := K) hd, fflow_const, hx₀, map_one]

theorem fflow_isNFlow {b : Fin m → Fin 3} (hb : ∀ k, b k ≠ 0) (w : LieE K d₀ d₁ m)
    {x₀ : Var d₀ d₁ m → R} (hx₀ : ∀ k, x₀ (.e k (b k)) = 1) :
    IsNFlow g₂ g₃ b w (fflow g₂ g₃ b w x₀) :=
  ⟨fflow_isFlow b w x₀, hb, fflow_norm hb w hx₀⟩

/-- Flows stay on the cubics. -/
theorem flow_Fk {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m} {Γ : Var d₀ d₁ m → PowerSeries R}
    (hΓ : IsFlow g₂ g₃ b w Γ) (k : Fin m)
    (h0 : aeval (fun v => PowerSeries.constantCoeff (Γ v)) (Fk g₂ g₃ d₀ d₁ k) = 0) :
    aeval Γ (Fk g₂ g₃ d₀ d₁ k) = 0 :=
  aeval_eq_zero_of_Dw hΓ (Dw_Fk two_ne_zero b w k) h0

/-- Flows stay on `Y Z = 1`. -/
theorem flow_YZ {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m} {Γ : Var d₀ d₁ m → PowerSeries R}
    (hΓ : IsFlow g₂ g₃ b w Γ) (j : Fin d₁)
    (h0 : aeval (fun v => PowerSeries.constantCoeff (Γ v)) (YZ K d₀ m j) = 0) :
    aeval Γ (YZ K d₀ m j) = 0 :=
  aeval_eq_zero_of_Dw hΓ (a := 0) (by rw [zero_mul]; exact Dw_YZ b w j) h0

end Flow

/-! ### The formal exponential and the points `p + exp(z w)` -/

section Exp

variable {K : Type u} [Field K] [CharZero K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

local notation "dz" => (PowerSeries.derivative (R := K))

omit [CharZero K] in
theorem coords_chartAt (p : GPt K d₀ d₁ g₂ g₃) (k : Fin m) :
    coords p 1 (.e k (chartAt p k)) = 1 := by
  simp [coords, rep_chartAt]

omit [CharZero K] in
theorem chartAt_ne (p : GPt K d₀ d₁ g₂ g₃) (k : Fin m) : chartAt p k ≠ 0 := by
  unfold chartAt; split <;> decide

variable (g₂ g₃) in
/-- **The point `p + exp(z w)`**: the flow of `D_w` from the normalized representative of `p`, in
the canonical charts at `p`. -/
noncomputable def fexp (p : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) : Var d₀ d₁ m → PowerSeries K :=
  fflow g₂ g₃ (chartAt p) w (coords p 1)

theorem fexp_isNFlow (p : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) :
    IsNFlow g₂ g₃ (chartAt p) w (fexp g₂ g₃ p w) :=
  fflow_isNFlow (chartAt_ne p) w (coords_chartAt p)

omit [CharZero K] in
theorem fexp_const (p : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) :
    PowerSeries.constantCoeff (fexp g₂ g₃ p w v) = coords p 1 v :=
  fflow_const _ _ _ v

/-- `p + exp(z w)` lies on the cubics. -/
theorem fexp_Fk (p : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (k : Fin m) :
    aeval (fexp g₂ g₃ p w) (Fk g₂ g₃ d₀ d₁ k) = 0 := by
  refine flow_Fk (fexp_isNFlow p w).flow k ?_
  simp only [fexp_const]
  have := Fv_rep (two_ne_zero (α := K)) (p.2.2 k)
  simpa [Fk, Fv, F, coords] using this

/-- `p + exp(z w)` lies on `Y Z = 1`. -/
theorem fexp_YZ (p : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (j : Fin d₁) :
    aeval (fexp g₂ g₃ p w) (YZ K d₀ m j) = 0 := by
  refine flow_YZ (fexp_isNFlow p w).flow j ?_
  simp [fexp_const, YZ, coords]

variable (g₂ g₃) in
/-- **The formal exponential** `exp(z w) = 0 + exp(z w)` (all charts `V`). -/
noncomputable abbrev Exp (w : LieE K d₀ d₁ m) : Var d₀ d₁ m → PowerSeries K :=
  fexp g₂ g₃ 0 w

omit [CharZero K] in
theorem chartAt_zero_gen : chartAt (0 : GPt K d₀ d₁ g₂ g₃) = fun _ => 1 := rfl

/-- `G_a`: `x ↦ ξ z`. -/
theorem Exp_x (w : LieE K d₀ d₁ m) (i : Fin d₀) :
    Exp g₂ g₃ w (.x i) = PowerSeries.C (w.1 i) * PowerSeries.X := by
  have hd : dz (Exp g₂ g₃ w (.x i) - PowerSeries.C (w.1 i) * PowerSeries.X) = 0 := by
    rw [map_sub, (fexp_isNFlow 0 w).flow (.x i), Derivation.leibniz]
    simp [dval]
  have := eq_C_of_derivative_eq_zero (K := K) hd
  rw [map_sub, fexp_const] at this
  simpa [coords, sub_eq_zero] using this

omit [CharZero K] in
theorem derivative_rescale (a : K) (f : PowerSeries K) :
    dz (PowerSeries.rescale a f) = PowerSeries.C a * PowerSeries.rescale a (dz f) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
    PowerSeries.coeff_rescale, PowerSeries.coeff_derivative]
  ring

/-- `G_m`: `y ↦ exp(η z)`. -/
theorem Exp_y (w : LieE K d₀ d₁ m) (j : Fin d₁) :
    Exp g₂ g₃ w (.y j) = PowerSeries.rescale (w.2.1 j) (PowerSeries.exp K) := by
  have h := eq_zero_of_derivative_eq_mul (K := K)
    (f := Exp g₂ g₃ w (.y j) - PowerSeries.rescale (w.2.1 j) (PowerSeries.exp K))
    (a := PowerSeries.C (w.2.1 j)) ?_ ?_
  · exact sub_eq_zero.mp h
  · rw [map_sub, (fexp_isNFlow 0 w).flow (.y j), derivative_rescale, PowerSeries.derivative_exp]
    simp [dval]
    ring
  · rw [map_sub, fexp_const, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale]
    simp [coords]

/-- `G_m`: `z ↦ exp(−η z)`. -/
theorem Exp_z (w : LieE K d₀ d₁ m) (j : Fin d₁) :
    Exp g₂ g₃ w (.z j) = PowerSeries.rescale (-w.2.1 j) (PowerSeries.exp K) := by
  have h := eq_zero_of_derivative_eq_mul (K := K)
    (f := Exp g₂ g₃ w (.z j) - PowerSeries.rescale (-w.2.1 j) (PowerSeries.exp K))
    (a := PowerSeries.C (-w.2.1 j)) ?_ ?_
  · exact sub_eq_zero.mp h
  · rw [map_sub, (fexp_isNFlow 0 w).flow (.z j), derivative_rescale, PowerSeries.derivative_exp]
    simp [dval]
    ring
  · rw [map_sub, fexp_const, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale]
    simp [coords]

/-- `E`: the `V`-coordinate of `P(ζ z)` is `1`. -/
theorem Exp_V (w : LieE K d₀ d₁ m) (k : Fin m) : Exp g₂ g₃ w (.e k 1) = 1 :=
  (fexp_isNFlow 0 w).norm k

omit [CharZero K] in
/-- `E`: `s(0) = t(0) = 0` for `P(ζ z) = (s, 1, t)`. -/
theorem Exp_UW_zero (w : LieE K d₀ d₁ m) (k : Fin m) :
    PowerSeries.constantCoeff (Exp g₂ g₃ w (.e k 0)) = 0 ∧
      PowerSeries.constantCoeff (Exp g₂ g₃ w (.e k 2)) = 0 := by
  simp [fexp_const, coords, rep, O]

/-- `E`: the `V`-chart ODE `s′ = ζ (−1/2 − g₂ s t − (3/2) g₃ t²)`. -/
theorem Exp_U_deriv (w : LieE K d₀ d₁ m) (k : Fin m) :
    dz (Exp g₂ g₃ w (.e k 0)) = PowerSeries.C (w.2.2 k) *
      (-PowerSeries.C (1 / 2) - PowerSeries.C (g₂ k) * Exp g₂ g₃ w (.e k 0) * Exp g₂ g₃ w (.e k 2)
        - PowerSeries.C (3 / 2) * PowerSeries.C (g₃ k) * Exp g₂ g₃ w (.e k 2) ^ 2) := by
  rw [(fexp_isNFlow 0 w).flow (.e k 0)]
  simp only [dval, chartAt_zero_gen, chartPoly, chartV, Exp_V, map_mul, map_sub, map_neg, map_pow,
    map_ofNat, aeval_X, aeval_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have : (PowerSeries.C (3 / 2 : K)) = 3 * PowerSeries.C (1 / 2) := by
    rw [← map_ofNat PowerSeries.C 3, ← map_mul]; norm_num
  rw [this]; ring

/-- `E`: the `V`-chart ODE `t′ = ζ (−6 s² + (g₂/2) t²)`. -/
theorem Exp_W_deriv (w : LieE K d₀ d₁ m) (k : Fin m) :
    dz (Exp g₂ g₃ w (.e k 2)) = PowerSeries.C (w.2.2 k) *
      (-6 * Exp g₂ g₃ w (.e k 0) ^ 2 + PowerSeries.C (g₂ k / 2) * Exp g₂ g₃ w (.e k 2) ^ 2) := by
  rw [(fexp_isNFlow 0 w).flow (.e k 2)]
  simp only [dval, chartAt_zero_gen, chartPoly, chartV, map_mul, map_add, map_neg, map_pow,
    map_ofNat, aeval_X, aeval_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have : (PowerSeries.C (g₂ k / 2)) = PowerSeries.C (1 / 2) * PowerSeries.C (g₂ k) := by
    rw [← map_mul]; ring_nf
  rw [this]; ring

/-- `E`: `F(P(ζ z)) = 0`, i.e. `t − 4 s³ + g₂ s t² + g₃ t³ = 0`. -/
theorem Exp_F (w : LieE K d₀ d₁ m) (k : Fin m) :
    Fv (PowerSeries.C (g₂ k)) (PowerSeries.C (g₃ k)) (fun i => Exp g₂ g₃ w (.e k i)) = 0 := by
  have := fexp_Fk (0 : GPt K d₀ d₁ g₂ g₃) w k
  simpa [Fk, Fv, F, PowerSeries.algebraMap_apply] using this

end Exp

end LSG.ME
