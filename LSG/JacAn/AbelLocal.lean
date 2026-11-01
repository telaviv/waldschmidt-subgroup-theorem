/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.EulerJacobi
import LSG.JacAn.Branch

/-!
# Abel's theorem, locally (ABVAR §2.2 a2)

Let `c_t(x) = Σ_{j ≤ m} c_j(t) x^j` be a holomorphic family of polynomials and `R_t = f − c_t²`. Suppose the
points `x_i(t)` (`i ∈ s`) are roots of `R_t`, differentiable at `t₀`, and at `t₀` they are *all* the roots of
`R_{t₀}`, simple (`#s = deg R_{t₀}`). The points `(x_i(t), c_t(x_i(t)))` are the intersections of `y² = f(x)` with
`y = c_t(x)`.

* `deriv_root_eq` (implicit differentiation): `R'(x_i) x_i' = 2 c(x_i) δc(x_i)`, `δc = ∂_t c`.
* `abel_local`: `Σ_i x_i^k x_i' / y_i = 0` for `k + m + 2 ≤ #s` (Euler–Jacobi with `q = 2 X^k δc`).
  For `deg f = 2g + 1` and `k ≤ g − 1` this holds in both regimes `m ≤ g` (`#s = 2g + 1`) and `m ≥ g + 1`
  (`#s = 2m`).
* `hasDerivAt_abelSum`: if each point moves on a local branch `B_i`, the Abel sum `Σ_i I_i(x_i(t))` has derivative
  `0` at `t₀`. This is the infinitesimal form of "the divisors cut out by `y = c_t(x)` are linearly equivalent",
  i.e. of exp being a local homomorphism.
-/

noncomputable section

open Polynomial Finset Filter Topology Metric

namespace LSG.JacAn

variable {m : ℕ}

/-- The polynomial `c_t = Σ_{j ≤ m} c_j(t) X^j`. -/
def cPoly (c : Fin (m + 1) → ℂ → ℂ) (t : ℂ) : ℂ[X] := ∑ j : Fin (m + 1), C (c j t) * X ^ (j : ℕ)

/-- The polynomial `Σ_{j ≤ m} a_j X^j` (used for `δc = ∂_t c_t`). -/
def coeffPoly (a : Fin (m + 1) → ℂ) : ℂ[X] := ∑ j : Fin (m + 1), C (a j) * X ^ (j : ℕ)

lemma cPoly_eq (c : Fin (m + 1) → ℂ → ℂ) (t : ℂ) : cPoly c t = coeffPoly (fun j => c j t) := rfl

lemma natDegree_coeffPoly_le (a : Fin (m + 1) → ℂ) : (coeffPoly a).natDegree ≤ m := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.lt_succ_iff.mp j.2

lemma eval_coeffPoly (a : Fin (m + 1) → ℂ) (x : ℂ) :
    (coeffPoly a).eval x = ∑ j : Fin (m + 1), a j * x ^ (j : ℕ) := by
  simp [coeffPoly, eval_finsetSum]

lemma eval_derivative_coeffPoly (a : Fin (m + 1) → ℂ) (x : ℂ) :
    (derivative (coeffPoly a)).eval x = ∑ j : Fin (m + 1), a j * ((j : ℕ) * x ^ ((j : ℕ) - 1)) := by
  simp only [coeffPoly, derivative_sum, eval_finsetSum, derivative_C_mul_X_pow, eval_mul, eval_C,
    eval_pow, eval_X]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- The derivative of `t ↦ c_t(x(t))`: `δc(x) + c'(x) x'`. -/
lemma hasDerivAt_eval_cPoly {c : Fin (m + 1) → ℂ → ℂ} {c' : Fin (m + 1) → ℂ} {x : ℂ → ℂ} {x' t₀ : ℂ}
    (hc : ∀ j, HasDerivAt (c j) (c' j) t₀) (hx : HasDerivAt x x' t₀) :
    HasDerivAt (fun t => (cPoly c t).eval (x t))
      ((coeffPoly c').eval (x t₀) + (derivative (cPoly c t₀)).eval (x t₀) * x') t₀ := by
  have h : HasDerivAt (fun t => ∑ j : Fin (m + 1), c j t * x t ^ (j : ℕ))
      (∑ j : Fin (m + 1), (c' j * x t₀ ^ (j : ℕ) + c j t₀ * ((j : ℕ) * x t₀ ^ ((j : ℕ) - 1) * x')))
      t₀ := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact (hc j).mul (hx.pow _)
  convert h using 1
  · funext t; rw [cPoly_eq, eval_coeffPoly]
  · rw [cPoly_eq, eval_coeffPoly, eval_derivative_coeffPoly, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring

/-- **Implicit differentiation**: if `x(t)` is a root of `R_t = f − c_t²` for `t` near `t₀`, then
`R_{t₀}'(x) x' = 2 c_{t₀}(x) δc(x)`. -/
theorem deriv_root_eq (f : ℂ[X]) {c : Fin (m + 1) → ℂ → ℂ} {c' : Fin (m + 1) → ℂ} {x : ℂ → ℂ}
    {x' t₀ : ℂ} (hc : ∀ j, HasDerivAt (c j) (c' j) t₀) (hx : HasDerivAt x x' t₀)
    (hroot : ∀ᶠ t in 𝓝 t₀, (f - cPoly c t ^ 2).eval (x t) = 0) :
    (derivative (f - cPoly c t₀ ^ 2)).eval (x t₀) * x' =
      2 * (cPoly c t₀).eval (x t₀) * (coeffPoly c').eval (x t₀) := by
  have hF : HasDerivAt (fun t => f.eval (x t) - ((cPoly c t).eval (x t)) ^ 2)
      ((derivative f).eval (x t₀) * x' - 2 * (cPoly c t₀).eval (x t₀) *
        ((coeffPoly c').eval (x t₀) + (derivative (cPoly c t₀)).eval (x t₀) * x')) t₀ := by
    have h1 := (f.hasDerivAt (x t₀)).comp t₀ hx
    have h2 := (hasDerivAt_eval_cPoly hc hx).pow 2
    convert h1.sub h2 using 1
    · funext t; simp
    · norm_num
  have h0 : HasDerivAt (fun t => f.eval (x t) - ((cPoly c t).eval (x t)) ^ 2) 0 t₀ := by
    refine (hasDerivAt_const t₀ (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hroot] with t ht
    simpa using ht
  have := hF.unique h0
  rw [derivative_sub, derivative_sq, eval_sub, eval_mul, eval_mul, eval_C]
  linear_combination this

/-- **Abel's theorem, locally.** Along the family of intersections of `y² = f(x)` with `y = c_t(x)`,
`Σ_i x_i^k x_i' / y_i = 0` at `t₀` whenever `k + m + 2 ≤ #s` (`y_i = c_{t₀}(x_i(t₀))`). -/
theorem abel_local (f : ℂ[X]) {ι : Type*} (s : Finset ι)
    {c : Fin (m + 1) → ℂ → ℂ} {c' : Fin (m + 1) → ℂ} {x : ι → ℂ → ℂ} {x' : ι → ℂ} {t₀ : ℂ}
    (hc : ∀ j, HasDerivAt (c j) (c' j) t₀) (hx : ∀ i ∈ s, HasDerivAt (x i) (x' i) t₀)
    (hroot : ∀ i ∈ s, ∀ᶠ t in 𝓝 t₀, (f - cPoly c t ^ 2).eval (x i t) = 0)
    (hinj : Set.InjOn (fun i => x i t₀) s) (hR : f - cPoly c t₀ ^ 2 ≠ 0)
    (hdeg : (f - cPoly c t₀ ^ 2).natDegree = #s)
    (hy : ∀ i ∈ s, (cPoly c t₀).eval (x i t₀) ≠ 0) {k : ℕ} (hk : k + m + 2 ≤ #s) :
    ∑ i ∈ s, x i t₀ ^ k * x' i / (cPoly c t₀).eval (x i t₀) = 0 := by
  classical
  set R := f - cPoly c t₀ ^ 2 with hRdef
  have hroot₀ : ∀ i ∈ s, R.eval (x i t₀) = 0 := fun i hi => (hroot i hi).self_of_nhds
  set q : ℂ[X] := C 2 * X ^ k * coeffPoly c' with hq
  have hqdeg : q.natDegree + 2 ≤ #s := by
    have : q.natDegree ≤ k + m := by
      refine (natDegree_mul_le).trans (add_le_add ?_ (natDegree_coeffPoly_le c'))
      refine (natDegree_mul_le).trans ?_
      simp
    omega
  have hEJ := eulerJacobi_roots (q := q) hinj hdeg hroot₀ hqdeg
  rw [← hEJ]
  refine sum_congr rfl fun i hi => ?_
  have hR' : (derivative R).eval (x i t₀) ≠ 0 :=
    eval_derivative_ne_zero_of_roots hR hinj hdeg hroot₀ hi
  have hd := deriv_root_eq f hc (hx i hi) (hroot i hi)
  have hx' : x' i = 2 * (cPoly c t₀).eval (x i t₀) * (coeffPoly c').eval (x i t₀) /
      (derivative R).eval (x i t₀) := by
    rw [eq_div_iff hR', mul_comm]; exact hd
  rw [hx', hq]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  field_simp [hy i hi]

/-- **The Abel sum is stationary along the family.** If moreover each `x_i(t₀)` lies in the disc of a local branch
`B i` of `y² = f(x)` with `B_i.Y(x_i(t₀)) = c_{t₀}(x_i(t₀))`, and `g − 1 + m + 2 ≤ #s`, then
`d/dt Σ_i I_i(x_i(t)) = 0` at `t₀`. -/
theorem hasDerivAt_abelSum (f : ℂ[X]) {g : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → LocalBranch f g)
    {c : Fin (m + 1) → ℂ → ℂ} {c' : Fin (m + 1) → ℂ} {x : ι → ℂ → ℂ} {x' : ι → ℂ} {t₀ : ℂ}
    (hc : ∀ j, HasDerivAt (c j) (c' j) t₀) (hx : ∀ i ∈ s, HasDerivAt (x i) (x' i) t₀)
    (hroot : ∀ i ∈ s, ∀ᶠ t in 𝓝 t₀, (f - cPoly c t ^ 2).eval (x i t) = 0)
    (hinj : Set.InjOn (fun i => x i t₀) s) (hR : f - cPoly c t₀ ^ 2 ≠ 0)
    (hdeg : (f - cPoly c t₀ ^ 2).natDegree = #s)
    (hball : ∀ i ∈ s, x i t₀ ∈ ball (B i).x₀ (B i).r)
    (hbranch : ∀ i ∈ s, (B i).Y (x i t₀) = (cPoly c t₀).eval (x i t₀))
    (hg : g + m + 1 ≤ #s) :
    HasDerivAt (fun t => ∑ i ∈ s, (B i).I (x i t)) 0 t₀ := by
  have hy : ∀ i ∈ s, (cPoly c t₀).eval (x i t₀) ≠ 0 := fun i hi =>
    hbranch i hi ▸ (B i).Y_ne _ (hball i hi)
  have h := HasDerivAt.fun_sum (u := s) fun i hi => ((B i).I_deriv _ (hball i hi)).scomp t₀ (hx i hi)
  have hsum : ∑ i ∈ s, x' i • omegaVec g (B i).Y (x i t₀) = 0 := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, omegaVec, Pi.zero_apply]
    have hk : (k : ℕ) + m + 2 ≤ #s := by have := k.2; omega
    rw [← abel_local f s hc hx hroot hinj hR hdeg hy hk]
    refine sum_congr rfl fun i hi => ?_
    rw [hbranch i hi]; ring
  rw [hsum] at h
  exact h

/-- **Abel's theorem along a connected family.** If the hypotheses of `hasDerivAt_abelSum` hold at every
parameter of a connected open set `U ⊆ ℂ`, the Abel sum `Σ_i I_i(x_i(t))` is constant on `U`. -/
theorem abelSum_const (f : ℂ[X]) {g : ℕ} {ι : Type*} (s : Finset ι) (B : ι → LocalBranch f g)
    {U : Set ℂ} (hU : IsOpen U) (hU' : IsPreconnected U)
    {c : Fin (m + 1) → ℂ → ℂ} {c' : ℂ → Fin (m + 1) → ℂ} {x : ι → ℂ → ℂ} {x' : ℂ → ι → ℂ}
    (hc : ∀ t ∈ U, ∀ j, HasDerivAt (c j) (c' t j) t)
    (hx : ∀ t ∈ U, ∀ i ∈ s, HasDerivAt (x i) (x' t i) t)
    (hroot : ∀ t ∈ U, ∀ i ∈ s, (f - cPoly c t ^ 2).eval (x i t) = 0)
    (hinj : ∀ t ∈ U, Set.InjOn (fun i => x i t) s) (hR : ∀ t ∈ U, f - cPoly c t ^ 2 ≠ 0)
    (hdeg : ∀ t ∈ U, (f - cPoly c t ^ 2).natDegree = #s)
    (hball : ∀ t ∈ U, ∀ i ∈ s, x i t ∈ ball (B i).x₀ (B i).r)
    (hbranch : ∀ t ∈ U, ∀ i ∈ s, (B i).Y (x i t) = (cPoly c t).eval (x i t))
    (hg : g + m + 1 ≤ #s) {t₁ t₂ : ℂ} (h₁ : t₁ ∈ U) (h₂ : t₂ ∈ U) :
    ∑ i ∈ s, (B i).I (x i t₁) = ∑ i ∈ s, (B i).I (x i t₂) := by
  have hD : ∀ t ∈ U, HasDerivAt (fun t => ∑ i ∈ s, (B i).I (x i t)) 0 t := fun t ht =>
    hasDerivAt_abelSum f s B (hc t ht) (hx t ht)
      (fun i hi => by filter_upwards [hU.mem_nhds ht] with t' ht' using hroot t' ht' i hi)
      (hinj t ht) (hR t ht) (hdeg t ht) (hball t ht) (hbranch t ht) hg
  exact hU.is_const_of_deriv_eq_zero hU' (fun t ht => (hD t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hD t ht).deriv) h₁ h₂

end LSG.JacAn
