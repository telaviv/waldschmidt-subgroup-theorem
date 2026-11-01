/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LemmaUBounds
import LSG.AuxFun.Polarize

/-!
# Lemma U (W_UPGRADE §1.2, multiplicity along `W`), at every point of `Y(S)` (Stage 3, D3b)

Data (`LUData`): generators `y_j ∈ Λ(G)` with coordinates in a number field `K` (via `ι : K → ℂ`),
cone representatives `X₀_{j,k}` of `exp_{E_k}((y_j)_k)`, a basis `w_r` of `W` with coordinates in `K`,
`g₂, g₃, e₁ = ℘(ω₁/2)` in `K`, all of size `(H, d)`.

**`lemmaU_core`.** There is `c₀` such that: if `Ψ = Σ_l p_l M_l` (monomials of elliptic degree `D`,
`α ≤ A₀`, `β ≤ A₁`, `|p_l| ≤ e^B`) satisfies `|Ψ| ≤ e^{−U}` on `V ∩ B(0, c₀ S)` and
`c₀ (B + log(L+1) + (A₀+1) log(S+1) + (A₁+1) S + (D+1) S² + (T+1) log(T+2)) ≤ U`, then `Ψ` vanishes
to order `≥ T` along `W` at every `Σ hⱼ yⱼ`, `0 ≤ hⱼ ≤ S` (`LSG.W88.VanishAlong`).

Proof (per point `t` and grid direction `v = Σ c_r w_r`, `c_r ≤ T`): `F_t = Π R_k^D · Ψ(t + s v)`
(`Fpoly_eq`) with `R_k(0) ≠ 0`; the Taylor coefficients of `F_t` lie in `K` with explicit sizes
(`ks_gfac`, `KS.poly`); Cauchy on the disc of radius `ρ₁/(1+|v|)` with the chart lower bound
(`exists_chart`) and Liouville (`tco_eq_zero_of_small`) kill them; division by the unit
(`iteratedDeriv_eq_zero_of_mul`); polarization (`iteratedDeriv_line_eq_zero_of_span`).
-/

open Complex Finset LSG.Elliptic LSG.Weierstrass LSG.W88 PeriodPair
open scoped ContDiff

noncomputable section

namespace LSG.W88

/-- **Analytic multiplicity `≥ T` along `W` at `y`**: all derivatives of order `< T` of
`s ↦ Φ(y + s w)` vanish at `0`, for every `w ∈ W`. -/
def VanishAlong {E : Type*} [AddCommGroup E] [Module ℂ E] (Φ : E → ℂ) (W : Submodule ℂ E)
    (T : ℝ) (y : E) : Prop :=
  ∀ w ∈ W, ∀ k : ℕ, (k : ℝ) < T → iteratedDeriv k (fun s : ℂ => Φ (y + s • w)) 0 = 0

end LSG.W88

namespace LSG.Aux

variable {d0 d1 m : ℕ}
variable {K : Type*} [Field K] [NumberField K]

/-- The arithmetic data of Lemma U. -/
structure LUData (Ls : Fin m → PeriodPair) (ι : K →+* ℂ) (μ τ : ℕ) where
  y : Fin μ → Tan d0 d1 m
  w : Fin τ → Tan d0 d1 m
  X₀ : Fin μ → Fin m → Fin 3 → ℂ
  γ₂ : Fin m → K
  γ₃ : Fin m → K
  H : ℝ
  d : ℕ
  hH : 1 ≤ H
  hd : 1 ≤ d
  hγ₂ : ∀ k, ι (γ₂ k) = (Ls k).g₂
  hγ₃ : ∀ k, ι (γ₃ k) = (Ls k).g₃
  ha : ∀ j i, Sz ι H d ((y j).1 i)
  hb : ∀ j i, Sz ι H d (exp ((y j).2.1 i))
  hX₀ : ∀ j k, IsRep (Ls k) ((y j).2.2 k) (X₀ j k)
  hX₀s : ∀ j k i, Sz ι H d (X₀ j k i)
  hw0 : ∀ r i, Sz ι H d ((w r).1 i)
  hw1 : ∀ r i, Sz ι H d ((w r).2.1 i)
  hw2 : ∀ r k, Sz ι H d ((w r).2.2 k)
  he₁ : ∀ k, Sz ι H d (℘[Ls k] (zh (Ls k)))
  hg₂ : ∀ k, Sz ι H d ((Ls k).g₂ / 2)

lemma small_of_bounds {M ρ Q U a₁ a₂ a₃ : ℝ} {deg k : ℕ} (hM : M ≤ Real.exp a₁ * Real.exp (-U))
    (hρ0 : 0 < ρ) (hρ : (1 / ρ) ^ k ≤ Real.exp a₂) (hQ0 : 0 ≤ Q) (hQ : Q ≤ Real.exp a₃)
    (h : a₁ + a₂ + deg * a₃ < U) : M / ρ ^ k * Q ^ deg < 1 := by
  have h1 : M / ρ ^ k ≤ Real.exp (a₁ - U + a₂) := by
    rw [div_eq_mul_one_div, ← one_div_pow, Real.exp_add, sub_eq_add_neg, Real.exp_add]
    exact mul_le_mul hM hρ (by positivity) (by positivity)
  have h2 : Q ^ deg ≤ Real.exp (deg * a₃) := by
    calc Q ^ deg ≤ Real.exp a₃ ^ deg := pow_le_pow_left₀ hQ0 hQ deg
      _ = Real.exp (deg * a₃) := by rw [← Real.exp_nat_mul]
  have h3 : M / ρ ^ k * Q ^ deg ≤ Real.exp (a₁ + a₂ + deg * a₃ - U) := by
    by_cases hneg : M / ρ ^ k < 0
    · calc M / ρ ^ k * Q ^ deg ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
        _ ≤ _ := (Real.exp_pos _).le
    have hneg' : 0 ≤ M / ρ ^ k := not_lt.mp hneg
    calc M / ρ ^ k * Q ^ deg ≤ Real.exp (a₁ - U + a₂) * Real.exp (deg * a₃) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Real.exp (a₁ + a₂ + deg * a₃ - U) := by rw [← Real.exp_add]; ring_nf
  calc M / ρ ^ k * Q ^ deg ≤ Real.exp (a₁ + a₂ + deg * a₃ - U) := h3
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

end LSG.Aux
