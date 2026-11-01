/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Chart
import LSG.AuxFun.LemmaUAlg

/-!
# Lemma U: the function `F_t` and its identity with `Ψ(t + s v)` (Stage 3, D3b)

For `t, v ∈ T_G`, representatives `X'_k` of `exp_{E_k}(t_k + z₀)` and law indices `κ_k`, the
*basic factors* (`gfac`) are
* `t.1 i + v.1 i · s` (`G_a`), `e^{t.2.1 i} e^{v.2.1 i · s}` (`G_m`),
* `law_{κ_k}(X'_k, ξ_k(s))_{cidx c}` with `ξ_k(s) = (℘_k(z₀ + v_k s), ℘'_k(z₀ + v_k s), 1)` (elliptic),
and `F_t(s) = Σ_l p_l Π_f gfac_f(s)^{n_{l,f}}` (`Fpoly`), `n = Mono.expo`.

* `Mono.eval_eq_prod`: monomials as products over `Fct = Fin d₀ ⊕ Fin d₁ ⊕ (Fin m × Fin 3)`.
* `lawk_eq_smul_ellV`: `law(X', ξ(s)) = R(s) · ellV(t_k + v_k s)` with
  `R = law_j / ellV_j` for any chart index `j` with `ellV_j ≠ 0` (`R = 0` if the law degenerates).
* **`Fpoly_eq`**: `F_t(s) = Π_k R_k(s)^D · Ψ(t + s v)`, `Ψ = Σ_l p_l M_l`.
* **`tco_eq_zero_of_small`**: Cauchy + Liouville for a `KS` function.
-/

open Complex Finset LSG.Elliptic LSG.Weierstrass LSG.W88 PeriodPair

noncomputable section

namespace LSG.Aux

variable {d0 d1 m D : ℕ}

/-- Index set of the coordinate functions of `exp_G`. -/
abbrev Fct (d0 d1 m : ℕ) := Fin d0 ⊕ Fin d1 ⊕ (Fin m × Fin 3)

/-- The exponent vector of a monomial. -/
def Mono.expo (μ : Mono d0 d1 m D) : Fct d0 d1 m → ℕ
  | .inl i => μ.α i
  | .inr (.inl i) => μ.β i
  | .inr (.inr kc) => μ.γ kc.1 kc.2

/-- The coordinate functions of `exp_G`. -/
def coordF (Ls : Fin m → PeriodPair) : Fct d0 d1 m → Tan d0 d1 m → ℂ
  | .inl i => fun p => p.1 i
  | .inr (.inl i) => fun p => exp (p.2.1 i)
  | .inr (.inr kc) => fun p => ellW (Ls kc.1) kc.2 (p.2.2 kc.1)

lemma Mono.eval_eq_prod (Ls : Fin m → PeriodPair) (μ : Mono d0 d1 m D) (p : Tan d0 d1 m) :
    μ.eval Ls p = ∏ f, coordF Ls f p ^ μ.expo f := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_prod_type, Mono.eval]
  simp only [coordF, Mono.expo]
  ring

/-- `ellW` index `c` sits at cone index `cidx c`. -/
def cidx : Fin 3 → Fin 3 := ![2, 0, 1]

lemma ellV_cidx (L : PeriodPair) (u : ℂ) (c : Fin 3) : ellV L u (cidx c) = ellW L c u := by
  fin_cases c <;> rfl

/-- The second argument `ξ(s)` of the law. -/
def xiV (L : PeriodPair) (c s : ℂ) : Fin 3 → ℂ := ![wpP L c s, wpQ L c s, 1]

/-- The basic factors of `F_t`. -/
def gfac (Ls : Fin m → PeriodPair) (t v : Tan d0 d1 m) (κ : Fin m → Fin 2)
    (X' : Fin m → Fin 3 → ℂ) : Fct d0 d1 m → ℂ → ℂ
  | .inl i => fun s => t.1 i + v.1 i * s
  | .inr (.inl i) => fun s => exp (t.2.1 i) * exp (v.2.1 i * s)
  | .inr (.inr kc) => fun s => lawk (κ kc.1) (Ls kc.1).g₂ (Ls kc.1).g₃ (X' kc.1)
      (xiV (Ls kc.1) (v.2.2 kc.1) s) (cidx kc.2)

/-- `F_t`. -/
def Fpoly (Ls : Fin m → PeriodPair) (t v : Tan d0 d1 m) (κ : Fin m → Fin 2)
    (X' : Fin m → Fin 3 → ℂ) {L : ℕ} (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ) (s : ℂ) : ℂ :=
  ∑ l, (p l : ℂ) * ∏ f, gfac Ls t v κ X' f s ^ (μs l).expo f

/-- `Ψ = Σ_l p_l M_l`. -/
def Psi (Ls : Fin m → PeriodPair) {L : ℕ} (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ)
    (x : Tan d0 d1 m) : ℂ :=
  ∑ l, (p l : ℂ) * (μs l).eval Ls x

/-- **The law against the chart.** -/
lemma lawk_eq_smul_ellV (L : PeriodPair) {u c s : ℂ} {X' : Fin 3 → ℂ}
    (hX' : IsRep L (u + zh L) X') (hs : zh L + c * s ∉ L.lattice) (κ : Fin 2) {j : Fin 3}
    (hj : ellV L (u + c * s) j ≠ 0) :
    lawk κ L.g₂ L.g₃ X' (xiV L c s) =
      (lawk κ L.g₂ L.g₃ X' (xiV L c s) j / ellV L (u + c * s) j) • ellV L (u + c * s) := by
  classical
  by_cases h0 : lawk κ L.g₂ L.g₃ X' (xiV L c s) = 0
  · rw [h0]; simp
  have hxi : IsRep L (zh L + c * s) (xiV L c s) := isRep_xi L hs
  have hrep : toPoint L.g₂ L.g₃ (lawk κ L.g₂ L.g₃ X' (xiV L c s)) = expE L (u + c * s) := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hΔ := discr_ne_zero L
    have hsum : toPoint L.g₂ L.g₃ (lawk κ L.g₂ L.g₃ X' (xiV L c s)) =
        toPoint L.g₂ L.g₃ X' + toPoint L.g₂ L.g₃ (xiV L c s) := by
      fin_cases κ
      · exact toPoint_law₁ h2 hΔ hX'.2.1 hxi.2.1 hX'.1 hxi.1 h0
      · exact toPoint_law₂ h2 hΔ hX'.2.1 hxi.2.1 hX'.1 hxi.1 h0
    rw [hsum, hX'.2.2, hxi.2.2]
    refine (expE_add L _ _).symm.trans ?_
    have : u + zh L + (zh L + c * s) = u + c * s + L.ω₁ := by simp only [zh]; ring
    rw [this, expE_add_mem L _ L.ω₁_mem_lattice]
  have hV := isRep_ellV L (u + c * s)
  obtain ⟨r, -, hr⟩ := (toPoint_eq_iff two_ne_zero (discr_ne_zero L)
    (Fv_lawk hX'.2.1 hxi.2.1 κ) hV.2.1 h0 hV.1).mp (hrep.trans hV.2.2.symm)
  have hrj : lawk κ L.g₂ L.g₃ X' (xiV L c s) j / ellV L (u + c * s) j = r := by
    rw [hr, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hj, mul_one]
  rw [hrj]; exact hr

/-- **`F_t = Π_k R_k^D · Ψ(t + s v)`.** -/
theorem Fpoly_eq (Ls : Fin m → PeriodPair) (t v : Tan d0 d1 m) (κ : Fin m → Fin 2)
    (X' : Fin m → Fin 3 → ℂ) (hX' : ∀ k, IsRep (Ls k) (t.2.2 k + zh (Ls k)) (X' k))
    {L : ℕ} (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ) (j : Fin m → Fin 3) {s : ℂ}
    (hs : ∀ k, zh (Ls k) + v.2.2 k * s ∉ (Ls k).lattice)
    (hj : ∀ k, ellV (Ls k) (t.2.2 k + v.2.2 k * s) (j k) ≠ 0) :
    Fpoly Ls t v κ X' μs p s = (∏ k, (lawk (κ k) (Ls k).g₂ (Ls k).g₃ (X' k)
        (xiV (Ls k) (v.2.2 k) s) (j k) / ellV (Ls k) (t.2.2 k + v.2.2 k * s) (j k)) ^ D) *
      Psi Ls μs p (t + s • v) := by
  set R : Fin m → ℂ := fun k => lawk (κ k) (Ls k).g₂ (Ls k).g₃ (X' k)
    (xiV (Ls k) (v.2.2 k) s) (j k) / ellV (Ls k) (t.2.2 k + v.2.2 k * s) (j k)
  have hfac : ∀ f : Fct d0 d1 m, gfac Ls t v κ X' f s =
      (match f with
        | .inl _ => 1
        | .inr (.inl _) => 1
        | .inr (.inr kc) => R kc.1) * coordF Ls f (t + s • v) := by
    intro f
    rcases f with i | i | ⟨k, c⟩
    · simp [gfac, coordF]; ring
    · simp [gfac, coordF, Complex.exp_add]; ring_nf
    · simp only [gfac, coordF]
      have := congrFun (lawk_eq_smul_ellV (Ls k) (hX' k) (hs k) (κ k) (hj k)) (cidx c)
      rw [this, Pi.smul_apply, smul_eq_mul, ellV_cidx]
      simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, R]
      ring_nf
  unfold Fpoly Psi
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [Mono.eval_eq_prod]
  simp_rw [hfac, mul_pow, prod_mul_distrib]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [one_pow, prod_const_one, one_mul, Mono.expo]
  have hD : ∀ k, ∏ c : Fin 3, R k ^ (μs l).γ k c = R k ^ D := fun k => by
    rw [prod_pow_eq_pow_sum, (μs l).hγ k]
  simp only [hD]
  ring

/-! ### Cauchy + Liouville -/

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

/-- **Small Taylor coefficients of bounded size vanish.** -/
theorem tco_eq_zero_of_small {F : ℂ → ℂ} {A B : ℝ} {e δ : ℕ} (hF : KS ι A B e δ F)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (he : 1 ≤ e) (hδ : 1 ≤ δ) {ρ M : ℝ} (hρ : 0 < ρ)
    (hdc : DiffContOnCl ℂ F (Metric.ball 0 ρ)) (hM : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖F z‖ ≤ M)
    {k : ℕ} (hsmall : M / ρ ^ k * ((e * δ ^ k * k.factorial : ℕ) * (A * B ^ k)) ^
      Module.finrank ℚ K < 1) : tco k F = 0 := by
  by_contra h0
  have hsz := hF.2 k
  have hAB : 1 ≤ A * B ^ k := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hB)
  have hd : 1 ≤ e * δ ^ k * k.factorial :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hL := hsz.one_le_norm_mul h0 hAB hd
  have hC := norm_tco_le hρ hdc hM k
  have hpos : 0 ≤ (((e * δ ^ k * k.factorial : ℕ) : ℝ) * (A * B ^ k)) ^ Module.finrank ℚ K := by
    positivity
  have := mul_le_mul_of_nonneg_right hC hpos
  linarith

end LSG.Aux
