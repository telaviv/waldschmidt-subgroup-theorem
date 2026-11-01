/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LemmaUAlg
import LSG.AuxFun.WpSeries
import LSG.AuxFunV.ExpCoordsN

/-!
# `KS` tools for the vector-extension Lemma U (Stage 5, phase 2)

* **`KS.eval_mvpoly`**: an integer polynomial evaluated at `KS` series (of a common size) is `KS`,
  with constants depending only on the polynomial (`Σ |coefficients|`, total degree).
* `KS.mul_prod`: a series of base `2B` times a product of series of base `B` keeps base `2B`.
* **`ks_zS`**: the `ζ`-increment `Z_c(s) = ζ(z₀ + c s) − ζ(z₀)` at the half period `z₀ = ω₁/2`
  (`Z' = −c ℘(z₀ + c s)`, so the coefficients come from `ks_wpSeries`).
-/

open Finset Filter Topology PeriodPair

noncomputable section

namespace LSG.AuxV

open LSG.Aux

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

/-! ### Integer polynomials in `KS` series -/

/-- **An integer polynomial evaluated at `KS` series.** -/
theorem KS.eval_mvpoly {σ : Type*} (f : MvPolynomial σ ℤ) {A B : ℝ} {e δ : ℕ}
    (g : σ → ℂ → ℂ) (hB : 0 ≤ B) (hA : 1 ≤ A) (hg : ∀ i, KS ι A B e δ (g i)) :
    KS ι ((∑ m ∈ f.support, |(f.coeff m : ℝ)|) * (2 ^ f.totalDegree * A ^ f.totalDegree))
      (2 * B) (e ^ f.totalDegree) δ (fun s => MvPolynomial.aeval (fun i => g i s) f) := by
  classical
  set N := f.totalDegree
  have hfun : (fun s => MvPolynomial.aeval (fun i => g i s) f) =
      fun s => ∑ m ∈ f.support, (f.coeff m : ℂ) * ∏ i ∈ m.support, g i s ^ m i := by
    funext s
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.aeval_monomial, eq_intCast, Finsupp.prod]
  rw [hfun, sum_mul]
  refine KS.sum (ι := ι) _ (by positivity) fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i ≤ N := MvPolynomial.le_totalDegree hm
  have hp := KS.prod_pow (ι := ι) m.support hB (fun i _ => hg i) (fun i => m i)
  have hp' : KS ι (2 ^ N * A ^ N) (2 * B) (e ^ N) δ (fun s => ∏ i ∈ m.support, g i s ^ m i) := by
    refine hp.mono ?_ (by positivity) le_rfl ?_ dvd_rfl
    · rw [prod_pow_eq_pow_sum]
      exact mul_le_mul (pow_le_pow_right₀ one_le_two hdeg) (pow_le_pow_right₀ hA hdeg)
        (by positivity) (by positivity)
    · rw [prod_pow_eq_pow_sum]; exact pow_dvd_pow e hdeg
  simpa using hp'.const_mul (Sz.intCast (ι := ι) (f.coeff m))

/-- Polynomials in differentiable functions are differentiable. -/
lemma differentiableAt_aeval {σ : Type*} (f : MvPolynomial σ ℤ) (g : σ → ℂ → ℂ) {s : ℂ}
    (hg : ∀ i, DifferentiableAt ℂ (g i) s) :
    DifferentiableAt ℂ (fun s => MvPolynomial.aeval (fun i => g i s) f) s := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C]; exact differentiableAt_const _
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hg i)

/-- A series of base `2B` times a product of series of base `B`. -/
theorem KS.mul_prod {α : Type*} (s : Finset α) {A B : ℝ} (hB : 0 ≤ B) {e δ : ℕ}
    {f : ℂ → ℂ} (hf : KS ι A (2 * B) e δ f) {g : α → ℂ → ℂ} {Ag : α → ℝ} {eg : α → ℕ}
    (hg : ∀ a ∈ s, KS ι (Ag a) B (eg a) δ (g a)) :
    KS ι (2 ^ s.card * A * ∏ a ∈ s, Ag a) (2 * B) (e * ∏ a ∈ s, eg a) δ
      (fun x => f x * ∏ a ∈ s, g a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert a s ha ih =>
    have h := (ih fun b hb => hg b (mem_insert_of_mem hb)).mul_basic hB (hg a (mem_insert_self a s))
    simp only [prod_insert ha, card_insert_of_notMem ha]
    convert h using 1
    · rw [pow_succ]; ring
    · ring
    · funext x; simp only [Pi.mul_apply]; ring

/-! ### The `ζ`-increment at the half period -/

variable (L : PeriodPair)

/-- `Z_c(s) = ζ(z₀ + c s) − ζ(z₀)`. -/
def zS (c s : ℂ) : ℂ := LSG.Weierstrass.zeta L (zh L + c * s) - LSG.Weierstrass.zeta L (zh L)

lemma zS_zero (c : ℂ) : zS L c 0 = 0 := by unfold zS; rw [mul_zero, add_zero, sub_self]

lemma hasDerivAt_zS (c : ℂ) {s : ℂ} (hs : zh L + c * s ∉ L.lattice) :
    HasDerivAt (zS L c) (-(c * wpP L c s)) s := by
  have h1 := LSG.Weierstrass.hasDerivAt_zeta L hs
  have h2 : HasDerivAt (fun s : ℂ => zh L + c * s) c s := by
    simpa using ((hasDerivAt_id s).const_mul c).const_add (zh L)
  have := (h1.comp s h2).sub_const (LSG.Weierstrass.zeta L (zh L))
  convert this using 1
  · rfl
  · change -(c * ℘[L] (zh L + c * s)) = _; ring

lemma analyticAt_zS (c : ℂ) : AnalyticAt ℂ (zS L c) 0 := by
  have hopen : ∀ᶠ s in 𝓝 (0 : ℂ), zh L + c * s ∉ L.lattice := eventually_notMem L c
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hopen
  refine DifferentiableOn.analyticAt (s := Metric.ball 0 r) (fun s hs => ?_)
    (Metric.ball_mem_nhds 0 hr)
  exact (hasDerivAt_zS L c (hball s hs)).differentiableAt.differentiableWithinAt

lemma deriv_zS (c : ℂ) : deriv (zS L c) =ᶠ[𝓝 0] fun s => -c * wpP L c s := by
  filter_upwards [eventually_notMem L c] with s hs
  rw [(hasDerivAt_zS L c hs).deriv]; ring

/-- **Sizes of the Taylor coefficients of the `ζ`-increment.** -/
theorem ks_zS {c : ℂ} {Hc A B : ℝ} {E : ℕ} (hc : Sz ι Hc E c)
    (hP : KS ι A B E (E ^ 2) (wpP L c)) (hB : Hc ≤ B) (hA : 0 ≤ A) :
    KS ι A B 1 (E ^ 2) (zS L c) := by
  refine ⟨analyticAt_zS L c, fun j => ?_⟩
  rcases j with _ | j
  · have : tco 0 (zS L c) = 0 := by simp [tco, zS_zero]
    rw [this]; exact (Sz.zero _).mono_le (by simpa using hA)
  · have hj : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hrec : tco (j + 1) (zS L c) = -c * tco j (wpP L c) / (j + 1 : ℕ) := by
      have h := tco_deriv (zS L c) j
      rw [tco_congr (deriv_zS L c), tco_const_mul] at h
      field_simp
      push_cast at h ⊢
      linear_combination -h
    rw [hrec]
    have h1 := ((hc.neg.mul (hP.2 j)).div_nat (Nat.succ_ne_zero j))
    refine (by simpa [neg_mul] using h1 :
      Sz ι (Hc * (A * B ^ j) / (j + 1 : ℕ)) (E * (E * (E ^ 2) ^ j * j.factorial) * (j + 1))
        (-c * tco j (wpP L c) / (j + 1 : ℕ))).mono ?_ ?_
    · have hHc : 0 ≤ Hc := hc.nonneg
      have hB0 : 0 ≤ B := hHc.trans hB
      have hpos : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_pos j
      calc Hc * (A * B ^ j) / (j + 1 : ℕ) ≤ Hc * (A * B ^ j) :=
            div_le_self (by positivity) hpos
        _ ≤ B * (A * B ^ j) := by gcongr
        _ = A * B ^ (j + 1) := by ring
    · refine ⟨1, ?_⟩
      rw [Nat.factorial_succ]; ring

end LSG.AuxV
