/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.ContinuationW

/-!
# The periods are Abel integrals along paths (input to a5)

* `IsAbelAlongW`: the local property of the (mixed-chart) Abel integral along a path (`exists_abelAlongW`).
* `IsAbelAlongW.continuousOn`, `IsAbelAlongW.hasDerivAt`: `A` is continuous, and differentiable with derivative
  `u' · (u^k / Yp)` wherever `Yp ≠ 0` (in both chart types).
* `IsAbelAlongW.curveIntegral`: if the zeros of `Yp` are countable, `(A 1)_j = ∫ᶜ x^j dx/y` along the path, for
  piecewise-`C¹` data (derivatives on `(0, 1)` only; the endpoints may be singular, as for `liftPath`).
* **`abelAlong_liftPath`**: for the model `y² = 4x⁵ + 1` (`f₅`), the Abel integral along `[ζ^e]ℓ` exists and
  `(A 1)_j = ((−1)^j/5)(ζ^e)^{j+1} B((j+1)/5, (j+1)/5)`; so the periods of `cycleE e` are differences of Abel integrals
  along paths with the same endpoints (`period_eq_abelAlong`).
-/

noncomputable section

open Polynomial Metric Set Filter Topology MeasureTheory

namespace LSG.JacAn

variable {f : ℂ[X]} {g : ℕ} {u Yp : ℝ → ℂ}

/-- The local property of the mixed-chart Abel integral along `(u, Yp)`. -/
def IsAbelAlongW (f : ℂ[X]) (g : ℕ) (u Yp : ℝ → ℂ) (A : ℝ → (Fin g → ℂ)) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∃ C : PathChart f g, ∃ ε > 0,
    ∀ t ∈ ball s ε ∩ Icc 0 1, C.Carries u Yp t ∧
      ∀ t' ∈ ball s ε ∩ Icc 0 1, A t' - A t = C.F u Yp t' - C.F u Yp t

lemma PathChart.continuousWithinAt_F (C : PathChart f g) {s : ℝ}
    (hu : ContinuousWithinAt u (Icc 0 1) s) (hY : ContinuousWithinAt Yp (Icc 0 1) s)
    (hC : C.Carries u Yp s) : ContinuousWithinAt (C.F u Yp) (Icc 0 1) s := by
  cases C with
  | br B => exact ((B.I_an _ hC.1).continuousAt).comp_continuousWithinAt hu
  | we W => exact ((W.I_an _ hC.1).continuousAt).comp_continuousWithinAt hY

theorem IsAbelAlongW.continuousOn {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlongW f g u Yp A)
    (hu : ContinuousOn u (Icc 0 1)) (hY : ContinuousOn Yp (Icc 0 1)) : ContinuousOn A (Icc 0 1) := by
  intro s hs
  obtain ⟨C, ε, hε, hC⟩ := hA s hs
  have hs' := hC s ⟨mem_ball_self hε, hs⟩
  have hc : ContinuousWithinAt (fun τ => A s + (C.F u Yp τ - C.F u Yp s)) (Icc 0 1) s :=
    continuousWithinAt_const.add ((C.continuousWithinAt_F (hu s hs) (hY s hs) hs'.1).sub
      continuousWithinAt_const)
  refine hc.congr_of_eventuallyEq ?_ (by simp)
  filter_upwards [inter_mem_nhdsWithin (Icc 0 1) (ball_mem_nhds s hε), self_mem_nhdsWithin]
    with τ hτ hτI
  have := hs'.2 τ ⟨hτ.2, hτI⟩
  rw [← this]; abel

/-- Derivative of a chart's Abel integral along the path, where `Yp ≠ 0`. -/
lemma PathChart.hasDerivAt_F (C : PathChart f g) {t : ℝ} {u' Yp' : ℂ} (hu : HasDerivAt u u' t)
    (hY : HasDerivAt Yp Yp' t) (hC : ∀ᶠ τ in 𝓝 t, C.Carries u Yp τ) (hY0 : Yp t ≠ 0) :
    HasDerivAt (C.F u Yp) (u' • fun k : Fin g => u t ^ (k : ℕ) / Yp t) t := by
  have hCt := hC.self_of_nhds
  cases C with
  | br B =>
    refine ((B.I_deriv _ hCt.1).scomp t hu).congr_deriv ?_
    funext k; simp [omegaVec, hCt.2]
  | we W =>
    have hX := W.hasDerivAt_X hCt.1
    have h1 := (W.I_deriv _ hCt.1).scomp t hY
    -- `u = X ∘ Yp` near `t`, so `u' = Yp' X'(Yp)`
    have hu2 : HasDerivAt u (Yp' • (2 * Yp t / (derivative f).eval (W.X (Yp t)))) t := by
      refine (hX.scomp t hY).congr_of_eventuallyEq ?_
      filter_upwards [hC] with τ hτ using hτ.2.symm
    have hu' := hu.unique hu2
    refine h1.congr_deriv ?_
    have hne := W.fd_ne _ hCt.1
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, weierVec, hu', hCt.2]
    rw [hCt.2] at hne
    field_simp

theorem IsAbelAlongW.hasDerivAt {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlongW f g u Yp A) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {u' Yp' : ℂ} (hu : HasDerivAt u u' t) (hY : HasDerivAt Yp Yp' t)
    (hY0 : Yp t ≠ 0) : HasDerivAt A (u' • fun k : Fin g => u t ^ (k : ℕ) / Yp t) t := by
  obtain ⟨C, ε, hε, hC⟩ := hA t (Ioo_subset_Icc_self ht)
  have hn : ball t ε ∩ Icc 0 1 ∈ 𝓝 t := inter_mem (ball_mem_nhds t hε) (Icc_mem_nhds ht.1 ht.2)
  have hCev : ∀ᶠ τ in 𝓝 t, C.Carries u Yp τ := by
    filter_upwards [hn] with τ hτ using (hC τ hτ).1
  have hD := C.hasDerivAt_F hu hY hCev hY0
  have hev : (fun τ => A t + (C.F u Yp τ - C.F u Yp t)) =ᶠ[𝓝 t] A := by
    filter_upwards [hn] with τ hτ
    have := (hC t ⟨mem_ball_self hε, Ioo_subset_Icc_self ht⟩).2 τ hτ
    rw [← this]; abel
  exact ((hD.sub_const _).const_add (A t)).congr_of_eventuallyEq hev.symm

/-- **The components of the Abel integral along a path are curve integrals** (zeros of `Yp` countable;
derivatives on `(0, 1)` only). -/
theorem IsAbelAlongW.curveIntegral {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlongW f g u Yp A) (hA0 : A 0 = 0)
    (hu : ContinuousOn u (Icc 0 1)) (hY : ContinuousOn Yp (Icc 0 1)) {u' Yp' : ℝ → ℂ}
    (hu' : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt u (u' t) t) (hY' : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Yp (Yp' t) t)
    (hZ : {t | Yp t = 0}.Countable) {P Q : ℂ × ℂ} (γ : Path P Q)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t = (u t, Yp t)) (j : Fin g)
    (hint : CurveIntegrable (Beta.omegaJ j) γ) :
    ∫ᶜ p in γ, Beta.omegaJ j p = A 1 j := by
  -- the integrand `curveIntegralFun` agrees on `(0, 1)` with `u' u^j / Yp`
  have hfun : ∀ t ∈ Ioo (0 : ℝ) 1, curveIntegralFun (Beta.omegaJ j) γ t = u' t * (u t ^ (j : ℕ) / Yp t) := by
    intro t ht
    have hev : γ.extend =ᶠ[𝓝 t] fun s => (u s, Yp s) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using hγ s (Ioo_subset_Icc_self hs)
    have hd : derivWithin γ.extend unitInterval t = (u' t, Yp' t) := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hev.deriv_eq,
        ((hu' t ht).prodMk (hY' t ht)).deriv]
    rw [curveIntegralFun_def, hd, hev.eq_of_nhds]
    simp [Beta.omegaJ]; ring
  have hae : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      curveIntegralFun (Beta.omegaJ j) γ t = u' t * (u t ^ (j : ℕ) / Yp t) := by
    filter_upwards [(countable_singleton (1 : ℝ)).ae_notMem volume] with t ht1 hmem
    rw [uIoc_of_le zero_le_one] at hmem
    exact hfun t ⟨hmem.1, lt_of_le_of_ne hmem.2 ht1⟩
  have hint' : IntervalIntegrable (fun t => u' t * (u t ^ (j : ℕ) / Yp t)) volume 0 1 := by
    refine (hint : IntervalIntegrable _ volume 0 1).congr_ae ?_
    rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae
  rw [curveIntegral_def, intervalIntegral.integral_congr_ae hae]
  have hcA : ContinuousOn (fun t => A t j) (Icc 0 1) := fun t ht =>
    ((continuous_apply j).continuousAt.comp_continuousWithinAt (hA.continuousOn hu hY t ht))
  rw [integral_eq_of_hasDerivAt_off_countable_of_le (fun t => A t j) _ zero_le_one hZ hcA
    (fun t ht => ?_) hint', hA0]
  · simp
  · have h := hA.hasDerivAt ht.1 (hu' t ht.1) (hY' t ht.1) ht.2
    exact (hasDerivAt_pi.mp h j).congr_deriv (by simp)

/-! ## The paths `[ζ^e]ℓ` on `y² = 4x⁵ + 1` -/

/-- The model polynomial `f₅ = 4x⁵ + 1` (ABVAR A0.1). -/
def f₅ : ℂ[X] := C 4 * X ^ 5 + C 1

lemma f₅_eval (x : ℂ) : f₅.eval x = 4 * x ^ 5 + 1 := by simp [f₅]

lemma f₅_deriv_eval (x : ℂ) : (derivative f₅).eval x = 20 * x ^ 4 := by
  simp [f₅]; ring

open Beta in
/-- **The Abel integral along `[ζ^e]ℓ` exists and computes the Beta period.** -/
theorem abelAlong_liftPath (e : ℕ) :
    ∃ A : ℝ → (Fin 2 → ℂ), A 0 = 0 ∧ IsAbelAlongW f₅ 2 (fun t => (liftFun e t).1) (fun t => (liftFun e t).2) A ∧
      ∀ j : Fin 2, A 1 j = cst e j * Complex.betaIntegral (((j : ℕ) + 1 : ℂ) / 5) (((j : ℕ) + 1 : ℂ) / 5) := by
  set u : ℝ → ℂ := fun t => (liftFun e t).1
  set Yp : ℝ → ℂ := fun t => (liftFun e t).2
  have hu : ContinuousOn u (Icc 0 1) := (continuous_fst.comp (continuous_liftFun e)).continuousOn
  have hY : ContinuousOn Yp (Icc 0 1) := (continuous_snd.comp (continuous_liftFun e)).continuousOn
  have hsq : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ^ 2 = f₅.eval (u t) := by
    intro t ht
    rw [f₅_eval]
    exact liftPath_mem_curve e ⟨t, ht⟩
  have hY0 : ∀ t, Yp t = 0 → t = 1 / 2 := by
    intro t h
    simp only [Yp, liftFun] at h
    have : (2 * t - 1 : ℝ) = 0 := by exact_mod_cast h
    linarith
  have hsimple : ∀ t ∈ Icc (0 : ℝ) 1, Yp t = 0 → (derivative f₅).eval (u t) ≠ 0 := by
    intro t ht h
    rw [f₅_deriv_eval]
    have h4 : (4 : ℂ) * u t ^ 5 + 1 = 0 := by rw [← f₅_eval, ← hsq t ht, h]; ring
    intro h20
    have : u t = 0 := by
      have : u t ^ 4 = 0 := by linear_combination h20 / 20
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    rw [this] at h4; norm_num at h4
  obtain ⟨A, hA0, hA⟩ := exists_abelAlongW (g := 2) hu hY hsq hsimple
  refine ⟨A, hA0, hA, fun j => ?_⟩
  have hZ : {t | Yp t = 0}.Countable :=
    (countable_singleton (1 / 2 : ℝ)).mono fun t ht => hY0 t ht
  have hu' : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt u
      (-(zetaN 5 ^ e) * (((1 - 2 * t) * (1 / 5) * (t * (1 - t)) ^ ((1 / 5 : ℝ) - 1) : ℝ) : ℂ)) t :=
    fun t ht => (hasDerivAt_liftFun e ht.1 ht.2).fst
  have hY' : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Yp (2 : ℂ) t :=
    fun t ht => (hasDerivAt_liftFun e ht.1 ht.2).snd
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, (liftPath e).extend t = (u t, Yp t) := by
    intro t ht
    rw [Path.extend_apply _ ht]; rfl
  have hAW : IsAbelAlongW f₅ 2 u Yp A := hA
  have h := hAW.curveIntegral hA0 hu hY hu' hY' hZ (liftPath e) hγ j (curveIntegrable_liftPath e j)
  rw [← h, curveIntegral_liftPath]

open Beta in
/-- **The periods of `[ζ^e]γ` are differences of Abel integrals along paths with the same endpoints**
(`(0, −1) → (0, 1)`): `∫_{cycleE e} x^j dx/y = A_e(1)_j − A_{e+1}(1)_j`. -/
theorem period_eq_abelAlong (e : ℕ) (j : Fin 2) {A A' : ℝ → (Fin 2 → ℂ)}
    (hA : ∀ j : Fin 2, A 1 j = cst e j * Complex.betaIntegral (((j : ℕ) + 1 : ℂ) / 5) (((j : ℕ) + 1 : ℂ) / 5))
    (hA' : ∀ j : Fin 2, A' 1 j =
      cst (e + 1) j * Complex.betaIntegral (((j : ℕ) + 1 : ℂ) / 5) (((j : ℕ) + 1 : ℂ) / 5)) :
    ∫ᶜ p in cycleE e, omegaJ j p = A 1 j - A' 1 j := by
  rw [hA, hA', cycleE, curveIntegral_trans (curveIntegrable_liftPath e j)
    (curveIntegrable_liftPath (e + 1) j).symm, curveIntegral_symm, curveIntegral_liftPath,
    curveIntegral_liftPath]
  ring

end LSG.JacAn
