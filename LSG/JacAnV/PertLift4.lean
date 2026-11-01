/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.PeriodKer

/-!
# M2.3 (N5, paths): the perturbed period paths carry the forms `x^j dx/y`, `j < 4`

The path machinery (`IsAbelAlong f g`, `WeierChart f g`, `abelAlong_perturb_eq`) is generic in `g`; only
`exists_pert_lift` was stated for `g = 2`. Here:
* `WeierChart.restrict2`: a chart for `g = 4` restricts to `g = 2` (same `X`, first two integrals);
* `abelAlong_liftPath_g`: the Abel integral along `[ζ^e]ℓ` for any `g`, `(A 1)_j = cst e j · B((j+1)/5, (j+1)/5)`;
* **`exists_pert_lift24`**: one perturbed lift `(u, Y)` of `[ζ^e]ℓ` carrying both the `g = 2` Abel integral (for the
  continuation) and the `g = 4` one (for `x³ dx/y`), with the endpoint values of both.
-/

noncomputable section

open Polynomial Metric Set Filter Topology Complex

namespace LSG.JacAn

open Beta

/-- Restriction of a Weierstrass chart from `g = 4` to `g = 2`. -/
def WeierChart.restrict2 {f : ℂ[X]} (W : WeierChart f 4) : WeierChart f 2 where
  e := W.e
  r := W.r
  r_pos := W.r_pos
  X := W.X
  X_zero := W.X_zero
  X_an := W.X_an
  X_sq := W.X_sq
  fd_ne := W.fd_ne
  I := fun y k => W.I y (Fin.castLE (by norm_num) k)
  I_zero := by funext k; simp [W.I_zero]
  I_deriv := fun y hy => by
    refine hasDerivAt_pi.mpr fun k => ?_
    have := hasDerivAt_pi.mp (W.I_deriv y hy) (Fin.castLE (by norm_num) k)
    simpa [weierVec] using this
  I_an := fun y hy => analyticAt_pi_iff.mpr fun k =>
    (analyticAt_pi_iff.mp (W.I_an y hy)) (Fin.castLE (by norm_num) k)

/-- **The Abel integral along `[ζ^e]ℓ`**, for any number `g` of forms `x^j dx/y`. -/
theorem abelAlong_liftPath_g (g e : ℕ) :
    ∃ A : ℝ → (Fin g → ℂ), A 0 = 0 ∧ IsAbelAlongW f₅ g (fun t => (liftFun e t).1) (fun t => (liftFun e t).2) A ∧
      ∀ j : Fin g, A 1 j = cst e j * Complex.betaIntegral (((j : ℕ) + 1 : ℂ) / 5) (((j : ℕ) + 1 : ℂ) / 5) := by
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
  obtain ⟨A, hA0, hA⟩ := exists_abelAlongW (g := g) hu hY hsq hsimple
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
  have hAW : IsAbelAlongW f₅ g u Yp A := hA
  have h := hAW.curveIntegral hA0 hu hY hu' hY' hZ (liftPath e) hγ j (curveIntegrable_liftPath e j)
  rw [← h, curveIntegral_liftPath]

/-- **The perturbed lift of `[ζ^e]ℓ` with the Abel integrals for `g = 2` and `g = 4`.** -/
theorem exists_pert_lift24 (e : ℕ) :
    ∃ u Y : ℝ → ℂ, ∃ A : ℝ → (Fin 2 → ℂ), ∃ A₄ : ℝ → (Fin 4 → ℂ),
      IsAbelAlong f₅ 2 u Y A ∧ IsAbelAlong f₅ 4 u Y A₄ ∧ A 0 = 0 ∧ A₄ 0 = 0 ∧
      ContinuousOn u (Icc 0 1) ∧ u 0 = 0 ∧ Y 0 = -1 ∧ u 1 = 0 ∧ Y 1 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖u t‖ < 1) ∧
      (∀ j : Fin 2, A 1 j = cst e j * Complex.betaIntegral (((j : ℕ) + 1 : ℂ) / 5) (((j : ℕ) + 1 : ℂ) / 5)) ∧
      ∀ j : Fin 4, A₄ 1 j = cst e j * Complex.betaIntegral (((j : ℕ) + 1 : ℂ) / 5) (((j : ℕ) + 1 : ℂ) / 5) := by
  obtain ⟨A₀, hA₀0, hA₀W, hA₀1⟩ := abelAlong_liftPath e
  obtain ⟨B₀, hB₀0, hB₀W, hB₀1⟩ := abelAlong_liftPath_g 4 e
  set u₀ : ℝ → ℂ := fun t => (liftFun e t).1 with hu₀def
  have hA₀W' : IsAbelAlongW f₅ 2 u₀ (fun t => 2 * (t : ℂ) - 1) A₀ := hA₀W
  have hB₀W' : IsAbelAlongW f₅ 4 u₀ (fun t => 2 * (t : ℂ) - 1) B₀ := hB₀W
  have hu : ContinuousOn u₀ (Icc 0 1) := (continuous_fst.comp (continuous_liftFun e)).continuousOn
  have hYc : Continuous (fun t : ℝ => 2 * (t : ℂ) - 1) :=
    (continuous_const.mul Complex.continuous_ofReal).sub continuous_const
  have hsq : ∀ t ∈ Icc (0 : ℝ) 1, (2 * (t : ℂ) - 1) ^ 2 = f₅.eval (u₀ t) := by
    intro t ht
    rw [f₅_eval]
    exact liftPath_mem_curve e ⟨t, ht⟩
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hY0 : (2 * ((1 / 2 : ℝ) : ℂ) - 1) = 0 := by push_cast; ring
  have hd : (derivative f₅).eval (u₀ (1 / 2)) ≠ 0 := by
    rw [f₅_deriv_eval]
    have h4 : (4 : ℂ) * u₀ (1 / 2) ^ 5 + 1 = 0 := by rw [← f₅_eval, ← hsq _ hhalf, hY0]; ring
    intro h20
    have : u₀ (1 / 2) = 0 := by
      have : u₀ (1 / 2) ^ 4 = 0 := by linear_combination h20 / 20
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    rw [this] at h4; norm_num at h4
  obtain ⟨W, ε, hε, hW⟩ := exists_weier_along (g := 4) (Yp := fun t : ℝ => 2 * (t : ℂ) - 1) hu
    hYc.continuousOn hsq hhalf hY0 hd
  obtain ⟨ρ, hρ, hX⟩ := Metric.continuousAt_iff.mp (W.X_an 0 (mem_ball_self W.r_pos)).continuousAt
    (1 / 10) (by norm_num)
  set η : ℝ := min (min (1 / 4) (ε / 4)) (min (W.r / 6) (ρ / 4)) with hη
  have hr := W.r_pos
  have h1 : 0 < η := lt_min (lt_min (by norm_num) (by linarith)) (lt_min (by linarith) (by linarith))
  have hηa : η ≤ 1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hηb : η ≤ ε / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hηc : η ≤ W.r / 6 := (min_le_right _ _).trans (min_le_left _ _)
  have hηd : η ≤ ρ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have h2 : η < 1 / 2 := by linarith
  have h3 : 2 * η < ε := by linarith
  have h4 : 5 * η < W.r := by linarith
  have hdiff := continuous_pertU_diff W hW h1 h2 h3 h4
  have hueq : pertU W u₀ η = fun t => u₀ t + (W.X (pertY η t) - W.X (2 * (t : ℂ) - 1)) := rfl
  have hu' : ContinuousOn (pertU W u₀ η) (Icc 0 1) := by
    rw [hueq]; exact hu.add hdiff.continuousOn
  have hsq' : ∀ t ∈ Icc (0 : ℝ) 1, pertY η t ^ 2 = f₅.eval (pertU W u₀ η t) := fun t ht =>
    pert_sq W hW h1 h2 h3 h4 ht (hsq t ht)
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, pertY η t ≠ 0 := fun t _ => pertY_ne_zero h1
  obtain ⟨A, hA0, hA⟩ := exists_abelAlong (g := 2) hu' (continuous_pertY η).continuousOn hsq' hne
  obtain ⟨A₄, hA₄0, hA₄⟩ := exists_abelAlong (g := 4) hu' (continuous_pertY η).continuousOn hsq' hne
  have hAA : IsAbelAlong f₅ 2 (pertU W u₀ η) (pertY η) A := hA
  have hAA₄ : IsAbelAlong f₅ 4 (pertU W u₀ η) (pertY η) A₄ := hA₄
  have hAA' : IsAbelAlong f₅ 2 (pertU W.restrict2 u₀ η) (pertY η) A := hA
  have hA1 : A 1 = A₀ 1 :=
    abelAlong_perturb_eq W.restrict2 hW h1 h2 h3 h4 hA₀W' hA₀0 hAA'.toW hA0
  have hA₄1 : A₄ 1 = B₀ 1 := abelAlong_perturb_eq W hW h1 h2 h3 h4 hB₀W' hB₀0 hAA₄.toW hA₄0
  have far0 : η ≤ |(0 : ℝ) - 1 / 2| := by rw [abs_of_neg (by norm_num)]; linarith
  have far1 : η ≤ |(1 : ℝ) - 1 / 2| := by rw [abs_of_pos (by norm_num)]; linarith
  refine ⟨pertU W u₀ η, pertY η, A, A₄, hAA, hAA₄, hA0, hA₄0, hu', ?_, ?_, ?_, ?_, ?_,
    fun j => by rw [hA1]; exact hA₀1 j, fun j => by rw [hA₄1]; exact hB₀1 j⟩
  · rw [pertU_eq_of_far W u₀ far0]; simp [hu₀def, liftFun, rho]
  · rw [pertY_eq_of_far far0]; norm_num
  · rw [pertU_eq_of_far W u₀ far1]; norm_num [hu₀def, liftFun, rho]
  · rw [pertY_eq_of_far far1]; norm_num
  · intro t ht
    have hb : ‖u₀ t‖ ≤ 4 / 5 := norm_liftFun_fst_le e ht
    have hdf : ‖W.X (pertY η t) - W.X (2 * (t : ℂ) - 1)‖ < 1 / 5 := by
      by_cases hfar : η ≤ |t - 1 / 2|
      · rw [pertY_eq_of_far hfar, sub_self, norm_zero]; norm_num
      · push Not at hfar
        have hy1 : dist (pertY η t) 0 < ρ := by
          rw [dist_zero_right]; linarith [norm_pertY_le η t h1.le]
        have hy2 : dist (2 * (t : ℂ) - 1) 0 < ρ := by
          rw [dist_zero_right, norm_two_t_sub_one]; linarith
        have e1 := hX hy1
        have e2 := hX hy2
        rw [dist_eq_norm] at e1 e2
        calc ‖W.X (pertY η t) - W.X (2 * (t : ℂ) - 1)‖
            = ‖(W.X (pertY η t) - W.X 0) - (W.X (2 * (t : ℂ) - 1) - W.X 0)‖ := by congr 1; ring
          _ ≤ ‖W.X (pertY η t) - W.X 0‖ + ‖W.X (2 * (t : ℂ) - 1) - W.X 0‖ := norm_sub_le _ _
          _ < 1 / 5 := by linarith
    rw [hueq]
    calc ‖u₀ t + (W.X (pertY η t) - W.X (2 * (t : ℂ) - 1))‖
        ≤ ‖u₀ t‖ + ‖W.X (pertY η t) - W.X (2 * (t : ℂ) - 1)‖ := norm_add_le _ _
      _ < 1 := by linarith

/-- **The `x³ dx/y` period of `[ζ^e]γ` as a difference of `g = 4` Abel integrals.** -/
theorem period3_eq_abelAlong (e : ℕ) {A A' : ℝ → (Fin 4 → ℂ)}
    (hA : ∀ j : Fin 4, A 1 j = cst e j * Complex.betaIntegral (((j : ℕ) + 1 : ℂ) / 5) (((j : ℕ) + 1 : ℂ) / 5))
    (hA' : ∀ j : Fin 4, A' 1 j =
      cst (e + 1) j * Complex.betaIntegral (((j : ℕ) + 1 : ℂ) / 5) (((j : ℕ) + 1 : ℂ) / 5)) :
    ∫ᶜ p in cycleE e, omegaJ 3 p = A 1 3 - A' 1 3 := by
  rw [hA, hA', cycleE, curveIntegral_trans (curveIntegrable_liftPath e 3)
    (curveIntegrable_liftPath (e + 1) 3).symm, curveIntegral_symm, curveIntegral_liftPath,
    curveIntegral_liftPath]
  norm_num
  ring

end LSG.JacAn
