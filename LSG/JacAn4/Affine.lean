/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn4.Anchor

/-!
# A4.1b (S-a/S-b): every affine model point is in the cone

* `chart_div`: `f(x) − b(x)² = a(x) q(x) + chartR1J p · x + chartR0J p` for `a = x² − s₁x + s₂`, `b = b₁x + b₀`;
* `curve_approx`: a point of `C` is a limit of points with `y ≠ 0` (Weierstrass chart if `y = 0`);
* **`chart_mem`**: if every generic Grant point is in the cone, so is every chart point. Distinct roots: perturb
  Weierstrass points. Double root `x₀`: `y₀ ≠ 0` (simple roots of `f`), and `(x₀ ± t, Y(x₀ ± t))` (local branch)
  converge to it (symmetric difference quotients);
* **`ThetaData.affine_mem`**: with `affine_chart`, every model point with `X₀ ≠ 0` is in the cone.
-/

noncomputable section

open Metric Set Filter Topology Polynomial

namespace LSG.JacAn

/-- The division of `f − b²` by `a`. -/
lemma chart_div (x : ℂ) (p : Fin 4 → ℂ) :
    fc x - (p 2 * x + p 3) ^ 2 = (x ^ 2 - p 0 * x + p 1) *
      (-p 2 ^ 2 + 4 * p 0 ^ 3 - 8 * p 0 * p 1 + 4 * p 0 * x ^ 2 + 4 * x ^ 3 + x * (4 * p 0 ^ 2 - 4 * p 1)) +
      chartR1J p * x + chartR0J p := by
  simp only [fc, chartR1J, chartR0J]; ring

/-- A point of `C` is a limit of points with `y ≠ 0`. -/
lemma curve_approx {x y : ℂ} (h : y ^ 2 = fc x) : ∃ P : ℂ → ℂ × ℂ, Tendsto P (𝓝[≠] 0) (𝓝 (x, y)) ∧
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), (P t).2 ^ 2 = fc (P t).1 ∧ (P t).2 ≠ 0 := by
  by_cases hy : y = 0
  · subst hy
    have hfx : f₅.eval x = 0 := by rw [← fc_eq, ← h]; ring
    have hx0 : x ≠ 0 := by rintro rfl; simp [fc] at h
    have hd : (derivative f₅).eval x ≠ 0 := by
      rw [f₅_deriv_eval]; exact mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0)
    obtain ⟨W, hWe⟩ := WeierChart.exists_of_root (g := 2) hfx hd
    refine ⟨fun t => (W.X t, t), ?_, ?_⟩
    · have hc : ContinuousAt (fun t => (W.X t, t)) 0 :=
        ((W.X_an 0 (mem_ball_self W.r_pos)).continuousAt).prodMk continuousAt_id
      have := hc.tendsto
      rw [W.X_zero, hWe] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) W.r_pos), self_mem_nhdsWithin] with t ht ht0
      exact ⟨by rw [fc_eq, W.X_sq t ht], ht0⟩
  · refine ⟨fun _ => (x, y), tendsto_const_nhds, Eventually.of_forall fun _ => ⟨h, hy⟩⟩

variable {S : Set P9}

/-- **Chart points.** -/
theorem chart_mem (hS : IsClosed S)
    (hgen : ∀ x₁ y₁ x₂ y₂ : ℂ, y₁ ^ 2 = fc x₁ → y₂ ^ 2 = fc x₂ → x₁ ≠ x₂ → y₁ ≠ 0 → y₂ ≠ 0 →
      grantJ (mumfordPts x₁ y₁ x₂ y₂) ∈ S)
    {p : Fin 4 → ℂ} (hR1 : chartR1J p = 0) (hR0 : chartR0J p = 0) : grantJ p ∈ S := by
  -- closing along `𝓝[≠] 0`
  have hclose : ∀ m : ℂ → Fin 4 → ℂ, Tendsto m (𝓝[≠] 0) (𝓝 p) →
      (∀ᶠ t in 𝓝[≠] (0 : ℂ), grantJ (m t) ∈ S) → grantJ p ∈ S := fun m hm hev =>
    hS.mem_of_tendsto ((continuous_grantJ.tendsto p).comp hm) hev
  -- the roots of `a`
  obtain ⟨x₁, hx₁⟩ := Complex.exists_root (f := X ^ 2 - C (p 0) * X + C (p 1))
    (by rw [show (X ^ 2 - C (p 0) * X + C (p 1) : ℂ[X]).degree = 2 by compute_degree!]; norm_num)
  simp only [IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hx₁
  set x₂ := p 0 - x₁
  have hs1 : x₁ + x₂ = p 0 := by simp [x₂]
  have hs2 : x₁ * x₂ = p 1 := by simp only [x₂]; linear_combination -hx₁
  have hx₂ : x₂ ^ 2 - p 0 * x₂ + p 1 = 0 := by simp only [x₂]; linear_combination hx₁
  set y₁ := p 2 * x₁ + p 3
  set y₂ := p 2 * x₂ + p 3
  have hy₁ : y₁ ^ 2 = fc x₁ := by
    have := chart_div x₁ p; rw [hx₁, hR1, hR0] at this; linear_combination -this
  have hy₂ : y₂ ^ 2 = fc x₂ := by
    have := chart_div x₂ p; rw [hx₂, hR1, hR0] at this; linear_combination -this
  by_cases h12 : x₁ = x₂
  · -- double root `x₀`
    set x₀ := x₁
    set y₀ := y₁
    set Q : ℂ → ℂ := fun x => -p 2 ^ 2 + 4 * p 0 ^ 3 - 8 * p 0 * p 1 + 4 * p 0 * x ^ 2 + 4 * x ^ 3 +
      x * (4 * p 0 ^ 2 - 4 * p 1)
    have hfd : ∀ x, 4 * x ^ 5 + 1 - (p 2 * x + p 3) ^ 2 = (x - x₀) ^ 2 * Q x := by
      intro x
      have h := chart_div x p
      rw [hR1, hR0] at h
      simp only [fc] at h
      rw [h]; simp only [Q]; rw [← hs1, ← hs2, ← h12]; ring
    -- `20 x₀⁴ = 2 y₀ b₁` (derivative at `x₀`)
    have hderiv : 20 * x₀ ^ 4 = 2 * y₀ * p 2 := by
      have hL : HasDerivAt (fun x : ℂ => 4 * x ^ 5 + 1 - (p 2 * x + p 3) ^ 2)
          (20 * x₀ ^ 4 - 2 * y₀ * p 2) x₀ := by
        have h1 := ((hasDerivAt_pow 5 x₀).const_mul (4 : ℂ)).add_const (1 : ℂ)
        have h2 := (((hasDerivAt_id' x₀).const_mul (p 2)).add_const (p 3)).pow 2
        refine (h1.sub h2).congr_deriv ?_
        simp only [y₀, y₁]; push_cast; ring
      have hQd : DifferentiableAt ℂ Q x₀ := by simp only [Q]; fun_prop
      have hR : HasDerivAt (fun x : ℂ => (x - x₀) ^ 2 * Q x) 0 x₀ := by
        have hs := ((hasDerivAt_id' x₀).sub_const x₀).pow 2
        refine (hs.mul hQd.hasDerivAt).congr_deriv ?_
        simp
      have heq : (fun x : ℂ => 4 * x ^ 5 + 1 - (p 2 * x + p 3) ^ 2) = fun x => (x - x₀) ^ 2 * Q x :=
        funext hfd
      rw [heq] at hL
      have := hL.unique hR
      linear_combination this
    have hy0 : y₀ ≠ 0 := by
      intro h0
      have hf0 : fc x₀ = 0 := by rw [← hy₁]; change y₀ ^ 2 = 0; rw [h0]; ring
      rw [h0] at hderiv
      have : x₀ = 0 := by
        have : x₀ ^ 4 = 0 := by linear_combination hderiv / 20
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      rw [this] at hf0; simp [fc] at hf0
    -- local branch through `(x₀, y₀)`
    obtain ⟨B, hBx, hBy⟩ := LocalBranch.exists_of_mem (f := f₅) (g := 2) (x₀ := x₀) (y₀ := y₀)
      (by rw [← fc_eq]; exact hy₁) hy0
    have hball : ball B.x₀ B.r ∈ 𝓝 x₀ := by rw [hBx]; exact ball_mem_nhds _ B.r_pos
    have hx₀B : x₀ ∈ ball B.x₀ B.r := by rw [hBx]; exact mem_ball_self B.r_pos
    have hYd : HasDerivAt B.Y (p 2) x₀ := by
      have hd := ((B.Y_an x₀ hx₀B).differentiableAt).hasDerivAt
      have hsq : HasDerivAt (fun x => B.Y x ^ 2) (2 * y₀ * deriv B.Y x₀) x₀ := by
        refine (hd.pow 2).congr_deriv ?_
        rw [hBy]; push_cast; ring
      have hf : HasDerivAt (fun x => f₅.eval x) (20 * x₀ ^ 4) x₀ := by
        have := f₅.hasDerivAt x₀
        rwa [f₅_deriv_eval] at this
      have heq : (fun x => B.Y x ^ 2) =ᶠ[𝓝 x₀] fun x => f₅.eval x := by
        filter_upwards [hball] with x hx using B.Y_sq x hx
      have := hsq.unique (hf.congr_of_eventuallyEq heq)
      have hdY : deriv B.Y x₀ = p 2 := by
        apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hy0)
        linear_combination this + hderiv
      rw [← hdY]; exact hd
    have hlinp : Tendsto (fun t : ℂ => x₀ + t) (𝓝 0) (𝓝 x₀) :=
      Continuous.tendsto' (by fun_prop : Continuous fun t : ℂ => x₀ + t) 0 x₀ (by simp)
    have hlinm : Tendsto (fun t : ℂ => x₀ - t) (𝓝 0) (𝓝 x₀) :=
      Continuous.tendsto' (by fun_prop : Continuous fun t : ℂ => x₀ - t) 0 x₀ (by simp)
    set m : ℂ → Fin 4 → ℂ := fun t => mumfordPts (x₀ + t) (B.Y (x₀ + t)) (x₀ - t) (B.Y (x₀ - t))
    refine hclose m ?_ ?_
    · -- the limit
      have hneg : Tendsto (fun t : ℂ => -t) (𝓝[≠] 0) (𝓝[≠] 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (by simpa using (continuous_neg.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds)
          (by filter_upwards [self_mem_nhdsWithin] with t ht; exact neg_ne_zero.mpr ht)
      have hsl := hYd.tendsto_slope_zero
      have hsl' := hsl.comp hneg
      have hYc : Tendsto (fun t : ℂ => B.Y (x₀ + t)) (𝓝[≠] 0) (𝓝 y₀) := by
        have := hYd.continuousAt.tendsto.comp hlinp
        rw [hBy] at this
        exact this.mono_left nhdsWithin_le_nhds
      have hYc' : Tendsto (fun t : ℂ => B.Y (x₀ - t)) (𝓝[≠] 0) (𝓝 y₀) := by
        have := hYd.continuousAt.tendsto.comp hlinm
        rw [hBy] at this
        exact this.mono_left nhdsWithin_le_nhds
      have hsym : Tendsto (fun t : ℂ => (B.Y (x₀ + t) - B.Y (x₀ - t)) / ((x₀ + t) - (x₀ - t))) (𝓝[≠] 0)
          (𝓝 (p 2)) := by
        have := (hsl.add hsl').const_mul (1 / 2 : ℂ)
        rw [show (1 / 2 : ℂ) * (p 2 + p 2) = p 2 by ring] at this
        refine this.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : (t : ℂ) ≠ 0 := ht
        simp only [Function.comp_def, smul_eq_mul, ← sub_eq_add_neg]
        field_simp
        have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht'
        linear_combination (B.Y (x₀ - t) - B.Y (x₀ + t)) * hti
      refine tendsto_pi_nhds.mpr fun i => ?_
      fin_cases i
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun t => ?_)
        simp only [m, mumfordPts, Fin.zero_eta, Matrix.cons_val_zero]
        rw [← hs1, ← h12]; ring
      · have h := ((by fun_prop : Continuous fun t : ℂ => (x₀ + t) * (x₀ - t)).tendsto (0 : ℂ)).mono_left
          (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
        simp only [add_zero, sub_zero] at h
        rw [show x₀ * x₀ = p 1 by rw [← hs2, ← h12]] at h
        exact h.congr' (Eventually.of_forall fun t => by simp [m, mumfordPts])
      · exact hsym.congr' (Eventually.of_forall fun t => by simp [m, mumfordPts])
      · have hlim : Tendsto (fun t : ℂ => -x₀ * ((B.Y (x₀ + t) - B.Y (x₀ - t)) / ((x₀ + t) - (x₀ - t))) +
            (B.Y (x₀ + t) + B.Y (x₀ - t)) / 2) (𝓝[≠] 0) (𝓝 (-x₀ * p 2 + (y₀ + y₀) / 2)) :=
          (hsym.const_mul (-x₀)).add ((hYc.add hYc').div_const 2)
        rw [show -x₀ * p 2 + (y₀ + y₀) / 2 = p 3 by simp only [y₀, y₁, x₀]; ring] at hlim
        refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : (t : ℂ) ≠ 0 := ht
        have key : -x₀ * ((B.Y (x₀ + t) - B.Y (x₀ - t)) / ((x₀ + t) - (x₀ - t))) +
            (B.Y (x₀ + t) + B.Y (x₀ - t)) / 2 =
            ((x₀ + t) * B.Y (x₀ - t) - (x₀ - t) * B.Y (x₀ + t)) / ((x₀ + t) - (x₀ - t)) := by
          rw [show (x₀ + t) - (x₀ - t) = 2 * t by ring]
          field_simp
          ring
        rw [key]
        simp [m, mumfordPts]
    · -- generic for small `t ≠ 0`
      have hr : ∀ᶠ t in 𝓝[≠] (0 : ℂ), x₀ + t ∈ ball B.x₀ B.r ∧ x₀ - t ∈ ball B.x₀ B.r :=
        nhdsWithin_le_nhds ((hlinp.eventually hball).and (hlinm.eventually hball))
      filter_upwards [hr, self_mem_nhdsWithin] with t ht ht0
      refine hgen _ _ _ _ (by rw [fc_eq]; exact B.Y_sq _ ht.1) (by rw [fc_eq]; exact B.Y_sq _ ht.2) ?_
        (B.Y_ne _ ht.1) (B.Y_ne _ ht.2)
      intro h
      have : (2 : ℂ) * t = 0 := by linear_combination h
      exact ht0 (by simpa using this)
  · -- distinct roots: perturb Weierstrass points
    obtain ⟨P₁, hP₁, hP₁e⟩ := curve_approx hy₁
    obtain ⟨P₂, hP₂, hP₂e⟩ := curve_approx hy₂
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr h12
    have ha1 : Tendsto (fun t => (P₁ t).1) (𝓝[≠] 0) (𝓝 x₁) := (continuous_fst.tendsto _).comp hP₁
    have hb1 : Tendsto (fun t => (P₁ t).2) (𝓝[≠] 0) (𝓝 y₁) := (continuous_snd.tendsto _).comp hP₁
    have ha2 : Tendsto (fun t => (P₂ t).1) (𝓝[≠] 0) (𝓝 x₂) := (continuous_fst.tendsto _).comp hP₂
    have hb2 : Tendsto (fun t => (P₂ t).2) (𝓝[≠] 0) (𝓝 y₂) := (continuous_snd.tendsto _).comp hP₂
    set m : ℂ → Fin 4 → ℂ := fun t => mumfordPts (P₁ t).1 (P₁ t).2 (P₂ t).1 (P₂ t).2
    have hpm : p = mumfordPts x₁ y₁ x₂ y₂ := by
      funext i; fin_cases i <;> simp [mumfordPts, y₁, y₂] <;> [exact hs1.symm; exact hs2.symm; skip; skip] <;>
        field_simp <;> ring
    refine hclose m ?_ ?_
    · rw [hpm]
      refine tendsto_pi_nhds.mpr fun i => ?_
      fin_cases i
      · exact (ha1.add ha2).congr' (Eventually.of_forall fun t => by simp [m, mumfordPts])
      · exact (ha1.mul ha2).congr' (Eventually.of_forall fun t => by simp [m, mumfordPts])
      · exact ((hb1.sub hb2).div (ha1.sub ha2) hd).congr'
          (Eventually.of_forall fun t => by simp [m, mumfordPts])
      · exact (((ha1.mul hb2).sub (ha2.mul hb1)).div (ha1.sub ha2) hd).congr'
          (Eventually.of_forall fun t => by simp [m, mumfordPts])
    · have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (P₁ t).1 ≠ (P₂ t).1 := (ha1.sub ha2).eventually_ne hd |>.mono
        fun t ht h => ht (by rw [h, sub_self])
      filter_upwards [hP₁e, hP₂e, hne] with t h1 h2 h3
      exact hgen _ _ _ _ h1.1 h2.1 h3 h1.2 h2.2

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- **Affine model points are in the cone** (given the anchor `P₀ ∈` cone). -/
theorem ThetaData.affine_mem (SF : SurjFacts A) (hP₀ : baseP hp hx ∈ D.imgCone) {X : P9} (hX : A.OnQ X)
    (hX0 : X 0 ≠ 0) : X ∈ D.imgCone := by
  set Y := (X 0)⁻¹ • X
  have hY : A.OnQ Y := A.onQ_smul _ _ hX
  have hY0 : Y 0 = 1 := by simp [Y, hX0]
  obtain ⟨hYe, hR1, hR0⟩ := SF.affine_chart Y hY hY0
  have hmem := chart_mem D.isClosed_imgCone (fun x₁ y₁ x₂ y₂ h1 h2 h12 hy1 hy2 =>
    D.generic_mem hP₀ h1 h2 h12 hy1 hy2) hR1 hR0
  rw [← hYe] at hmem
  have := D.cone_smul hmem (X 0)
  rwa [smul_smul, mul_inv_cancel₀ hX0, one_smul] at this

end LSG.JacAn
