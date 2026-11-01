/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn4.Generic
import LSG.JacAnV.PertLift4

/-!
# M2.3 (N5, continuation): `θ_N` follows a moving divisor `(x, y) + (α, 3)`

Base: a generic pair `p = (p₁, α)` with germ radius `G₀` (in the application, the special base of
`expP_periodic_special`). `θ_N = D.thetaN` for a `θ`-datum over any base, and `z₀` with `P₀ = b • θ_N(z₀)`.

* `expLift_eq_smul'`: `expLift_{G₀} k v ∥ θ_N(v)` (base independence of `E`);
* `transP_eq_smul`: `transP k v = μ • θ_N(v + z₀)` (law 0 is column 0 of the laws);
* `eventually_zero_of_mul`: the identity-theorem step in several variables;
* **`follow_theta_local`**: along a path `(u, Y) + (α, 3)` from the base, at each time `s` there is a branch `B` at
  `u s` carrying the path near `s` such that, for `x` near `u s`,
  `θ_N(z₀ + A(s) + B.I x − B.I(u s)) ∥ grantJ(mumfordPts x (B.Y x) α 3)`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

/-- **Identity theorem, several variables**: `f g = 0` near `0` with `f` frequently nonzero gives `g = 0` near `0`. -/
lemma eventually_zero_of_mul {f g : (Fin 2 → ℂ) → ℂ}
    (h : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), AnalyticAt ℂ f w ∧ AnalyticAt ℂ g w ∧ f w * g w = 0)
    (hf : ∃ᶠ w in 𝓝 (0 : Fin 2 → ℂ), f w ≠ 0) : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), g w = 0 := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  have hfan : AnalyticOnNhd ℂ f (ball 0 ρ) := fun w hw => (hball w hw).1
  have hzero : ∀ w ∈ ball (0 : Fin 2 → ℂ) ρ, g w = 0 := by
    intro w₁ hw₁
    by_contra hg
    have hev : f =ᶠ[𝓝 w₁] 0 := by
      filter_upwards [((hball w₁ hw₁).2.1.continuousAt.eventually_ne hg),
        isOpen_ball.mem_nhds hw₁] with y hy hyb
      exact (mul_eq_zero.mp (hball y hyb).2.2).resolve_right hy
    have hf0 := hfan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hw₁ hev
    obtain ⟨w, hw, hwb⟩ := (hf.and_eventually (isOpen_ball.mem_nhds (mem_ball_self hρ))).exists
    exact hw (hf0 hwb)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with w hw using hzero w hw

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  (G₀ : GermRad A hp hx)
  {B₁' B₂' : LocalBranch f₅ 2} {p' : ℂ × ℂ} {hp' : p' ∈ dom2 B₁' B₂'} {hx' : p'.1 ≠ p'.2}
  {G : GermRad A hp' hx'} (D : ThetaData G)

include G₀ in
/-- `expLift` at the base `G₀` is a multiple of `θ_N` (of a datum over any base). -/
lemma expLift_eq_smul' (k : ℕ) {v : Fin 2 → ℂ} (hv : v ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G₀.ε)) :
    ∃ σ : ℂ, expLift A hp hx k v = σ • D.thetaN v := by
  have h := (expP_eq G₀ (G₀.mem_small hv)).symm.trans
    ((congrFun (expP_base_indep G₀ G) v).trans (D.expP_eq_thetaN v))
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.symm⟩

include G₀ in
/-- `transP k v = μ • θ_N(v + z₀)`. -/
lemma transP_eq_smul {z₀ : Fin 2 → ℂ} {b : ℂ} (hb : baseP hp hx = b • D.thetaN z₀) (k : ℕ)
    {v : Fin 2 → ℂ} (hv : v ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G₀.ε)) :
    ∃ μ : ℂ, transP (A := A) (hp := hp) (hx := hx) k v = μ • D.thetaN (v + z₀) := by
  obtain ⟨σ, hσ⟩ := expLift_eq_smul' G₀ D k hv
  obtain ⟨κ, -, hκ⟩ := D.laws_eq
  refine ⟨σ ^ 2 * b ^ 2 * (κ * D.thetaN (v - z₀) 0), funext fun m => ?_⟩
  rw [transP, hσ, hb, A.law0_smul_left, A.law0_smul_right]
  simp only [Pi.smul_apply, smul_eq_mul, A.law0_lawK, hκ]
  ring

include G₀ in
/-- **From `transP` to `θ_N`**: a local `Par` with an analytic chart-0 map `Ψ` transfers to `θ_N(z₀ + ·)`. -/
lemma par_theta_of_transP {z₀ : Fin 2 → ℂ} {b : ℂ} (hb : baseP hp hx = b • D.thetaN z₀) (k : ℕ)
    {c : Fin 2 → ℂ} (hc : c ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G₀.ε)) {Ψ : (Fin 2 → ℂ) → P9}
    (hΨ : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), AnalyticAt ℂ Ψ w)
    (hpar : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), Par (transP (A := A) (hp := hp) (hx := hx) k (c + w)) (Ψ w)) :
    ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), Par (D.thetaN (z₀ + c + w)) (Ψ w) := by
  have hball : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), c + w ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G₀.ε) := by
    have hcont : ContinuousAt (fun w : Fin 2 → ℂ => c + w) 0 := (continuous_const.add continuous_id).continuousAt
    exact hcont.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hc)
  -- some coordinate of `transP` is frequently nonzero
  have hfr := frequently_transP_ne (G := G₀) k hc
  have hm : ∃ m : Fin 9, ∃ᶠ w in 𝓝 (0 : Fin 2 → ℂ),
      transP (A := A) (hp := hp) (hx := hx) k (c + w) m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hfr
    have : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), ∀ m : Fin 9, transP (A := A) (hp := hp) (hx := hx) k (c + w) m = 0 :=
      eventually_all.mpr fun m => by simpa [Filter.Frequently] using hcon m
    filter_upwards [this] with w hw
    exact fun h => h (funext hw)
  obtain ⟨m, hmf⟩ := hm
  have hθan : ∀ w, AnalyticAt ℂ (fun w => D.thetaN (z₀ + c + w)) w := fun w =>
    (D.analyticAt_thetaN _).comp (analyticAt_const.add analyticAt_id)
  have key : ∀ a b' : Fin 9, ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ),
      D.thetaN (z₀ + c + w) a * Ψ w b' - D.thetaN (z₀ + c + w) b' * Ψ w a = 0 := by
    intro a b'
    refine eventually_zero_of_mul (f := fun w => transP (A := A) (hp := hp) (hx := hx) k (c + w) m) ?_ hmf
    filter_upwards [hball, hΨ, hpar] with w hw hΨw hpw
    refine ⟨(analyticAt_pi_iff.mp ((analyticOn_transP G₀ k (c + w) hw).comp
      (analyticAt_const.add analyticAt_id))) m, ?_, ?_⟩
    · exact (((analyticAt_pi_iff.mp (hθan w)) a).mul ((analyticAt_pi_iff.mp hΨw) b')).sub
        (((analyticAt_pi_iff.mp (hθan w)) b').mul ((analyticAt_pi_iff.mp hΨw) a))
    · obtain ⟨μ, hμ⟩ := transP_eq_smul G₀ D hb k hw
      have e := hpw a b'
      rw [hμ] at e ⊢
      rw [show c + w + z₀ = z₀ + c + w by abel] at e ⊢
      simp only [Pi.smul_apply, smul_eq_mul] at e ⊢
      linear_combination D.thetaN (z₀ + c + w) m * e
  filter_upwards [eventually_all.mpr fun a => eventually_all.mpr fun b' => key a b'] with w hw
  intro a b'
  exact sub_eq_zero.mp (hw a b')

include G₀ in
/-- **`θ_N` follows the moving divisor `(u, Y) + (α, y₀)` in a local `x`-chart.** -/
theorem follow_theta_local {z₀ : Fin 2 → ℂ} {b : ℂ} (hb : baseP hp hx = b • D.thetaN z₀) (k : ℕ)
    {α y₀ : ℂ} (hαB : α ∈ ball B₂.x₀ B₂.r) (hy₀ : B₂.Y α = y₀)
    {u Y : ℝ → ℂ} {Ap : ℝ → (Fin 2 → ℂ)} (hA : IsAbelAlong f₅ 2 u Y Ap) (hA0 : Ap 0 = 0)
    (hu : ContinuousOn u (Icc 0 1)) (hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u t ≠ α)
    (hstart : mumfordPts (u 0) (Y 0) α y₀ = mumford B₁ B₂ p)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, Ap t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G₀.ε)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ B : LocalBranch f₅ 2, ∃ ε > 0,
      (∀ t ∈ ball s ε ∩ Icc 0 1, u t ∈ ball B.x₀ B.r ∧ B.Y (u t) = Y t ∧
        ∀ t' ∈ ball s ε ∩ Icc 0 1, Ap t' - Ap t = B.I (u t') - B.I (u t)) ∧
      ∀ᶠ x in 𝓝 (u s), x ∈ ball B.x₀ B.r ∧ x ≠ α ∧
        Par (D.thetaN (z₀ + Ap s + (B.I x - B.I (u s)))) (grantJ (mumfordPts x (B.Y x) α y₀)) := by
  obtain ⟨B, ε, hε, hB⟩ := hA s hs
  have hs' := hB s ⟨mem_ball_self hε, hs⟩
  refine ⟨B, ε, hε, hB, ?_⟩
  have hpq : (u s, α) ∈ dom2 B B₂ := ⟨hs'.1, hαB⟩
  have hxq : (u s, α).1 ≠ (u s, α).2 := hdiag s hs
  set Ψ : (Fin 2 → ℂ) → P9 := fun w => psiJ hpq hxq (abel2 B B₂ (u s, α) + w) with hΨdef
  have hΨf : FlowNear Ψ := by filter_upwards [psi_flowNear hpq hxq] with w hw using hw.1
  have hΨan : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), AnalyticAt ℂ Ψ w := by
    filter_upwards [psi_flowNear hpq hxq] with w hw using hw.2
  have hΨ0 : Ψ 0 = grantJ (mumfordPts (u s) (Y s) ((fun _ : ℝ => α) s) ((fun _ : ℝ => y₀) s)) := by
    simp only [Ψ, add_zero, psiJ, localExp_abel2_self, mumford_eq_mumfordPts]
    rw [hs'.2.1, hy₀]
  have hU' : ∀ t ∈ Icc (0 : ℝ) 1, Ap t + (fun _ : ℝ => (0 : Fin 2 → ℂ)) t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G₀.ε) :=
    fun t ht => by simpa using hU t ht
  have hfol := follow_par G₀ k hA (abelAlong_const B₂ hαB hy₀) hA0 rfl hu continuousOn_const hdiag hstart hU'
    s hs Ψ hΨf hΨ0
  have hfol' : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), Par (transP (A := A) (hp := hp) (hx := hx) k (Ap s + w)) (Ψ w) := by
    filter_upwards [hfol] with w hw
    simpa using hw
  have par1 := par_theta_of_transP G₀ D hb k (hU s hs) hΨan hfol'
  -- pull back along `x ↦ B.I x − B.I (u s)`
  have hφ : Tendsto (fun x => B.I x - B.I (u s)) (𝓝 (u s)) (𝓝 0) := by
    have h := ((B.I_an _ hs'.1).continuousAt.tendsto).sub (tendsto_const_nhds (x := B.I (u s)))
    simpa using h
  have hq : Tendsto (fun x : ℂ => (x, α)) (𝓝 (u s)) (𝓝 (u s, α)) :=
    (continuous_id.prodMk continuous_const).tendsto _
  filter_upwards [hφ.eventually par1, hq.eventually (abelInv_abel2 hpq hxq), isOpen_ball.mem_nhds hs'.1,
    (continuous_id.continuousAt (x := u s)).eventually_ne (hdiag s hs)] with x hx1 hx2 hx3 hx4
  refine ⟨hx3, hx4, ?_⟩
  have habel : abel2 B B₂ (u s, α) + (B.I x - B.I (u s)) = abel2 B B₂ (x, α) := by
    simp only [abel2]; abel
  have hΨx : Ψ (B.I x - B.I (u s)) = grantJ (mumfordPts x (B.Y x) α y₀) := by
    simp only [Ψ, habel, psiJ, localExp, Function.comp, hx2, mumford_eq_mumfordPts, hy₀]
  rw [← hΨx]
  exact hx1

end LSG.JacAn
