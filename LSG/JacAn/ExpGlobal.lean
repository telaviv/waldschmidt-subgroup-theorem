/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.PF

/-!
# a4, step 3: the global flow equation of `E`, and the link to `Ψ`

Fix a germ radius `G` (so `germ` is an analytic chart-4 flow solution on `ball 0 ε`), `k : ℕ`, and the lift
`Ẽ = expLift k`, analytic on `ball 0 (2ᵏ ε)`.

* `expLift_near0`: `Ẽ ∝ germ` on `ball 0 ε`;
* **`PF4_expLift`**: `Ẽ` satisfies the chart-4 projective flow equation on the whole ball (PF near 0 from the germ, then
  the identity theorem); **`PF0_expLift`**: also in the chart `X₀` (chart switch where `Ẽ₄ ≠ 0`, then identity theorem);
* `T k w = law0 (Ẽ w) P₀` (the translate of `E` by the base point `P₀ = Ψ(z₀)`); **`PF0_T`**: it satisfies PF⁰ on the
  ball (E1 with chart-4 input near 0, identity theorem);
* **`link`**: `normalize 0 (T k w) = Ψ(z₀ + w)` near `0` (anchor `law0(e₄, P₀) ∝ P₀`, affine; (U) in the chart `X₀`).
  This needs no witness that `E` leaves Θ.
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  (G : GermRad A hp hx)

lemma GermRad.mem_small {k : ℕ} {z : Fin 2 → ℂ} (hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul, norm_inv, norm_pow]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, inv_mul_lt_iff₀ (by positivity)]
  exact hz

lemma GermRad.ball_sub (k : ℕ) : ball (0 : Fin 2 → ℂ) G.ε ⊆ ball 0 (2 ^ k * G.ε) :=
  ball_subset_ball (le_mul_of_one_le_left G.pos.le (one_le_pow₀ (by norm_num)))

include G in
/-- The base nondegeneracy is recovered from the germ radius. -/
lemma GermRad.hP₀ : A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 ≠ 0 := by
  have h := (G.good 0 (mem_ball_self G.pos)).1.1
  intro h0
  simp only [germ, add_zero, normalize, Pi.smul_apply, smul_eq_mul] at h
  change (A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4)⁻¹ * A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 = 1
    at h
  rw [h0] at h; simp at h

include G in
lemma GermRad.germ_zero : germ A hp hx 0 = origin9 := LSG.JacAn.germ_zero A hp hx G.hP₀

lemma baseP_onQ : A.OnQ (baseP hp hx) := by
  simpa [baseP] using (eventually_psi_flow_onQ A hp hx).self_of_nhds.2

lemma baseP_zero : baseP hp hx 0 = 1 := by simp [baseP, psiJ, grantJ]

lemma expLift_onQ {k : ℕ} {z : Fin 2 → ℂ} (h : ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε) :
    A.OnQ (expLift A hp hx k z) :=
  A.dup_iter_onQ k (G.good _ h).2.1

include G in
/-- `Ẽ ∝ germ` on `ball 0 ε`. -/
lemma expLift_near0 (k : ℕ) {z : Fin 2 → ℂ} (hz : z ∈ ball (0 : Fin 2 → ℂ) G.ε) :
    ∃ μ : ℂ, μ ≠ 0 ∧ expLift A hp hx k z = μ • germ A hp hx z := by
  induction k with
  | zero => exact ⟨1, one_ne_zero, by simp [expLift]⟩
  | succ k ih =>
    obtain ⟨μ, hμ, he⟩ := ih
    have hmem : ((2 : ℂ) ^ (k + 1))⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε :=
      G.mem_small (G.ball_sub (k + 1) hz)
    obtain ⟨ν, hν, hν'⟩ := expLift_succ G hmem
    exact ⟨ν * μ, mul_ne_zero hν hμ, by rw [hν', he, smul_smul]⟩

lemma analyticOn_expLift (k : ℕ) : AnalyticOnNhd ℂ (expLift A hp hx k) (ball 0 (2 ^ k * G.ε)) :=
  fun _ hz => analyticAt_expLift G (G.mem_small hz)

/-- **The chart-4 projective flow equation for `Ẽ` on the whole ball.** -/
theorem PF4_expLift (k : ℕ) : ∀ z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε), PFAt A.W4 1 4 (expLift A hp hx k) z := by
  refine PFAt.of_eventually A.W4_analytic isOpen_ball (convex_ball _ _).isPreconnected (analyticOn_expLift G k)
    (mem_ball_self (by have := G.pos; positivity)) ?_
  filter_upwards [ball_mem_nhds (0 : Fin 2 → ℂ) G.pos] with z hz
  obtain ⟨hflow, -, han, -⟩ := G.good z hz
  refine (PFAt.of_flowSol A.W4_four hflow).of_eventually_smul A.W4_smul han
    (analyticOn_expLift G k z (G.ball_sub k hz)) (m := 4) (by rw [hflow.1]; exact one_ne_zero) ?_
  filter_upwards [isOpen_ball.mem_nhds hz] with z' hz'
  obtain ⟨μ, -, he⟩ := expLift_near0 G k hz'
  exact ⟨μ, he⟩

include G in
lemma expLift_zero (k : ℕ) : ∃ μ : ℂ, μ ≠ 0 ∧ expLift A hp hx k 0 = μ • origin9 := by
  obtain ⟨μ, hμ, he⟩ := expLift_near0 G k (mem_ball_self G.pos)
  exact ⟨μ, hμ, by rw [he, G.germ_zero]⟩

/-- **The chart-0 projective flow equation for `Ẽ` on the whole ball.** -/
theorem PF0_expLift (k : ℕ) : ∀ z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε), PFAt flowW 1 0 (expLift A hp hx k) z := by
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  refine PFAt.of_eventually analyticOnNhd_flowW isOpen_ball (convex_ball _ _).isPreconnected
    (analyticOn_expLift G k) (mem_ball_self hpos) ?_
  obtain ⟨μ, hμ, he⟩ := expLift_zero G k
  have h4 : ∀ᶠ z in 𝓝 (0 : Fin 2 → ℂ), expLift A hp hx k z 4 ≠ 0 := by
    have hc : ContinuousAt (fun z => expLift A hp hx k z 4) 0 :=
      (continuous_apply 4).continuousAt.comp (analyticAt_expLift G (G.mem_small (mem_ball_self hpos))).continuousAt
    refine hc.eventually_ne ?_
    show expLift A hp hx k 0 4 ≠ 0
    rw [he]; simp [origin9, hμ]
  filter_upwards [h4, ball_mem_nhds (0 : Fin 2 → ℂ) hpos] with z hz4 hz
  exact A.PFAt_chart (expLift_onQ G (G.mem_small hz)) hz4 (PF4_expLift G k z hz)

/-- The translate of `E` by the base point: `T k w = law0 (Ẽ w) P₀`. -/
def transP (k : ℕ) (w : Fin 2 → ℂ) : P9 := A.law0 (expLift A hp hx k w) (baseP hp hx)

lemma analyticOn_transP (k : ℕ) : AnalyticOnNhd ℂ (transP (A := A) (hp := hp) (hx := hx) k)
    (ball 0 (2 ^ k * G.ε)) := fun w hw => by
  have hpr : AnalyticAt ℂ (fun w => (expLift A hp hx k w, baseP hp hx)) w :=
    (analyticOn_expLift G k w hw).prod analyticAt_const
  exact AnalyticAt.comp (g := fun XY : P9 × P9 => A.law0 XY.1 XY.2)
    (f := fun w => (expLift A hp hx k w, baseP hp hx)) (A.law0_analytic _ (mem_univ _)) hpr

/-- `law0(e₄, Y) = s · (−8 Y₀) · Y`. -/
lemma A1Facts.law0_origin_left (Y : P9) : A.law0 origin9 Y = (A.swapSign * (-8 * Y 0)) • Y := by
  rw [A.law0_swap, A.law0_origin, smul_smul]

include G in
/-- `T k 0 ∝ P₀` with a nonzero factor. -/
lemma transP_zero (k : ℕ) : ∃ a : ℂ, a ≠ 0 ∧ transP (A := A) (hp := hp) (hx := hx) k 0 = a • baseP hp hx := by
  obtain ⟨μ, hμ, he⟩ := expLift_zero G k
  refine ⟨μ ^ 2 * (A.swapSign * (-8 * baseP hp hx 0)), ?_, ?_⟩
  · rw [baseP_zero]
    exact mul_ne_zero (pow_ne_zero 2 hμ) (mul_ne_zero A.swapSign_ne (by norm_num))
  · rw [transP, he, A.law0_smul_left, A.law0_origin_left, smul_smul]

/-- **PF⁰ for the translate `T` on the whole ball** (E1 with chart-4 input near 0). -/
theorem PF0_transP (k : ℕ) :
    ∀ w ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε), PFAt flowW 1 0 (transP (A := A) (hp := hp) (hx := hx) k) w := by
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  refine PFAt.of_eventually analyticOnNhd_flowW isOpen_ball (convex_ball _ _).isPreconnected
    (analyticOn_transP G k) (mem_ball_self hpos) ?_
  set P₀ := baseP hp hx
  set H : (Fin 2 → ℂ) → P9 := fun w => A.law0 (germ A hp hx w) P₀
  -- `H 0 = s (−8) P₀` has nonzero `X₀`
  have hH0 : H 0 0 ≠ 0 := by
    simp only [H, G.germ_zero, A.law0_origin_left, Pi.smul_apply, smul_eq_mul, P₀, baseP_zero]
    exact mul_ne_zero (mul_ne_zero A.swapSign_ne (by norm_num)) one_ne_zero
  have hHan : ∀ w ∈ ball (0 : Fin 2 → ℂ) G.ε, AnalyticAt ℂ H w := fun w hw => by
    have hpr : AnalyticAt ℂ (fun w => (germ A hp hx w, P₀)) w := (G.good w hw).2.2.1.prod analyticAt_const
    exact AnalyticAt.comp (g := fun XY : P9 × P9 => A.law0 XY.1 XY.2)
      (f := fun w => (germ A hp hx w, P₀)) (A.law0_analytic _ (mem_univ _)) hpr
  have hne : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), H w 0 ≠ 0 :=
    ((continuous_apply 0).continuousAt.comp (hHan 0 (mem_ball_self G.pos)).continuousAt).eventually_ne hH0
  filter_upwards [hne, ball_mem_nhds (0 : Fin 2 → ℂ) G.pos] with w hw0 hw
  obtain ⟨hflow, hQ, -, -⟩ := G.good w hw
  have hPF : PFAt flowW 1 0 H w := A.PFAt_law0_40 hflow hQ baseP_onQ
  refine hPF.of_eventually_smul flowW_smul (hHan w hw) (analyticOn_transP G k w (G.ball_sub k hw))
    (m := 0) hw0 ?_
  filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
  obtain ⟨μ, -, he⟩ := expLift_near0 G k hw'
  exact ⟨μ ^ 2, by simp only [transP, he, A.law0_smul_left, H]; rfl⟩

include G in
/-- **The link**: `normalize 0 (T k w) = Ψ(z₀ + w)` near `0`. -/
theorem link (k : ℕ) : ∃ δ > 0, ∀ w ∈ ball (0 : Fin 2 → ℂ) δ,
    normalize 0 (transP (A := A) (hp := hp) (hx := hx) k w) = psiJ hp hx (abel2 B₁ B₂ p + w) := by
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  obtain ⟨a, ha, hT0⟩ := transP_zero G k
  have hT00 : transP (A := A) (hp := hp) (hx := hx) k 0 0 ≠ 0 := by
    rw [hT0]; simp [baseP_zero, ha]
  have hTc : ContinuousAt (fun w => transP (A := A) (hp := hp) (hx := hx) k w 0) 0 :=
    (continuous_apply 0).continuousAt.comp (analyticOn_transP G k 0 (mem_ball_self hpos)).continuousAt
  have hev := Filter.Eventually.and (hTc.eventually_ne hT00) (Filter.Eventually.and
    (ball_mem_nhds (0 : Fin 2 → ℂ) hpos) (eventually_psi_flow_onQ A hp hx))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨δ, hδ, ?_⟩
  refine flow_unique flowW contDiff_flowW 1 (fun w hw => ?_) (fun w hw => ?_) ?_
  · obtain ⟨h0, hwU, -⟩ := hball w hw
    exact (PF0_transP G k w hwU).hasFDerivAt_normalize flowW_smul
      (analyticOn_transP G k w hwU).differentiableAt h0
  · exact (hball w hw).2.2.1.2
  · rw [hT0, add_zero]
    funext l
    simp only [normalize, Pi.smul_apply, smul_eq_mul, baseP_zero, mul_one]
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    rfl

end LSG.JacAn
