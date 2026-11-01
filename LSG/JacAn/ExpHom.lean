/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.ExpGlobal

/-!
# a4, step 4: the homomorphism, inversion and periodicity (no witness that `E` leaves Θ)

Projective equalities are stated as parallelism `Par X Y` (all 2×2 minors vanish). With `Ẽ = expLift k`,
`T w = law0 (Ẽ w) P₀` and `U = ball 0 (2ᵏ ε)`:

* `par_of_eventually`: the identity theorem for parallelism of analytic maps on a connected open set;
* `PF0_law0_expLift`: `z ↦ law0 (Ẽ z) Y` satisfies PF⁰ on `U` for any `Y ∈ V(Q)` with `Y₀ ≠ 0`;
* **`hom_trans`** (translated homomorphism): `law0 (Ẽ z) (T w) ∥ T (z + w)` for `z, w, z + w ∈ U`;
* **`inv_trans`** (inversion): `Ẽ a ∥ law0 (T a) (negP P₀)` for `a ∈ U`;
* **`periodic_of_trans`** (periods): if `T c = λ • P₀` (`λ ≠ 0`), then `Ẽ (z + c) ∥ Ẽ z`, i.e. `E (z + c) = E z`, for
  all `z` with `z, z + c ∈ U`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

/-- Parallelism of two vectors of `ℂ⁹` (projective equality when both are nonzero). -/
def Par (X Y : P9) : Prop := ∀ a b : Fin 9, X a * Y b = X b * Y a

lemma Par.symm {X Y : P9} (h : Par X Y) : Par Y X := fun a b => by linear_combination -(h a b)

lemma Par.smul_left {X Y : P9} (c : ℂ) (h : Par X Y) : Par (c • X) Y := fun a b => by
  simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * h a b

lemma Par.smul_right {X Y : P9} (c : ℂ) (h : Par X Y) : Par X (c • Y) := (h.symm.smul_left c).symm

lemma par_self (X : P9) : Par X X := fun a b => by ring

lemma Par.trans {X Y Z : P9} (h₁ : Par X Y) (h₂ : Par Y Z) {m : Fin 9} (hm : Y m ≠ 0) : Par X Z := by
  intro a b
  have key : (X a * Z b - X b * Z a) * (Y m * Y m) = 0 := by
    linear_combination (Z b * Y m) * h₁ a m - (Z a * Y m) * h₁ b m + (X m * Y a) * h₂ m b -
      (X m * Y b) * h₂ m a
  have := (mul_eq_zero.mp key).resolve_right (mul_ne_zero hm hm)
  linear_combination this

lemma Par.eq_smul {X Y : P9} (h : Par X Y) {m : Fin 9} (hm : X m ≠ 0) : Y = (Y m / X m) • X := by
  funext b
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination (h m b)

lemma par_normalize (c : Fin 9) (X : P9) : Par (normalize c X) X := by
  simpa [normalize] using (par_self X).smul_left (X c)⁻¹

/-- **Identity theorem for parallelism.** -/
theorem par_of_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E}
    (hUc : IsPreconnected U) {F₁ F₂ : E → P9} (h₁ : AnalyticOnNhd ℂ F₁ U) (h₂ : AnalyticOnNhd ℂ F₂ U)
    {u₀ : E} (hu₀ : u₀ ∈ U) (h : ∀ᶠ u in 𝓝 u₀, Par (F₁ u) (F₂ u)) : ∀ u ∈ U, Par (F₁ u) (F₂ u) := by
  intro u hu a b
  have hc : ∀ (F : E → P9), AnalyticOnNhd ℂ F U → ∀ m, AnalyticOnNhd ℂ (fun u => F u m) U :=
    fun F hF m z hz => (analyticAt_pi_iff.mp (hF z hz)) m
  have hφ : AnalyticOnNhd ℂ (fun u => F₁ u a * F₂ u b - F₁ u b * F₂ u a) U := fun z hz =>
    ((hc F₁ h₁ a z hz).mul (hc F₂ h₂ b z hz)).sub ((hc F₁ h₁ b z hz).mul (hc F₂ h₂ a z hz))
  have h0 : (fun u => F₁ u a * F₂ u b - F₁ u b * F₂ u a) =ᶠ[𝓝 u₀] 0 := by
    filter_upwards [h] with z hz
    simp [hz a b]
  have := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hu₀ h0 hu
  simp only [Pi.zero_apply] at this
  linear_combination this

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  (G : GermRad A hp hx)

lemma analyticAt_law0_comp {F : E' → P9} {Y : P9} {u : E'} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (hF : AnalyticAt ℂ F u) : AnalyticAt ℂ (fun u => A.law0 (F u) Y) u := by
  have hpr : AnalyticAt ℂ (fun u => (F u, Y)) u := hF.prod analyticAt_const
  exact AnalyticAt.comp (g := fun XY : P9 × P9 => A.law0 XY.1 XY.2) (f := fun u => (F u, Y))
    (A.law0_analytic _ (mem_univ _)) hpr

/-- **PF⁰ for `z ↦ law0 (Ẽ z) Y`** on `U`, for `Y ∈ V(Q)` with `Y₀ ≠ 0`. -/
theorem PF0_law0_expLift (k : ℕ) {Y : P9} (hYQ : A.OnQ Y) (hY0 : Y 0 ≠ 0) :
    ∀ z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε), PFAt flowW 1 0 (fun z => A.law0 (expLift A hp hx k z) Y) z := by
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  refine PFAt.of_eventually analyticOnNhd_flowW isOpen_ball (convex_ball _ _).isPreconnected
    (fun z hz => analyticAt_law0_comp (analyticOn_expLift G k z hz)) (mem_ball_self hpos) ?_
  set H : (Fin 2 → ℂ) → P9 := fun w => A.law0 (germ A hp hx w) Y
  have hH0 : H 0 0 ≠ 0 := by
    simp only [H, G.germ_zero, A.law0_origin_left, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero A.swapSign_ne (mul_ne_zero (by norm_num) hY0)) hY0
  have hHan : ∀ w ∈ ball (0 : Fin 2 → ℂ) G.ε, AnalyticAt ℂ H w := fun w hw =>
    analyticAt_law0_comp (G.good w hw).2.2.1
  have hne : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), H w 0 ≠ 0 :=
    ((continuous_apply 0).continuousAt.comp (hHan 0 (mem_ball_self G.pos)).continuousAt).eventually_ne hH0
  filter_upwards [hne, ball_mem_nhds (0 : Fin 2 → ℂ) G.pos] with w hw0 hw
  obtain ⟨hflow, hQ, -, -⟩ := G.good w hw
  refine (A.PFAt_law0_40 hflow hQ hYQ).of_eventually_smul flowW_smul (hHan w hw)
    (analyticAt_law0_comp (analyticOn_expLift G k w (G.ball_sub k hw))) (m := 0) hw0 ?_
  filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
  obtain ⟨μ, -, he⟩ := expLift_near0 G k hw'
  exact ⟨μ ^ 2, by simp only [he, A.law0_smul_left, H]⟩

lemma psiJ_zero (z : Fin 2 → ℂ) : psiJ hp hx z 0 = 1 := by simp [psiJ, grantJ]

lemma analyticOn_transP' (k : ℕ) {u : Fin 2 → ℂ} (hu : u ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    AnalyticAt ℂ (transP (A := A) (hp := hp) (hx := hx) k) u := analyticOn_transP G k u hu

include G in
/-- Near `0`, `T w = (T w)₀ • Ψ(z₀ + w)`. -/
lemma eventually_transP_eq (k : ℕ) :
    ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ),
      transP (A := A) (hp := hp) (hx := hx) k w =
        (transP (A := A) (hp := hp) (hx := hx) k w 0) • psiJ hp hx (abel2 B₁ B₂ p + w) := by
  obtain ⟨δ, hδ, hl⟩ := link G k
  filter_upwards [ball_mem_nhds (0 : Fin 2 → ℂ) hδ] with w hw
  have h := hl w hw
  have h0 : transP (A := A) (hp := hp) (hx := hx) k w 0 ≠ 0 := by
    intro h0
    have := congrFun h 0
    simp [normalize, h0, psiJ_zero] at this
  rw [← h]
  simp [normalize, smul_smul, h0]

include G in
/-- **Translated homomorphism near `(0, 0)`.** -/
lemma hom_trans_near (k : ℕ) : ∀ᶠ zw in 𝓝 ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ)),
    Par (A.law0 (expLift A hp hx k zw.1) (transP (A := A) (hp := hp) (hx := hx) k zw.2))
      (transP (A := A) (hp := hp) (hx := hx) k (zw.1 + zw.2)) := by
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  obtain ⟨δ₁, hδ₁, h1⟩ := Metric.eventually_nhds_iff_ball.mp
    ((eventually_transP_eq G k).and (eventually_psi_flow_onQ A hp hx))
  obtain ⟨μ, hμ, he⟩ := expLift_zero G k
  -- joint continuity of `(z, w) ↦ law0 (Ẽ z) Ψ(z₀ + w)` at `(0, 0)`
  set Φ : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ :=
    fun zw => A.law0 (expLift A hp hx k zw.1) (psiJ hp hx (abel2 B₁ B₂ p + zw.2)) 0
  have hΦc : ContinuousAt Φ (0, 0) := by
    have hE : ContinuousAt (expLift A hp hx k) 0 := (analyticOn_expLift G k 0 (mem_ball_self hpos)).continuousAt
    have hΨ : ContinuousAt (fun w => psiJ hp hx (abel2 B₁ B₂ p + w)) 0 :=
      (eventually_psi_flow_onQ A hp hx).self_of_nhds.1.2.continuousAt
    have hL : ContinuousAt (fun XY : P9 × P9 => A.law0 XY.1 XY.2)
        (expLift A hp hx k 0, psiJ hp hx (abel2 B₁ B₂ p + 0)) :=
      (A.law0_analytic _ (mem_univ _)).continuousAt
    have hpair : ContinuousAt (fun zw : (Fin 2 → ℂ) × (Fin 2 → ℂ) =>
        (expLift A hp hx k zw.1, psiJ hp hx (abel2 B₁ B₂ p + zw.2))) (0, 0) :=
      (hE.comp_of_eq continuousAt_fst rfl).prodMk (hΨ.comp_of_eq continuousAt_snd rfl)
    exact (continuous_apply 0).continuousAt.comp
      (ContinuousAt.comp_of_eq (g := fun XY : P9 × P9 => A.law0 XY.1 XY.2) hL hpair rfl)
  have hΦ0 : Φ (0, 0) ≠ 0 := by
    simp only [Φ, he, A.law0_smul_left, A.law0_origin_left, Pi.smul_apply, smul_eq_mul, psiJ_zero, add_zero]
    simp [hμ, A.swapSign_ne]
  obtain ⟨ρ₀, hρ₀, hΦb⟩ := Metric.eventually_nhds_iff_ball.mp (hΦc.eventually_ne hΦ0)
  set r := min (min (δ₁ / 2) ρ₀) (min G.ε (2 ^ k * G.ε)) / 2
  have hr : 0 < r := half_pos (lt_min (lt_min (half_pos hδ₁) hρ₀) (lt_min G.pos hpos))
  have hrδ : r ≤ δ₁ / 2 := by
    have := min_le_left (min (δ₁ / 2) ρ₀) (min G.ε (2 ^ k * G.ε))
    have := min_le_left (δ₁ / 2) ρ₀
    have : r ≤ min (min (δ₁ / 2) ρ₀) (min G.ε (2 ^ k * G.ε)) := half_le_self (le_of_lt (lt_min (lt_min
      (half_pos hδ₁) hρ₀) (lt_min G.pos hpos)))
    linarith
  have hrρ : r < ρ₀ := by
    have h := min_le_right (δ₁ / 2) ρ₀
    have h' := min_le_left (min (δ₁ / 2) ρ₀) (min G.ε (2 ^ k * G.ε))
    have : r < min (min (δ₁ / 2) ρ₀) (min G.ε (2 ^ k * G.ε)) :=
      half_lt_self (lt_min (lt_min (half_pos hδ₁) hρ₀) (lt_min G.pos hpos))
    linarith
  have hrU : r < 2 ^ k * G.ε := by
    have h := min_le_right G.ε (2 ^ k * G.ε)
    have h' := min_le_right (min (δ₁ / 2) ρ₀) (min G.ε (2 ^ k * G.ε))
    have : r < min (min (δ₁ / 2) ρ₀) (min G.ε (2 ^ k * G.ε)) :=
      half_lt_self (lt_min (lt_min (half_pos hδ₁) hρ₀) (lt_min G.pos hpos))
    linarith
  have hsum : ∀ z ∈ ball (0 : Fin 2 → ℂ) r, ∀ w ∈ ball (0 : Fin 2 → ℂ) r,
      z + w ∈ ball (0 : Fin 2 → ℂ) δ₁ := by
    intro z hz w hw
    rw [mem_ball_zero_iff] at hz hw ⊢
    calc ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le _ _
      _ < δ₁ := by linarith
  have hprod : ∀ z ∈ ball (0 : Fin 2 → ℂ) r, ∀ w ∈ ball (0 : Fin 2 → ℂ) r, (z, w) ∈ ball (0, 0) ρ₀ := by
    intro z hz w hw
    rw [mem_ball_zero_iff] at hz hw
    rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]
    exact max_lt (hz.trans hrρ) (hw.trans hrρ)
  have hwδ : ∀ w ∈ ball (0 : Fin 2 → ℂ) r, w ∈ ball (0 : Fin 2 → ℂ) δ₁ := fun w hw =>
    ball_subset_ball (hrδ.trans (half_le_self hδ₁.le)) hw
  -- for fixed `w`: `normalize 0 (law0 (Ẽ z) Ψ(z₀ + w)) = Ψ(z₀ + z + w)` on `ball 0 r`
  have key : ∀ w ∈ ball (0 : Fin 2 → ℂ) r, ∀ z ∈ ball (0 : Fin 2 → ℂ) r,
      normalize 0 (A.law0 (expLift A hp hx k z) (psiJ hp hx (abel2 B₁ B₂ p + w))) =
        psiJ hp hx (abel2 B₁ B₂ p + (z + w)) := by
    intro w hw
    set Y := psiJ hp hx (abel2 B₁ B₂ p + w)
    have hYQ : A.OnQ Y := (h1 w (hwδ w hw)).2.2
    have hY0 : Y 0 = 1 := psiJ_zero _
    refine flow_unique flowW contDiff_flowW 1 (fun z hz => ?_) (fun z hz => ?_) ?_
    · have hzU : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := ball_subset_ball hrU.le hz
      exact (PF0_law0_expLift G k hYQ (by rw [hY0]; exact one_ne_zero) z hzU).hasFDerivAt_normalize
        flowW_smul (analyticAt_law0_comp (analyticOn_expLift G k z hzU)).differentiableAt
        (hΦb (z, w) (hprod z hz w hw))
    · have hflow := (h1 _ (hsum z hz w hw)).2.1.2
      have := hflow.comp z ((hasFDerivAt_id z).add_const w)
      simpa [add_assoc] using this
    · rw [he, A.law0_smul_left, A.law0_origin_left, smul_smul, zero_add]
      funext l
      simp only [normalize, Pi.smul_apply, smul_eq_mul, hY0]
      have : μ ^ 2 * (A.swapSign * (-8 * 1)) * 1 ≠ 0 := by simp [hμ, A.swapSign_ne]
      have hs := A.swapSign_ne
      field_simp
      rfl
  filter_upwards [prod_mem_nhds (ball_mem_nhds (0 : Fin 2 → ℂ) hr) (ball_mem_nhds (0 : Fin 2 → ℂ) hr)]
    with zw hzw
  obtain ⟨hz, hw⟩ := hzw
  set z := zw.1; set w := zw.2
  have hTw := (h1 w (hwδ w hw)).1
  have hTzw := (h1 (z + w) (hsum z hz w hw)).1
  have hk := key w hw z hz
  rw [hTw, A.law0_smul_right, hTzw]
  refine ((Par.smul_left _ ?_).smul_right _)
  rw [← hk]
  exact (par_normalize 0 _).symm

/-- **The translated homomorphism**: `law0 (Ẽ z) (T w) ∥ T (z + w)` for `z, w, z + w ∈ U`. -/
theorem hom_trans (k : ℕ) {z w : Fin 2 → ℂ} (hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hw : w ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) (hzw : z + w ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    Par (A.law0 (expLift A hp hx k z) (transP (A := A) (hp := hp) (hx := hx) k w))
      (transP (A := A) (hp := hp) (hx := hx) k (z + w)) := by
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  set R := 2 ^ k * G.ε
  set D : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ)) :=
    (Prod.fst ⁻¹' ball 0 R) ∩ (Prod.snd ⁻¹' ball 0 R) ∩ ((fun zw => zw.1 + zw.2) ⁻¹' ball 0 R)
  have hDc : Convex ℝ D := by
    have h1 := (convex_ball (0 : Fin 2 → ℂ) R).linear_preimage (LinearMap.fst ℝ (Fin 2 → ℂ) (Fin 2 → ℂ))
    have h2 := (convex_ball (0 : Fin 2 → ℂ) R).linear_preimage (LinearMap.snd ℝ (Fin 2 → ℂ) (Fin 2 → ℂ))
    have h3 := (convex_ball (0 : Fin 2 → ℂ) R).linear_preimage
      (LinearMap.fst ℝ (Fin 2 → ℂ) (Fin 2 → ℂ) + LinearMap.snd ℝ (Fin 2 → ℂ) (Fin 2 → ℂ))
    exact (h1.inter h2).inter h3
  have hT : ∀ u ∈ ball (0 : Fin 2 → ℂ) R, AnalyticAt ℂ (transP (A := A) (hp := hp) (hx := hx) k) u :=
    fun u hu => analyticOn_transP G k u hu
  have hF₁ : AnalyticOnNhd ℂ (fun zw : (Fin 2 → ℂ) × (Fin 2 → ℂ) =>
      A.law0 (expLift A hp hx k zw.1) (transP (A := A) (hp := hp) (hx := hx) k zw.2)) D := by
    intro zw hzw
    have hpr : AnalyticAt ℂ (fun zw : (Fin 2 → ℂ) × (Fin 2 → ℂ) =>
        (expLift A hp hx k zw.1, transP (A := A) (hp := hp) (hx := hx) k zw.2)) zw :=
      ((analyticOn_expLift G k zw.1 hzw.1.1).comp analyticAt_fst).prod ((hT zw.2 hzw.1.2).comp analyticAt_snd)
    exact AnalyticAt.comp (g := fun XY : P9 × P9 => A.law0 XY.1 XY.2) (A.law0_analytic _ (mem_univ _)) hpr
  have hF₂ : AnalyticOnNhd ℂ (fun zw : (Fin 2 → ℂ) × (Fin 2 → ℂ) =>
      transP (A := A) (hp := hp) (hx := hx) k (zw.1 + zw.2)) D := fun zw hzw =>
    AnalyticAt.comp (g := transP (A := A) (hp := hp) (hx := hx) k)
      (f := fun zw : (Fin 2 → ℂ) × (Fin 2 → ℂ) => zw.1 + zw.2) (hT _ hzw.2) (analyticAt_fst.add analyticAt_snd)
  have h0 : ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ)) ∈ D := by
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [hpos]
  exact par_of_eventually hDc.isPreconnected hF₁ hF₂ h0 (hom_trans_near G k) (z, w) ⟨⟨hz, hw⟩, hzw⟩

lemma Par.of_smul_left {X Y : P9} {a : ℂ} (ha : a ≠ 0) (h : Par (a • X) Y) : Par X Y := by
  have := h.smul_left a⁻¹
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this

lemma Par.of_smul_right {X Y : P9} {a : ℂ} (ha : a ≠ 0) (h : Par X (a • Y)) : Par X Y :=
  (h.symm.of_smul_left ha).symm

include G in
/-- **Inversion**: `Ẽ a ∥ law0 (T a) (negP P₀)` on `U`. -/
theorem inv_trans (k : ℕ) {a : Fin 2 → ℂ} (ha : a ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    Par (expLift A hp hx k a) (A.law0 (transP (A := A) (hp := hp) (hx := hx) k a) (A.negP (baseP hp hx))) := by
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  refine par_of_eventually (convex_ball _ _).isPreconnected (analyticOn_expLift G k)
    (fun u hu => analyticAt_law0_comp (analyticOn_transP G k u hu)) (mem_ball_self hpos) ?_ a ha
  filter_upwards [eventually_transP_eq G k, ball_mem_nhds (0 : Fin 2 → ℂ) G.pos] with u hT hu
  obtain ⟨μ, -, he⟩ := expLift_near0 G k hu
  rw [he, hT, A.law0_smul_left]
  refine (Par.smul_left _ ?_).smul_right _
  exact par_normalize 4 _

include G in
/-- **Periods**: if `T c = λ • P₀` with `λ ≠ 0`, then `Ẽ (z + c) ∥ Ẽ z` whenever `z, z + c ∈ U`. -/
theorem periodic_of_trans (k : ℕ) {c : Fin 2 → ℂ} (hcU : c ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hc : ∃ l : ℂ, l ≠ 0 ∧ transP (A := A) (hp := hp) (hx := hx) k c = l • baseP hp hx)
    {z : Fin 2 → ℂ} (hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hzc : z + c ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    Par (expLift A hp hx k (z + c)) (expLift A hp hx k z) := by
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  obtain ⟨l, hl, hTc⟩ := hc
  obtain ⟨a, ha, hT0⟩ := transP_zero G k
  set R := 2 ^ k * G.ε
  have hmemD : ∀ u, u + c ∈ ball (0 : Fin 2 → ℂ) R ↔ u ∈ ball (-c) R := fun u => by
    rw [mem_ball_zero_iff, mem_ball, dist_eq_norm, sub_neg_eq_add]
  set D : Set (Fin 2 → ℂ) := ball 0 R ∩ ball (-c) R
  have hDc : Convex ℝ D := (convex_ball _ _).inter (convex_ball _ _)
  have h0D : (0 : Fin 2 → ℂ) ∈ D := ⟨mem_ball_self hpos, (hmemD 0).mp (by simpa using hcU)⟩
  have hTan : ∀ u ∈ ball (0 : Fin 2 → ℂ) R, AnalyticAt ℂ (transP (A := A) (hp := hp) (hx := hx) k) u :=
    fun u hu => analyticOn_transP G k u hu
  -- conditions near `0`
  have e1 : ∀ᶠ u in 𝓝 (0 : Fin 2 → ℂ), (transP (A := A) (hp := hp) (hx := hx) k) u 0 ≠ 0 := by
    refine ((continuous_apply 0).continuousAt.comp (hTan 0 (mem_ball_self hpos)).continuousAt).eventually_ne ?_
    show (transP (A := A) (hp := hp) (hx := hx) k) 0 0 ≠ 0
    rw [hT0]; simp [baseP_zero, ha]
  have e2 : ∀ᶠ u in 𝓝 (0 : Fin 2 → ℂ), (transP (A := A) (hp := hp) (hx := hx) k) (u + c) 0 ≠ 0 := by
    have hc' : ContinuousAt (fun u => (transP (A := A) (hp := hp) (hx := hx) k) (u + c) 0) 0 := by
      have h1 : ContinuousAt (transP (A := A) (hp := hp) (hx := hx) k) (0 + c) := by
        rw [zero_add]; exact (hTan c hcU).continuousAt
      have h2 : ContinuousAt (fun u : Fin 2 → ℂ => u + c) 0 := (continuous_id.add continuous_const).continuousAt
      exact (continuous_apply 0).continuousAt.comp (h1.comp_of_eq h2 rfl)
    refine hc'.eventually_ne ?_
    show (transP (A := A) (hp := hp) (hx := hx) k) (0 + c) 0 ≠ 0
    rw [zero_add, hTc]; simp [baseP_zero, hl]
  have e3 : ∀ᶠ u in 𝓝 (0 : Fin 2 → ℂ), A.law0 ((transP (A := A) (hp := hp) (hx := hx) k) u) (A.negP (baseP hp hx)) 4 ≠ 0 := by
    have hc' : ContinuousAt (fun u => A.law0 ((transP (A := A) (hp := hp) (hx := hx) k) u) (A.negP (baseP hp hx)) 4) 0 :=
      (continuous_apply 4).continuousAt.comp (analyticAt_law0_comp (hTan 0 (mem_ball_self hpos))).continuousAt
    refine hc'.eventually_ne ?_
    show A.law0 ((transP (A := A) (hp := hp) (hx := hx) k) 0) (A.negP (baseP hp hx)) 4 ≠ 0
    rw [hT0, A.law0_smul_left]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero 2 ha) G.hP₀
  have e4 : D ∈ 𝓝 (0 : Fin 2 → ℂ) := (isOpen_ball.inter isOpen_ball).mem_nhds h0D
  refine par_of_eventually hDc.isPreconnected (F₁ := fun u => expLift A hp hx k (u + c))
    (F₂ := expLift A hp hx k)
    (fun u hu => AnalyticAt.comp (g := expLift A hp hx k) (f := fun u => u + c)
      (analyticOn_expLift G k (u + c) ((hmemD u).mpr hu.2)) (analyticAt_id.add analyticAt_const))
    (fun u hu => analyticOn_expLift G k u hu.1) h0D ?_ z ⟨hz, (hmemD z).mp hzc⟩
  filter_upwards [e1, e2, e3, e4] with u hu1 hu2 hu3 hu4
  have huU : u ∈ ball (0 : Fin 2 → ℂ) R := hu4.1
  have hucU : u + c ∈ ball (0 : Fin 2 → ℂ) R := (hmemD u).mpr hu4.2
  -- `(transP (A := A) (hp := hp) (hx := hx) k) u ∥ (transP (A := A) (hp := hp) (hx := hx) k) (u + c)`
  have hpar : Par ((transP (A := A) (hp := hp) (hx := hx) k) u) ((transP (A := A) (hp := hp) (hx := hx) k) (u + c)) := by
    have h := hom_trans G k huU hcU hucU
    rw [hTc, A.law0_smul_right] at h
    exact h.of_smul_left (pow_ne_zero 2 hl)
  set ν := (transP (A := A) (hp := hp) (hx := hx) k) (u + c) 0 / (transP (A := A) (hp := hp) (hx := hx) k) u 0
  have hν : ν ≠ 0 := div_ne_zero hu2 hu1
  have hTν : (transP (A := A) (hp := hp) (hx := hx) k) (u + c) = ν • (transP (A := A) (hp := hp) (hx := hx) k) u := hpar.eq_smul hu1
  have hi1 := inv_trans G k hucU
  have hi2 := inv_trans G k huU
  rw [hTν, A.law0_smul_left] at hi1
  exact (hi1.of_smul_right (pow_ne_zero 2 hν)).trans hi2.symm hu3

include G in
/-- **The kernel criterion**: if `T c = λ • P₀` (`λ ≠ 0`), then `E (z + c) = E z` for all `z` with `z, z + c ∈ U`. -/
theorem expP_periodic (k : ℕ) {c : Fin 2 → ℂ} (hcU : c ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hc : ∃ l : ℂ, l ≠ 0 ∧ transP (A := A) (hp := hp) (hx := hx) k c = l • baseP hp hx)
    {z : Fin 2 → ℂ} (hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hzc : z + c ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) : expP G (z + c) = expP G z := by
  have h := periodic_of_trans G k hcU hc hz hzc
  have hne₁ := expLift_ne_zero G (G.mem_small hzc)
  have hne₂ := expLift_ne_zero G (G.mem_small hz)
  obtain ⟨m, hm⟩ : ∃ m, expLift A hp hx k (z + c) m ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hne₁ (funext hcon)
  rw [expP_eq G (G.mem_small hzc), expP_eq G (G.mem_small hz), Projectivization.mk_eq_mk_iff']
  set σ := expLift A hp hx k z m / expLift A hp hx k (z + c) m with hσ
  have he : expLift A hp hx k z = σ • expLift A hp hx k (z + c) := h.eq_smul hm
  have hs : σ ≠ 0 := by
    intro h0; rw [h0, zero_smul] at he; exact hne₂ he
  refine ⟨σ⁻¹, ?_⟩
  rw [he, smul_smul, inv_mul_cancel₀ hs, one_smul]

end LSG.JacAn
