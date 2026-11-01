/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Continuation
import LSG.JacAn.Charts

/-!
# The Abel integral along paths through Weierstrass points (a6, mixed charts)

`Continuation.lean` handles paths with `y ≠ 0`. Here a path may pass through Weierstrass points `(e, 0)` (simple
roots of `f`): near such parameters the `y`-chart `WeierChart` is used. A `PathChart` is either kind of chart;
`PathChart.F` is its Abel integral read along the path and `PathChart.Carries` says the chart contains the path point.

* `exists_injOn_ball`: `x ↦ f(x)` is injective near any `x₀` with `f'(x₀) ≠ 0`;
* `WeierChart.X_eventuallyEq`, `WeierChart.I_sub_eventually`, `WeierChart.I_sub_branch_eventually`: on overlaps,
  chart Abel integrals differ by locally constant functions (all cases reduce to "zero derivative near a point");
* `PathChart.eventually_compat`: the same along the path;
* **`exists_abelAlongW`**: the Abel integral along a continuous path in the affine curve whose zeros of `y` are simple
  roots of `f` (in particular every path when `f` is squarefree).
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

variable {f : ℂ[X]} {g : ℕ}

/-- `x ↦ f(x)` is injective near any point with `f' ≠ 0`. -/
lemma exists_injOn_ball (f : ℂ[X]) {x₀ : ℂ} (hd : (derivative f).eval x₀ ≠ 0) :
    ∃ ρ > 0, InjOn (fun x => f.eval x) (ball x₀ ρ) := by
  have hs := (f.hasStrictDerivAt x₀).hasStrictFDerivAt_equiv hd
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (hs.toOpenPartialHomeomorph _).open_source x₀
    hs.mem_toOpenPartialHomeomorph_source
  exact ⟨ρ, hρ, (hs.toOpenPartialHomeomorph _).injOn.mono hball⟩

/-- A function with zero derivative near `y₀` is constant near `y₀`. -/
lemma eventually_eq_of_hasDerivAt_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {G : ℂ → V}
    {y₀ : ℂ} (h : ∀ᶠ y in 𝓝 y₀, HasDerivAt G 0 y) : ∀ᶠ y in 𝓝 y₀, G y = G y₀ := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  filter_upwards [ball_mem_nhds y₀ hρ] with y hy
  exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball y₀ ρ).isPreconnected
    (fun z hz => (hball z hz).differentiableAt.differentiableWithinAt) (fun z hz => (hball z hz).deriv)
    hy (mem_ball_self hρ)

namespace WeierChart

/-- Two `y`-charts through the same point have the same `X` near it. -/
lemma X_eventuallyEq (W W' : WeierChart f g) {y₀ : ℂ} (hy : y₀ ∈ ball (0 : ℂ) W.r)
    (hy' : y₀ ∈ ball (0 : ℂ) W'.r) (hX : W.X y₀ = W'.X y₀) : W.X =ᶠ[𝓝 y₀] W'.X := by
  obtain ⟨ρ, hρ, hinj⟩ := exists_injOn_ball f (W.fd_ne y₀ hy)
  have c1 : ∀ᶠ y in 𝓝 y₀, W.X y ∈ ball (W.X y₀) ρ :=
    (W.X_an y₀ hy).continuousAt.preimage_mem_nhds (ball_mem_nhds _ hρ)
  have c2 : ∀ᶠ y in 𝓝 y₀, W'.X y ∈ ball (W.X y₀) ρ := by
    rw [hX]; exact (W'.X_an y₀ hy').continuousAt.preimage_mem_nhds (ball_mem_nhds _ hρ)
  filter_upwards [c1, c2, isOpen_ball.mem_nhds hy, isOpen_ball.mem_nhds hy'] with y h1 h2 h3 h4
  exact hinj h1 h2 (by simp only; rw [W.X_sq y h3, W'.X_sq y h4])

/-- **`y`-chart vs `y`-chart**: `W.I − W'.I` is locally constant near a common point. -/
lemma I_sub_eventually (W W' : WeierChart f g) {y₀ : ℂ} (hy : y₀ ∈ ball (0 : ℂ) W.r)
    (hy' : y₀ ∈ ball (0 : ℂ) W'.r) (hX : W.X y₀ = W'.X y₀) :
    ∀ᶠ y in 𝓝 y₀, W.I y - W'.I y = W.I y₀ - W'.I y₀ := by
  refine eventually_eq_of_hasDerivAt_zero (G := fun y => W.I y - W'.I y) ?_
  filter_upwards [W.X_eventuallyEq W' hy hy' hX, isOpen_ball.mem_nhds hy, isOpen_ball.mem_nhds hy']
    with y hXy h3 h4
  have := (W.I_deriv y h3).sub (W'.I_deriv y h4)
  have h0 : weierVec g f W.X y - weierVec g f W'.X y = 0 := by
    funext k; simp [weierVec, hXy]
  rwa [h0] at this

/-- **`y`-chart vs `x`-branch**: `W.I − B.I ∘ X` is locally constant near a common point. -/
lemma I_sub_branch_eventually (W : WeierChart f g) (B : LocalBranch f g) {y₀ : ℂ}
    (hy : y₀ ∈ ball (0 : ℂ) W.r) (hB : W.X y₀ ∈ ball B.x₀ B.r) (hY : B.Y (W.X y₀) = y₀) :
    ∀ᶠ y in 𝓝 y₀, W.I y - B.I (W.X y) = W.I y₀ - B.I (W.X y₀) := by
  have hy0 : y₀ ≠ 0 := hY ▸ B.Y_ne _ hB
  have hXc := (W.X_an y₀ hy).continuousAt
  have c1 : ∀ᶠ y in 𝓝 y₀, W.X y ∈ ball B.x₀ B.r := hXc.preimage_mem_nhds (isOpen_ball.mem_nhds hB)
  have hcs : ContinuousAt (fun y => B.Y (W.X y) + y) y₀ :=
    ((B.Y_an _ hB).continuousAt.comp hXc).add continuousAt_id
  have c2 : ∀ᶠ y in 𝓝 y₀, B.Y (W.X y) + y ≠ 0 := by
    refine hcs.eventually_ne ?_
    show B.Y (W.X y₀) + y₀ ≠ 0
    rw [hY]; intro h; apply hy0; linear_combination h / 2
  refine eventually_eq_of_hasDerivAt_zero (G := fun y => W.I y - B.I (W.X y)) ?_
  filter_upwards [c1, c2, isOpen_ball.mem_nhds hy] with y h1 h2 h3
  have hYy : B.Y (W.X y) = y := by
    have hsq : B.Y (W.X y) ^ 2 = y ^ 2 := by rw [B.Y_sq _ h1, W.X_sq y h3]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · exact absurd (by rw [h]; ring) h2
  have := (W.I_deriv y h3).sub (W.hasDerivAt_branch B h3 h1 hYy)
  rwa [sub_self] at this

end WeierChart

/-! ## Charts along a path -/

/-- A chart used along a path: an `x`-branch or a `y`-chart at a Weierstrass point. -/
inductive PathChart (f : ℂ[X]) (g : ℕ)
  | br (B : LocalBranch f g)
  | we (W : WeierChart f g)

namespace PathChart

/-- The chart's Abel integral read along the path `(u, Yp)`. -/
def F : PathChart f g → (ℝ → ℂ) → (ℝ → ℂ) → ℝ → (Fin g → ℂ)
  | br B, u, _, t => B.I (u t)
  | we W, _, Yp, t => W.I (Yp t)

/-- The chart contains the path point at time `t`. -/
def Carries : PathChart f g → (ℝ → ℂ) → (ℝ → ℂ) → ℝ → Prop
  | br B, u, Yp, t => u t ∈ ball B.x₀ B.r ∧ B.Y (u t) = Yp t
  | we W, u, Yp, t => Yp t ∈ ball (0 : ℂ) W.r ∧ W.X (Yp t) = u t

/-- **Compatibility along the path**: near a time where two charts both carry the path, their Abel integrals differ
by a constant. -/
theorem eventually_compat (C C' : PathChart f g) {u Yp : ℝ → ℂ} {S : Set ℝ} {τ : ℝ}
    (hYp : ContinuousWithinAt Yp S τ) (hC : C.Carries u Yp τ) (hC' : C'.Carries u Yp τ) :
    ∀ᶠ τ' in 𝓝[S] τ, C.Carries u Yp τ' → C'.Carries u Yp τ' →
      C.F u Yp τ' - C'.F u Yp τ' = C.F u Yp τ - C'.F u Yp τ := by
  cases C with
  | br B =>
    cases C' with
    | br B' =>
      refine Eventually.of_forall fun τ' h1 h2 => ?_
      exact B.I_sub_eq B' ⟨hC.1, hC'.1⟩ (hC.2.trans hC'.2.symm) ⟨h1.1, h2.1⟩
    | we W' =>
      have hG := W'.I_sub_branch_eventually B hC'.1 (hC'.2 ▸ hC.1) (by rw [hC'.2, hC.2])
      filter_upwards [hYp.eventually hG] with τ' h h1 h2
      simp only [F, Carries] at h h1 h2 hC hC' ⊢
      rw [h2.2] at h; rw [hC'.2] at h
      rw [← neg_sub, h, neg_sub]
  | we W =>
    cases C' with
    | br B' =>
      have hG := W.I_sub_branch_eventually B' hC.1 (hC.2 ▸ hC'.1) (by rw [hC.2, hC'.2])
      filter_upwards [hYp.eventually hG] with τ' h h1 h2
      simp only [F, Carries] at h h1 h2 hC hC' ⊢
      rw [h1.2] at h; rw [hC.2] at h
      exact h
    | we W' =>
      have hG := W.I_sub_eventually W' hC.1 hC'.1 (hC.2.trans hC'.2.symm)
      filter_upwards [hYp.eventually hG] with τ' h _ _
      exact h

end PathChart

/-! ## Existence of the Abel integral along mixed paths -/

section Path

variable {u Yp : ℝ → ℂ}

/-- Near a parameter where `Yp ≠ 0`, a branch carries the path. -/
lemma exists_branch_along' (hu : ContinuousOn u (Icc 0 1)) (hYp : ContinuousOn Yp (Icc 0 1))
    (hsq : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ^ 2 = f.eval (u t)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hne : Yp s ≠ 0) :
    ∃ B : LocalBranch f g, ∃ ε > 0, ∀ t ∈ ball s ε ∩ Icc 0 1,
      u t ∈ ball B.x₀ B.r ∧ B.Y (u t) = Yp t := by
  obtain ⟨B, hBx, hBy⟩ := LocalBranch.exists_of_mem (g := g) (hsq s hs) hne
  have hcu : ContinuousWithinAt u (Icc 0 1) s := hu s hs
  have h1 : ∀ᶠ t in 𝓝[Icc 0 1] s, u t ∈ ball B.x₀ B.r :=
    hcu.preimage_mem_nhdsWithin (hBx ▸ isOpen_ball.mem_nhds (mem_ball_self B.r_pos))
  have hcY : ContinuousWithinAt (fun t => B.Y (u t) + Yp t) (Icc 0 1) s := by
    have : ContinuousAt B.Y (u s) := (B.Y_an _ (hBx ▸ mem_ball_self B.r_pos)).continuousAt
    exact (this.comp_continuousWithinAt hcu).add (hYp s hs)
  have h2 : ∀ᶠ t in 𝓝[Icc 0 1] s, B.Y (u t) + Yp t ≠ 0 := by
    refine hcY.eventually_ne ?_
    show B.Y (u s) + Yp s ≠ 0
    rw [hBy]
    intro h; apply hne; linear_combination h / 2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp (h1.and (h2.and self_mem_nhdsWithin))
  refine ⟨B, ε, hε, fun t ht => ⟨(hball ht).1, ?_⟩⟩
  obtain ⟨hb, hs', htI⟩ := hball ht
  have hsq' : B.Y (u t) ^ 2 = Yp t ^ 2 := by rw [B.Y_sq _ hb, hsq t htI]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with h | h
  · exact h
  · exact absurd (by rw [h]; ring) hs'

/-- Near a parameter where `Yp = 0` (a simple root), a `y`-chart carries the path. -/
lemma exists_weier_along (hu : ContinuousOn u (Icc 0 1)) (hYp : ContinuousOn Yp (Icc 0 1))
    (hsq : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ^ 2 = f.eval (u t)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (h0 : Yp s = 0) (hd : (derivative f).eval (u s) ≠ 0) :
    ∃ W : WeierChart f g, ∃ ε > 0, ∀ t ∈ ball s ε ∩ Icc 0 1,
      Yp t ∈ ball (0 : ℂ) W.r ∧ W.X (Yp t) = u t := by
  have he : f.eval (u s) = 0 := by rw [← hsq s hs, h0]; ring
  obtain ⟨W, hWe⟩ := WeierChart.exists_of_root (g := g) he hd
  obtain ⟨ρ, hρ, hinj⟩ := exists_injOn_ball f hd
  have c1 : ∀ᶠ t in 𝓝[Icc 0 1] s, Yp t ∈ ball (0 : ℂ) W.r :=
    (hYp s hs).preimage_mem_nhdsWithin (h0 ▸ isOpen_ball.mem_nhds (mem_ball_self W.r_pos))
  have hXc : ContinuousWithinAt (fun t => W.X (Yp t)) (Icc 0 1) s :=
    ((W.X_an _ (h0 ▸ mem_ball_self W.r_pos)).continuousAt).comp_continuousWithinAt (hYp s hs)
  have hXs : W.X (Yp s) = u s := by rw [h0, W.X_zero, hWe]
  have c2 : ∀ᶠ t in 𝓝[Icc 0 1] s, W.X (Yp t) ∈ ball (u s) ρ :=
    hXc.preimage_mem_nhdsWithin (by rw [hXs]; exact ball_mem_nhds _ hρ)
  have c3 : ∀ᶠ t in 𝓝[Icc 0 1] s, u t ∈ ball (u s) ρ :=
    (hu s hs).preimage_mem_nhdsWithin (ball_mem_nhds _ hρ)
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhdsWithin_iff.mp (c1.and (c2.and (c3.and self_mem_nhdsWithin)))
  refine ⟨W, ε, hε, fun t ht => ⟨(hball ht).1, ?_⟩⟩
  obtain ⟨hy, hX, hu', htI⟩ := hball ht
  exact hinj hX hu' (by simp only; rw [W.X_sq _ hy, hsq t htI])

/-- **The Abel integral along a path through Weierstrass points exists.** The path `(u, Yp)` is continuous on
`[0, 1]`, lies on `y² = f(x)`, and its zeros of `y` are simple roots of `f`. -/
theorem exists_abelAlongW (hu : ContinuousOn u (Icc 0 1)) (hYp : ContinuousOn Yp (Icc 0 1))
    (hsq : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ^ 2 = f.eval (u t))
    (hsimple : ∀ t ∈ Icc (0 : ℝ) 1, Yp t = 0 → (derivative f).eval (u t) ≠ 0) :
    ∃ A : ℝ → (Fin g → ℂ), A 0 = 0 ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∃ C : PathChart f g, ∃ ε > 0,
      ∀ t ∈ ball s ε ∩ Icc 0 1, C.Carries u Yp t ∧
        ∀ t' ∈ ball s ε ∩ Icc 0 1, A t' - A t = C.F u Yp t' - C.F u Yp t := by
  have hC : ∀ s ∈ Icc (0 : ℝ) 1, ∃ C : PathChart f g, ∃ ε > 0, ∀ t ∈ ball s ε ∩ Icc 0 1,
      C.Carries u Yp t := by
    intro s hs
    by_cases h0 : Yp s = 0
    · obtain ⟨W, ε, hε, hW⟩ := exists_weier_along (g := g) hu hYp hsq hs h0 (hsimple s hs h0)
      exact ⟨.we W, ε, hε, hW⟩
    · obtain ⟨B, ε, hε, hB⟩ := exists_branch_along' (g := g) hu hYp hsq hs h0
      exact ⟨.br B, ε, hε, hB⟩
  choose C ε hε hCε using hC
  classical
  set F : ℝ → ℝ → (Fin g → ℂ) := fun s t => if h : s ∈ Icc (0 : ℝ) 1 then (C s h).F u Yp t else 0
  set ε' : ℝ → ℝ := fun s => if h : s ∈ Icc (0 : ℝ) 1 then ε s h else 1
  have hε's : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), ε' s = ε s hs := fun s hs => by
    simp only [ε', hs, ↓reduceDIte]
  have hFs : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) t, F s t = (C s hs).F u Yp t := fun s hs t => by
    simp only [F, hs, ↓reduceDIte]
  have hε' : ∀ s ∈ Icc (0 : ℝ) 1, 0 < ε' s := fun s hs => by rw [hε's s hs]; exact hε s hs
  have hcompat : ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, ∀ t ∈ ball s (ε' s) ∩ ball s' (ε' s') ∩ Icc 0 1,
      ∀ t' ∈ ball s (ε' s) ∩ ball s' (ε' s') ∩ Icc 0 1, F s t' - F s' t' = F s t - F s' t := by
    intro s hs s' hs' t ht t' ht'
    rw [hε's s hs, hε's s' hs'] at ht ht'
    rw [hFs s hs, hFs s hs, hFs s' hs', hFs s' hs']
    -- `J` is an interval on which both charts carry the path; the difference is locally constant on `J`
    set J := ball s (ε s hs) ∩ ball s' (ε s' hs') ∩ Icc (0 : ℝ) 1 with hJ
    have hJc : IsPreconnected J := (((convex_ball _ _).inter (convex_ball _ _)).inter
      (convex_Icc _ _)).isPreconnected
    have hcar : ∀ τ ∈ J, (C s hs).Carries u Yp τ ∧ (C s' hs').Carries u Yp τ := fun τ hτ =>
      ⟨hCε s hs τ ⟨hτ.1.1, hτ.2⟩, hCε s' hs' τ ⟨hτ.1.2, hτ.2⟩⟩
    have := Subtype.preconnectedSpace hJc
    set D : J → (Fin g → ℂ) := fun x => (C s hs).F u Yp x - (C s' hs').F u Yp x
    have hD : IsLocallyConstant D := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have hev := PathChart.eventually_compat (C s hs) (C s' hs') (hYp x x.2.2)
        (hcar x x.2).1 (hcar x x.2).2
      obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhdsWithin_iff.mp hev
      have hn : {y : J | (y : ℝ) ∈ ball (x : ℝ) δ} ∈ 𝓝 x :=
        (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hδ)
      filter_upwards [hn] with y hy
      exact hδb ⟨hy, y.2.2⟩ (hcar y y.2).1 (hcar y y.2).2
    exact hD.apply_eq_of_isPreconnected isPreconnected_univ (x := ⟨t', ht'⟩) (y := ⟨t, ht⟩)
      (mem_univ _) (mem_univ _)
  obtain ⟨A, hA0, hA⟩ := exists_patch F ε' hε' hcompat
  refine ⟨A, hA0, fun s hs => ⟨C s hs, ε s hs, hε s hs, fun t ht => ⟨hCε s hs t ht, fun t' ht' => ?_⟩⟩⟩
  have := hA s hs t (by rw [hε's s hs]; exact ht) t' (by rw [hε's s hs]; exact ht')
  rwa [hFs s hs, hFs s hs] at this

end Path

end LSG.JacAn
