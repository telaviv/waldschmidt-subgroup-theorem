/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.PathInt

/-!
# The continuation lemma, exp-free part (ABVAR §2.2 a6)

For a continuous path `t ↦ (u(t), Yp(t))`, `t ∈ [0,1]`, on the affine curve `y² = f(x)` with `Yp ≠ 0`, the local Abel
integrals of branch discs along the path patch together into one **Abel integral along the path**
`A : ℝ → ℂ^g`, `A 0 = 0`:

* `exists_patch` (pure topology, any abelian group): local primitives `F s` on intervals `ball s (ε s)`, whose
  pairwise differences are constant on overlaps, patch to a global `A` (Lebesgue number + induction).
* `patch_unique`: such an `A` is unique.
* `LocalBranch.I_sub_eq`: two branches that agree at one point of the (convex) intersection of their discs agree on
  all of it, and their Abel integrals differ by a constant there.
* **`exists_abelAlong`**: the Abel integral along the path exists (local form: near every `s`, `A` is a translate of
  `B.I ∘ u` for a branch `B` through `(u s, Yp s)`).
* **`abelAlong_branch`**: for *any* branch `B` and any `t, t'` with `(u, Yp)` inside `B` on `[t, t']`,
  `A t' − A t = B.I (u t') − B.I (u t)`.
* **`abelAlong_eq_integral`**, **`abelAlong_curveIntegral`**: for a `C¹` path, `A 1 = ∫₀¹ u' ω(u)` and its components
  are Mathlib curve integrals of `x^j dx/y`.

With the global exponential `E` of a4 this is used as: `t ↦ E(z₀ + A t)` and `t ↦ [moving divisor]` agree near
`t = 0` and both satisfy the same local law near each `t` (`abelAlong_branch` + `localExp_spec`), so they agree on
`[0, 1]` (`patch_unique`-style connectedness). Paths through Weierstrass points or `∞` feed `exists_patch` with the
chart primitives of `Charts.lean` instead of branch primitives.
-/

noncomputable section

open Polynomial Metric Set Filter Topology MeasureTheory

namespace LSG.JacAn

/-! ## Abstract patching on `[0, 1]` -/

section Patch

variable {V : Type*} [AddCommGroup V]

/-- The patching property up to `τ`. -/
def PatchUpTo (F : ℝ → ℝ → V) (ε : ℝ → ℝ) (τ : ℝ) (A : ℝ → V) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ ball s (ε s), t ∈ Icc 0 τ → ∀ t' ∈ ball s (ε s), t' ∈ Icc 0 τ →
    A t' - A t = F s t' - F s t

lemma mem_ball_of_between {s e t t' τ : ℝ} (ht : t ∈ ball s e) (ht' : t' ∈ ball s e) (h1 : t ≤ τ)
    (h2 : τ ≤ t') : τ ∈ ball s e := by
  rw [Real.ball_eq_Ioo] at *
  exact ⟨lt_of_lt_of_le ht.1 h1, lt_of_le_of_lt h2 ht'.2⟩

/-- One extension step of the patching induction. -/
lemma patch_step (F : ℝ → ℝ → V) (ε : ℝ → ℝ)
    (hcompat : ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, ∀ t ∈ ball s (ε s) ∩ ball s' (ε s') ∩ Icc 0 1,
      ∀ t' ∈ ball s (ε s) ∩ ball s' (ε s') ∩ Icc 0 1, F s t' - F s' t' = F s t - F s' t)
    {τ τ' : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (hττ' : τ ≤ τ') (hτ'1 : τ' ≤ 1) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) (hsub : Icc τ τ' ⊆ ball s₀ (ε s₀)) {A : ℝ → V}
    (hA : PatchUpTo F ε τ A) :
    PatchUpTo F ε τ' (fun t => if t ≤ τ then A t else A τ + F s₀ t - F s₀ τ) := by
  set A' : ℝ → V := fun t => if t ≤ τ then A t else A τ + F s₀ t - F s₀ τ with hA'
  have hτs₀ : τ ∈ ball s₀ (ε s₀) := hsub ⟨le_rfl, hττ'⟩
  -- the mixed case `t ≤ τ < t'`
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ ball s (ε s), t ∈ Icc 0 τ' → ∀ t' ∈ ball s (ε s), t' ∈ Icc 0 τ' →
      t ≤ τ → τ < t' → A' t' - A' t = F s t' - F s t := by
    intro s hs t hts htI t' hts' htI' h1 h2
    have hτs : τ ∈ ball s (ε s) := mem_ball_of_between hts hts' h1 h2.le
    have hIH := hA s hs t hts ⟨htI.1, h1⟩ τ hτs ⟨hτ.1, le_rfl⟩
    have ht'₀ : t' ∈ ball s₀ (ε s₀) := hsub ⟨h2.le, htI'.2⟩
    have hc := hcompat s₀ hs₀ s hs τ ⟨⟨hτs₀, hτs⟩, hτ⟩ t' ⟨⟨ht'₀, hts'⟩, ⟨htI'.1, htI'.2.trans hτ'1⟩⟩
    simp only [hA', h1, not_le.mpr h2, ↓reduceIte]
    rw [sub_eq_iff_eq_add.mp hIH, sub_eq_iff_eq_add.mp hc]; abel
  intro s hs t hts htI t' hts' htI'
  by_cases h1 : t ≤ τ <;> by_cases h2 : t' ≤ τ
  · simp only [hA', h1, h2, ↓reduceIte]
    exact hA s hs t hts ⟨htI.1, h1⟩ t' hts' ⟨htI'.1, h2⟩
  · exact key s hs t hts htI t' hts' htI' h1 (not_le.mp h2)
  · have := key s hs t' hts' htI' t hts htI h2 (not_le.mp h1)
    rw [← neg_sub, this, neg_sub]
  · have ht₀ : t ∈ ball s₀ (ε s₀) := hsub ⟨(not_le.mp h1).le, htI.2⟩
    have ht'₀ : t' ∈ ball s₀ (ε s₀) := hsub ⟨(not_le.mp h2).le, htI'.2⟩
    have hc := hcompat s₀ hs₀ s hs t ⟨⟨ht₀, hts⟩, ⟨htI.1, htI.2.trans hτ'1⟩⟩
      t' ⟨⟨ht'₀, hts'⟩, ⟨htI'.1, htI'.2.trans hτ'1⟩⟩
    simp only [hA', h1, h2, ↓reduceIte]
    rw [sub_eq_iff_eq_add.mp hc]; abel

/-- **Patching lemma.** Local primitives `F s` on `ball s (ε s)` (`s ∈ [0,1]`) whose differences are constant on
overlaps patch to a global `A` with `A 0 = 0`. -/
theorem exists_patch (F : ℝ → ℝ → V) (ε : ℝ → ℝ) (hε : ∀ s ∈ Icc (0 : ℝ) 1, 0 < ε s)
    (hcompat : ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, ∀ t ∈ ball s (ε s) ∩ ball s' (ε s') ∩ Icc 0 1,
      ∀ t' ∈ ball s (ε s) ∩ ball s' (ε s') ∩ Icc 0 1, F s t' - F s' t' = F s t - F s' t) :
    ∃ A : ℝ → V, A 0 = 0 ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ ball s (ε s) ∩ Icc 0 1,
      ∀ t' ∈ ball s (ε s) ∩ Icc 0 1, A t' - A t = F s t' - F s t := by
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (s := Icc (0 : ℝ) 1)
    (c := fun s : Icc (0 : ℝ) 1 => ball (s : ℝ) (ε s)) isCompact_Icc (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hε x hx)⟩)
  set τ : ℕ → ℝ := fun n => min 1 (n * (δ / 2)) with hτdef
  have hτI : ∀ n, τ n ∈ Icc (0 : ℝ) 1 := fun n =>
    ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
  have hmono : ∀ n, τ n ≤ τ (n + 1) := fun n =>
    min_le_min le_rfl (by push_cast; nlinarith)
  have hgap : ∀ n, τ (n + 1) - τ n ≤ δ / 2 := by
    intro n
    simp only [hτdef]; push_cast
    rcases le_total 1 (n * (δ / 2)) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]; linarith
    · rw [min_eq_right h]
      have := min_le_right 1 (((n : ℝ) + 1) * (δ / 2)); nlinarith
  have hP : ∀ n, ∃ A : ℝ → V, A 0 = 0 ∧ PatchUpTo F ε (τ n) A := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, rfl, fun s _ t _ ht t' _ ht' => ?_⟩
      have h0 : τ 0 = 0 := by simp [hτdef]
      rw [h0] at ht ht'
      have : t = 0 := le_antisymm ht.2 ht.1
      have : t' = 0 := le_antisymm ht'.2 ht'.1
      subst t t'; simp
    | succ n ih =>
      obtain ⟨A, hA0, hA⟩ := ih
      obtain ⟨⟨s₀, hs₀⟩, hball⟩ := hleb (τ n) (hτI n)
      have hsub : Icc (τ n) (τ (n + 1)) ⊆ ball s₀ (ε s₀) := by
        intro t ht
        apply hball
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2, hgap n]
      refine ⟨_, ?_, patch_step F ε hcompat (hτI n) (hmono n) (hτI (n + 1)).2 hs₀ hsub hA⟩
      simp [(hτI n).1, hA0]
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  have hτN : τ N = 1 := by
    apply min_eq_left
    have : 2 / δ * (δ / 2) = 1 := by field_simp
    nlinarith
  obtain ⟨A, hA0, hA⟩ := hP N
  rw [hτN] at hA
  exact ⟨A, hA0, fun s hs t ht t' ht' => hA s hs t ht.1 ht.2 t' ht'.1 ht'.2⟩

/-- **Uniqueness of the patching.** -/
theorem patch_unique {F : ℝ → ℝ → V} {ε : ℝ → ℝ} (hε : ∀ s ∈ Icc (0 : ℝ) 1, 0 < ε s) {A A' : ℝ → V}
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ ball s (ε s) ∩ Icc 0 1, ∀ t' ∈ ball s (ε s) ∩ Icc 0 1,
      A t' - A t = F s t' - F s t)
    (hA' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ ball s (ε s) ∩ Icc 0 1, ∀ t' ∈ ball s (ε s) ∩ Icc 0 1,
      A' t' - A' t = F s t' - F s t)
    (h0 : A 0 = A' 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : A t = A' t := by
  have := Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
  set D : Icc (0 : ℝ) 1 → V := fun x => A x - A' x
  have hD : IsLocallyConstant D := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hn : {y : Icc (0 : ℝ) 1 | (y : ℝ) ∈ ball (x : ℝ) (ε x)} ∈ 𝓝 x :=
      (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self (hε x x.2))
    filter_upwards [hn] with y hy
    have h1 := hA x x.2 x ⟨mem_ball_self (hε x x.2), x.2⟩ y ⟨hy, y.2⟩
    have h2 := hA' x x.2 x ⟨mem_ball_self (hε x x.2), x.2⟩ y ⟨hy, y.2⟩
    simp only [D]
    rw [sub_eq_iff_eq_add.mp h1, sub_eq_iff_eq_add.mp h2]; abel
  have := hD.apply_eq_of_isPreconnected isPreconnected_univ (x := ⟨t, ht⟩) (y := ⟨0, by simp⟩)
    (mem_univ _) (mem_univ _)
  simp only [D, h0, sub_self] at this
  exact sub_eq_zero.mp this

end Patch

/-! ## Branch compatibility -/

variable {f : ℂ[X]} {g : ℕ}

/-- Two branches agreeing at one point of the intersection of their discs agree on all of it. -/
theorem LocalBranch.Y_eqOn (B B' : LocalBranch f g) {x₁ : ℂ}
    (h₁ : x₁ ∈ ball B.x₀ B.r ∩ ball B'.x₀ B'.r) (hY : B.Y x₁ = B'.Y x₁) :
    EqOn B.Y B'.Y (ball B.x₀ B.r ∩ ball B'.x₀ B'.r) := by
  have hU : IsPreconnected (ball B.x₀ B.r ∩ ball B'.x₀ B'.r) :=
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  refine hU.eq_of_sq_eq (fun x hx => (B.Y_an x hx.1).continuousAt.continuousWithinAt)
    (fun x hx => (B'.Y_an x hx.2).continuousAt.continuousWithinAt) (fun x hx => ?_)
    (fun hx => B'.Y_ne _ hx.2) h₁ hY
  simp only [Pi.pow_apply, B.Y_sq x hx.1, B'.Y_sq x hx.2]

/-- **Branch compatibility**: on the intersection of the discs, the Abel integrals of two branches that agree at one
point differ by a constant. -/
theorem LocalBranch.I_sub_eq (B B' : LocalBranch f g) {x₁ x : ℂ}
    (h₁ : x₁ ∈ ball B.x₀ B.r ∩ ball B'.x₀ B'.r) (hY : B.Y x₁ = B'.Y x₁)
    (hx : x ∈ ball B.x₀ B.r ∩ ball B'.x₀ B'.r) : B.I x - B'.I x = B.I x₁ - B'.I x₁ := by
  have hU := (isOpen_ball (x := B.x₀) (ε := B.r)).inter (isOpen_ball (x := B'.x₀) (ε := B'.r))
  have hUc : IsPreconnected (ball B.x₀ B.r ∩ ball B'.x₀ B'.r) :=
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hEq := B.Y_eqOn B' h₁ hY
  have hd : ∀ y ∈ ball B.x₀ B.r ∩ ball B'.x₀ B'.r, HasDerivAt (fun y => B.I y - B'.I y) 0 y := by
    intro y hy
    have := (B.I_deriv y hy.1).sub (B'.I_deriv y hy.2)
    have h0 : omegaVec g B.Y y - omegaVec g B'.Y y = 0 := by
      funext k; simp [omegaVec, hEq hy]
    rwa [h0] at this
  exact hU.is_const_of_deriv_eq_zero hUc (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hx h₁

/-! ## The Abel integral along a path -/

section Path

variable {u Yp : ℝ → ℂ}

/-- Near every parameter, a branch through the path point carries the path. -/
lemma exists_branch_along (hu : ContinuousOn u (Icc 0 1)) (hYp : ContinuousOn Yp (Icc 0 1))
    (hsq : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ^ 2 = f.eval (u t)) (hne : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ≠ 0)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ B : LocalBranch f g, ∃ ε > 0, ∀ t ∈ ball s ε ∩ Icc 0 1,
      u t ∈ ball B.x₀ B.r ∧ B.Y (u t) = Yp t := by
  obtain ⟨B, hBx, hBy⟩ := LocalBranch.exists_of_mem (g := g) (hsq s hs) (hne s hs)
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
    intro h; apply hne s hs; linear_combination h / 2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp (h1.and (h2.and self_mem_nhdsWithin))
  refine ⟨B, ε, hε, fun t ht => ⟨(hball ht).1, ?_⟩⟩
  obtain ⟨hb, hs', htI⟩ := hball ht
  have hsq' : B.Y (u t) ^ 2 = Yp t ^ 2 := by rw [B.Y_sq _ hb, hsq t htI]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with h | h
  · exact h
  · exact absurd (by rw [h]; ring) hs'

/-- **The Abel integral along a path exists**: a function `A` with `A 0 = 0` which near every parameter is a
translate of `B.I ∘ u` for a branch `B` carrying the path. -/
theorem exists_abelAlong (hu : ContinuousOn u (Icc 0 1)) (hYp : ContinuousOn Yp (Icc 0 1))
    (hsq : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ^ 2 = f.eval (u t)) (hne : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ≠ 0) :
    ∃ A : ℝ → (Fin g → ℂ), A 0 = 0 ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∃ B : LocalBranch f g, ∃ ε > 0,
      ∀ t ∈ ball s ε ∩ Icc 0 1, u t ∈ ball B.x₀ B.r ∧ B.Y (u t) = Yp t ∧
        ∀ t' ∈ ball s ε ∩ Icc 0 1, A t' - A t = B.I (u t') - B.I (u t) := by
  have hB : ∀ s ∈ Icc (0 : ℝ) 1, ∃ B : LocalBranch f g, ∃ ε > 0, ∀ t ∈ ball s ε ∩ Icc 0 1,
      u t ∈ ball B.x₀ B.r ∧ B.Y (u t) = Yp t := fun s hs => exists_branch_along hu hYp hsq hne hs
  choose B ε hε hBε using hB
  classical
  set F : ℝ → ℝ → (Fin g → ℂ) := fun s t => if h : s ∈ Icc (0 : ℝ) 1 then (B s h).I (u t) else 0
  set ε' : ℝ → ℝ := fun s => if h : s ∈ Icc (0 : ℝ) 1 then ε s h else 1
  have hε's : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), ε' s = ε s hs := fun s hs => by simp only [ε', hs, ↓reduceDIte]
  have hFs : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) t, F s t = (B s hs).I (u t) := fun s hs t => by
    simp only [F, hs, ↓reduceDIte]
  have hε' : ∀ s ∈ Icc (0 : ℝ) 1, 0 < ε' s := fun s hs => by rw [hε's s hs]; exact hε s hs
  have hcompat : ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, ∀ t ∈ ball s (ε' s) ∩ ball s' (ε' s') ∩ Icc 0 1,
      ∀ t' ∈ ball s (ε' s) ∩ ball s' (ε' s') ∩ Icc 0 1, F s t' - F s' t' = F s t - F s' t := by
    intro s hs s' hs' t ht t' ht'
    rw [hε's s hs, hε's s' hs'] at ht ht'
    rw [hFs s hs, hFs s hs, hFs s' hs', hFs s' hs']
    have a1 := hBε s hs t ⟨ht.1.1, ht.2⟩
    have a2 := hBε s' hs' t ⟨ht.1.2, ht.2⟩
    have b1 := hBε s hs t' ⟨ht'.1.1, ht'.2⟩
    have b2 := hBε s' hs' t' ⟨ht'.1.2, ht'.2⟩
    exact (B s hs).I_sub_eq (B s' hs') ⟨a1.1, a2.1⟩ (a1.2.trans a2.2.symm) ⟨b1.1, b2.1⟩
  obtain ⟨A, hA0, hA⟩ := exists_patch F ε' hε' hcompat
  refine ⟨A, hA0, fun s hs => ⟨B s hs, ε s hs, hε s hs, fun t ht => ⟨(hBε s hs t ht).1,
    (hBε s hs t ht).2, fun t' ht' => ?_⟩⟩⟩
  have := hA s hs t (by rw [hε's s hs]; exact ht) t' (by rw [hε's s hs]; exact ht')
  rwa [hFs s hs, hFs s hs] at this

/-- The local property of an Abel integral along the path. -/
def IsAbelAlong (f : ℂ[X]) (g : ℕ) (u Yp : ℝ → ℂ) (A : ℝ → (Fin g → ℂ)) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∃ B : LocalBranch f g, ∃ ε > 0,
    ∀ t ∈ ball s ε ∩ Icc 0 1, u t ∈ ball B.x₀ B.r ∧ B.Y (u t) = Yp t ∧
      ∀ t' ∈ ball s ε ∩ Icc 0 1, A t' - A t = B.I (u t') - B.I (u t)

/-- **Any branch computes increments of the Abel integral**: if `(u, Yp)` stays in the disc of `B` with
`B.Y ∘ u = Yp` on `[t, t']`, then `A t' − A t = B.I (u t') − B.I (u t)`. -/
theorem abelAlong_branch {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlong f g u Yp A) (B : LocalBranch f g)
    {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (hB : ∀ τ ∈ uIcc t t', u τ ∈ ball B.x₀ B.r ∧ B.Y (u τ) = Yp τ) :
    A t' - A t = B.I (u t') - B.I (u t) := by
  have hsub : uIcc t t' ⊆ Icc (0 : ℝ) 1 := (ordConnected_Icc).uIcc_subset ht ht'
  have := Subtype.preconnectedSpace (isPreconnected_uIcc (a := t) (b := t'))
  set D : uIcc t t' → (Fin g → ℂ) := fun x => A x - B.I (u x)
  have hD : IsLocallyConstant D := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨B', ε, hε, hB'⟩ := hA x (hsub x.2)
    have hn : {y : uIcc t t' | (y : ℝ) ∈ ball (x : ℝ) ε} ∈ 𝓝 x :=
      (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hε)
    filter_upwards [hn] with y hy
    have hx' := hB' x ⟨mem_ball_self hε, hsub x.2⟩
    have hy' := hB' y ⟨hy, hsub y.2⟩
    have hinc := hx'.2.2 y ⟨hy, hsub y.2⟩
    have hc := B'.I_sub_eq B ⟨hx'.1, (hB x x.2).1⟩ (hx'.2.1.trans (hB x x.2).2.symm)
      ⟨hy'.1, (hB y y.2).1⟩
    simp only [D]
    rw [sub_eq_iff_eq_add.mp hinc, sub_eq_iff_eq_add.mp hc]; abel
  have := hD.apply_eq_of_isPreconnected isPreconnected_univ (x := ⟨t', right_mem_uIcc⟩)
    (y := ⟨t, left_mem_uIcc⟩) (mem_univ _) (mem_univ _)
  simp only [D] at this
  rw [sub_eq_iff_eq_add.mp this]; abel

/-- **Uniqueness** of the Abel integral along a path. -/
theorem abelAlong_unique {A A' : ℝ → (Fin g → ℂ)} (hA : IsAbelAlong f g u Yp A)
    (hA' : IsAbelAlong f g u Yp A') (h0 : A 0 = A' 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : A t = A' t := by
  have hsub : uIcc 0 t ⊆ Icc (0 : ℝ) 1 := (ordConnected_Icc).uIcc_subset ⟨le_rfl, zero_le_one⟩ ht
  have := Subtype.preconnectedSpace (isPreconnected_uIcc (a := (0 : ℝ)) (b := t))
  set D : uIcc (0 : ℝ) t → (Fin g → ℂ) := fun x => A x - A' x
  have hD : IsLocallyConstant D := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨B, ε, hε, hB⟩ := hA x (hsub x.2)
    obtain ⟨B', ε', hε', hB'⟩ := hA' x (hsub x.2)
    have hn : {y : uIcc (0 : ℝ) t | (y : ℝ) ∈ ball (x : ℝ) (min ε ε')} ∈ 𝓝 x :=
      (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self (lt_min hε hε'))
    filter_upwards [hn] with y hy
    have hy1 : (y : ℝ) ∈ ball (x : ℝ) ε := ball_subset_ball (min_le_left _ _) hy
    have hy2 : (y : ℝ) ∈ ball (x : ℝ) ε' := ball_subset_ball (min_le_right _ _) hy
    have hx1 := hB x ⟨mem_ball_self hε, hsub x.2⟩
    have hx2 := hB' x ⟨mem_ball_self hε', hsub x.2⟩
    have hyB := hB y ⟨hy1, hsub y.2⟩
    have hyB' := hB' y ⟨hy2, hsub y.2⟩
    have i1 := hx1.2.2 y ⟨hy1, hsub y.2⟩
    have i2 := hx2.2.2 y ⟨hy2, hsub y.2⟩
    have hc := B.I_sub_eq B' ⟨hx1.1, hx2.1⟩ (hx1.2.1.trans hx2.2.1.symm) ⟨hyB.1, hyB'.1⟩
    simp only [D]
    rw [sub_eq_iff_eq_add.mp i1, sub_eq_iff_eq_add.mp i2, sub_eq_iff_eq_add.mp hc]; abel
  have := hD.apply_eq_of_isPreconnected isPreconnected_univ (x := ⟨t, right_mem_uIcc⟩)
    (y := ⟨0, left_mem_uIcc⟩) (mem_univ _) (mem_univ _)
  simp only [D, h0, sub_self] at this
  exact sub_eq_zero.mp this

/-- `exists_abelAlong` in terms of `IsAbelAlong`. -/
theorem exists_isAbelAlong (hu : ContinuousOn u (Icc 0 1)) (hYp : ContinuousOn Yp (Icc 0 1))
    (hsq : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ^ 2 = f.eval (u t)) (hne : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ≠ 0) :
    ∃ A : ℝ → (Fin g → ℂ), A 0 = 0 ∧ IsAbelAlong f g u Yp A :=
  exists_abelAlong hu hYp hsq hne

/-! ## `C¹` paths: the Abel integral is the integral of `ω` -/

/-- For a `C¹` path the Abel integral is `∫₀^t u' ω(u)`: derivative form. -/
theorem IsAbelAlong.hasDerivAt {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlong f g u Yp A) {u' : ℝ → ℂ}
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hu : HasDerivAt u (u' t) t) :
    HasDerivAt A (u' t • fun k : Fin g => u t ^ (k : ℕ) / Yp t) t := by
  obtain ⟨B, ε, hε, hB⟩ := hA t (Ioo_subset_Icc_self ht)
  have ht' := hB t ⟨mem_ball_self hε, Ioo_subset_Icc_self ht⟩
  have hD := (B.I_deriv _ ht'.1).scomp t hu
  have hev : (fun τ => A t + (B.I (u τ) - B.I (u t))) =ᶠ[𝓝 t] A := by
    filter_upwards [inter_mem (ball_mem_nhds t hε) (Icc_mem_nhds ht.1 ht.2)] with τ hτ
    have := ht'.2.2 τ hτ
    rw [← this]; abel
  have h2 := ((hD.sub_const (B.I (u t))).const_add (A t)).congr_of_eventuallyEq hev.symm
  refine h2.congr_deriv ?_
  funext k
  simp [omegaVec, ht'.2.1]

/-- Continuity of the Abel integral along a continuous path. -/
theorem IsAbelAlong.continuousOn {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlong f g u Yp A)
    (hu : ContinuousOn u (Icc 0 1)) : ContinuousOn A (Icc 0 1) := by
  intro s hs
  obtain ⟨B, ε, hε, hB⟩ := hA s hs
  have hs' := hB s ⟨mem_ball_self hε, hs⟩
  have hc : ContinuousWithinAt (fun τ => A s + (B.I (u τ) - B.I (u s))) (Icc 0 1) s :=
    continuousWithinAt_const.add
      ((((B.I_an _ hs'.1).continuousAt).comp_continuousWithinAt (hu s hs)).sub
        continuousWithinAt_const)
  refine hc.congr_of_eventuallyEq ?_ (by simp)
  filter_upwards [inter_mem_nhdsWithin (Icc 0 1) (ball_mem_nhds s hε), self_mem_nhdsWithin]
    with τ hτ hτI
  have := hs'.2.2 τ ⟨hτ.2, hτI⟩
  rw [← this]; abel

/-- **`A 1 = ∫₀¹ u' ω(u)`** for a `C¹` path off the Weierstrass points. -/
theorem IsAbelAlong.eq_integral {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlong f g u Yp A) (hA0 : A 0 = 0)
    {u' : ℝ → ℂ} (hu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt u (u' t) t) (hu' : ContinuousOn u' (Icc 0 1))
    (hYp : ContinuousOn Yp (Icc 0 1)) (hne : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ≠ 0) :
    A 1 = ∫ t in (0 : ℝ)..1, u' t • fun k : Fin g => u t ^ (k : ℕ) / Yp t := by
  have hcu : ContinuousOn u (Icc 0 1) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one (hA.continuousOn hcu)
    (fun t ht => hA.hasDerivAt ht (hu t (Ioo_subset_Icc_self ht))), hA0, sub_zero]
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  refine hu'.smul (continuousOn_pi.mpr fun k => ?_)
  exact (hcu.pow _).div hYp hne

/-- **Components are Mathlib curve integrals**: if `γ.extend = (u, Yp)` on `[0, 1]`, then
`(A 1) j = ∫ᶜ p in γ, x^j dx/y`. -/
theorem IsAbelAlong.curveIntegral {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlong f g u Yp A) (hA0 : A 0 = 0)
    {u' : ℝ → ℂ} (hu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt u (u' t) t) (hu' : ContinuousOn u' (Icc 0 1))
    {Yp' : ℝ → ℂ} (hY : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Yp (Yp' t) t)
    (hYp : ContinuousOn Yp (Icc 0 1)) (hne : ∀ t ∈ Icc (0 : ℝ) 1, Yp t ≠ 0)
    {P Q : ℂ × ℂ} (γ : Path P Q) (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t = (u t, Yp t)) (j : Fin g) :
    ∫ᶜ p in γ, Beta.omegaJ j p = A 1 j := by
  have hcu : ContinuousOn u (Icc 0 1) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun t => u' t • fun k : Fin g => u t ^ (k : ℕ) / Yp t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hu'.smul (continuousOn_pi.mpr fun k => (hcu.pow _).div hYp hne)
  have hc := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) j).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.proj_apply] at hc
  rw [hA.eq_integral hA0 hu hu' hYp hne, ← hc, curveIntegral_def]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(countable_singleton (1 : ℝ)).ae_notMem volume] with t ht1 hmem
  rw [uIoc_of_le zero_le_one] at hmem
  have h0 : 0 < t := hmem.1
  have h1 : t < 1 := lt_of_le_of_ne hmem.2 ht1
  have hev : γ.extend =ᶠ[𝓝 t] fun s => (u s, Yp s) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with s hs using hγ s (Ioo_subset_Icc_self hs)
  have hd : derivWithin γ.extend unitInterval t = (u' t, Yp' t) := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds h0 h1), hev.deriv_eq,
      ((hu t ⟨h0.le, h1.le⟩).prodMk (hY t ⟨h0, h1⟩)).deriv]
  rw [curveIntegralFun_def, hd, hev.eq_of_nhds]
  simp [Beta.omegaJ]; ring

end Path

end LSG.JacAn
