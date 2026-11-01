/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Branch

/-!
# Charts at the Weierstrass points and at `∞` (ABVAR §2.2 a3′; genus-generic)

`LocalBranch` uses `x` as coordinate, which fails where `y = 0` (Weierstrass points) and at `∞`. Here:

* `WeierChart f g`: at a simple root `e` of `f`, the coordinate is `y`; `x = X(y)` with `f(X(y)) = y²`, `X(0) = e`,
  and the differentials pull back to `ω_k = 2X^k/f'(X) dy` (`weierVec`), holomorphic; `I` is a primitive.
  `WeierChart.exists_of_root` builds one (`f(e) = 0`, `f'(e) ≠ 0`), via the analytic inverse of `x ↦ f(x)`.
* `InfChart f g`: for `deg f ≤ 2g + 1`, the coordinate is `τ` with `x = τ⁻²`, `y = τ^{−(2g+1)} H(τ)`,
  `H² = F` with `F(τ) = τ^{4g+2} f(τ⁻²)` the polynomial `revPoly f g` (`revPoly_eval`); `ω_k = −2τ^{2(g−1−k)}/H dτ`
  (`infVec`), holomorphic at `τ = 0` for `k < g`. `InfChart.exists_of_lc` builds one when `lc = f_{2g+1} ≠ 0`.
* Compatibility with `x`-branches on overlaps (the pull-back identities): `WeierChart.hasDerivAt_branch`,
  `InfChart.hasDerivAt_branch`: `d/dy B.I(X y) = weierVec`, `d/dτ B.I(τ⁻²) = infVec` wherever the branch value
  matches.
-/

noncomputable section

open Polynomial Metric Filter Topology

namespace LSG.JacAn

variable {f : ℂ[X]} {g : ℕ}

/-! ## Weierstrass points -/

/-- The pulled-back differentials at a Weierstrass point: `ω_k = 2 X(y)^k / f'(X(y)) dy`. -/
def weierVec (g : ℕ) (f : ℂ[X]) (X : ℂ → ℂ) (y : ℂ) : Fin g → ℂ :=
  fun k => 2 * X y ^ (k : ℕ) / (derivative f).eval (X y)

/-- A chart of `y² = f(x)` at a Weierstrass point `(e, 0)`, with coordinate `y`. -/
structure WeierChart (f : ℂ[X]) (g : ℕ) where
  /-- the root `e` of `f` -/
  e : ℂ
  /-- radius of the `y`-disc -/
  r : ℝ
  r_pos : 0 < r
  /-- `x` as a function of `y` -/
  X : ℂ → ℂ
  X_zero : X 0 = e
  X_an : AnalyticOnNhd ℂ X (ball 0 r)
  X_sq : ∀ y ∈ ball (0 : ℂ) r, f.eval (X y) = y ^ 2
  fd_ne : ∀ y ∈ ball (0 : ℂ) r, (derivative f).eval (X y) ≠ 0
  /-- the Abel integrals in the chart -/
  I : ℂ → (Fin g → ℂ)
  I_zero : I 0 = 0
  I_deriv : ∀ y ∈ ball (0 : ℂ) r, HasDerivAt I (weierVec g f X y) y
  I_an : AnalyticOnNhd ℂ I (ball 0 r)

namespace WeierChart

/-- **Existence of Weierstrass charts** at every simple root of `f`. -/
theorem exists_of_root {e : ℂ} (he : f.eval e = 0) (hd : (derivative f).eval e ≠ 0) :
    ∃ W : WeierChart f g, W.e = e := by
  have hs := (f.hasStrictDerivAt e).hasStrictFDerivAt_equiv hd
  set ψ := hs.localInverse _ _ _ with hψ
  have hψan : AnalyticAt ℂ ψ (f.eval e) :=
    analyticAt_localInverse (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) f e (Set.mem_univ _)) hs
  rw [he] at hψan
  have hψe : ψ 0 = e := by
    have := HasStrictFDerivAt.localInverse_apply_image hs; rwa [he] at this
  have hright := HasStrictFDerivAt.eventually_right_inverse hs
  rw [he] at hright
  -- `X y = ψ (y²)`
  have hsq : ContinuousAt (fun y : ℂ => y ^ 2) 0 := (continuous_pow 2).continuousAt
  have ht : Tendsto (fun y : ℂ => y ^ 2) (𝓝 0) (𝓝 0) := by simpa using hsq.tendsto
  have hev1 : ∀ᶠ y in 𝓝 (0 : ℂ), AnalyticAt ℂ ψ (y ^ 2) := ht.eventually hψan.eventually_analyticAt
  have hev2 : ∀ᶠ y in 𝓝 (0 : ℂ), f.eval (ψ (y ^ 2)) = y ^ 2 := ht.eventually hright
  have hXc : ContinuousAt (fun y : ℂ => ψ (y ^ 2)) 0 :=
    hψan.continuousAt.comp_of_eq hsq (by simp)
  have hev3 : ∀ᶠ y in 𝓝 (0 : ℂ), (derivative f).eval (ψ (y ^ 2)) ≠ 0 := by
    have hc : ContinuousAt (fun y : ℂ => (derivative f).eval (ψ (y ^ 2))) 0 :=
      (Polynomial.continuous _).continuousAt.comp hXc
    refine hc.eventually_ne ?_
    simpa [hψe] using hd
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff_ball.mp ((hev1.and hev2).and hev3)
  have hXan : AnalyticOnNhd ℂ (fun y : ℂ => ψ (y ^ 2)) (ball 0 r) := fun y hy => by
    have hp2 : AnalyticAt ℂ (fun y : ℂ => y ^ 2) y := analyticAt_id.pow 2
    exact AnalyticAt.comp (f := fun y : ℂ => y ^ 2) (hall y hy).1.1 hp2
  have hw : DifferentiableOn ℂ (weierVec g f fun y => ψ (y ^ 2)) (ball 0 r) := by
    intro y hy
    refine DifferentiableAt.differentiableWithinAt ?_
    rw [differentiableAt_pi]
    intro k
    refine (((hXan y hy).differentiableAt.pow _).const_mul 2).div ?_ (hall y hy).2
    exact (Polynomial.differentiable _).differentiableAt.comp y (hXan y hy).differentiableAt
  obtain ⟨I, hI0, hId, hIan⟩ := exists_primitive_ball hw
  exact ⟨⟨e, r, hr, fun y => ψ (y ^ 2), by simpa using hψe, hXan, fun y hy => (hall y hy).1.2,
    fun y hy => (hall y hy).2, I, hI0, hId, hIan⟩, rfl⟩

/-- `X'(y) = 2y / f'(X(y))`. -/
lemma hasDerivAt_X (W : WeierChart f g) {y : ℂ} (hy : y ∈ ball (0 : ℂ) W.r) :
    HasDerivAt W.X (2 * y / (derivative f).eval (W.X y)) y := by
  have hd := (W.X_an y hy).differentiableAt.hasDerivAt
  have h1 := (f.hasDerivAt (W.X y)).comp y hd
  have h2 : HasDerivAt (fun y => f.eval (W.X y)) (2 * y) y := by
    have := (hasDerivAt_pow 2 y)
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv (by push_cast; ring)
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz using W.X_sq z hz
  have h := h1.unique h2
  have hne := W.fd_ne y hy
  convert hd using 1
  rw [← h]; field_simp

/-- **Compatibility with `x`-branches**: where `X y` lies in the disc of `B` and `B.Y (X y) = y`,
`d/dy B.I (X y) = weierVec`. Hence `W.I − B.I ∘ X` has zero derivative there. -/
theorem hasDerivAt_branch (W : WeierChart f g) (B : LocalBranch f g) {y : ℂ}
    (hy : y ∈ ball (0 : ℂ) W.r) (hB : W.X y ∈ ball B.x₀ B.r) (hY : B.Y (W.X y) = y) :
    HasDerivAt (fun y => B.I (W.X y)) (weierVec g f W.X y) y := by
  have h := (B.I_deriv _ hB).scomp y (W.hasDerivAt_X hy)
  refine h.congr_deriv ?_
  have hy0 : y ≠ 0 := hY ▸ B.Y_ne _ hB
  have hne := W.fd_ne y hy
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, omegaVec, weierVec, hY]
  field_simp

end WeierChart

/-! ## The point at infinity -/

/-- `F(τ) = τ^{4g+2} f(τ⁻²)` as a polynomial (for `deg f ≤ 2g + 1`). -/
def revPoly (f : ℂ[X]) (g : ℕ) : ℂ[X] :=
  ∑ i ∈ Finset.range (2 * g + 2), C (f.coeff i) * X ^ (4 * g + 2 - 2 * i)

lemma revPoly_eval (hdeg : f.natDegree ≤ 2 * g + 1) {τ : ℂ} (hτ : τ ≠ 0) :
    (revPoly f g).eval τ = τ ^ (4 * g + 2) * f.eval ((τ⁻¹) ^ 2) := by
  rw [eval_eq_sum_range' (p := f) (n := 2 * g + 2) (by omega) ((τ⁻¹) ^ 2), Finset.mul_sum, revPoly,
    eval_finsetSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : 2 * i ≤ 4 * g + 2 := by have := Finset.mem_range.mp hi; omega
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  have : τ ^ (4 * g + 2) = τ ^ (4 * g + 2 - 2 * i) * τ ^ (2 * i) := by
    rw [← pow_add]; congr 1; omega
  rw [this, ← pow_mul, inv_pow, mul_comm 2 i]
  field_simp

lemma revPoly_eval_zero : (revPoly f g).eval 0 = f.coeff (2 * g + 1) := by
  rw [revPoly, eval_finsetSum, Finset.sum_eq_single (2 * g + 1)]
  · simp [show 4 * g + 2 - 2 * (2 * g + 1) = 0 by omega]
  · intro i hi hne
    have : 4 * g + 2 - 2 * i ≠ 0 := by have := Finset.mem_range.mp hi; omega
    simp [zero_pow this]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The pulled-back differentials at `∞`: `ω_k = −2 τ^{2(g−1−k)} / H(τ) dτ`. -/
def infVec (g : ℕ) (H : ℂ → ℂ) (τ : ℂ) : Fin g → ℂ :=
  fun k => -2 * τ ^ (2 * (g - 1 - (k : ℕ))) / H τ

/-- A chart of `y² = f(x)` at `∞`, coordinate `τ` with `x = τ⁻²`, `y = τ^{−(2g+1)} H(τ)`. -/
structure InfChart (f : ℂ[X]) (g : ℕ) where
  /-- radius of the `τ`-disc -/
  r : ℝ
  r_pos : 0 < r
  /-- `H = √F` -/
  H : ℂ → ℂ
  H_sq : ∀ τ ∈ ball (0 : ℂ) r, H τ ^ 2 = (revPoly f g).eval τ
  H_ne : ∀ τ ∈ ball (0 : ℂ) r, H τ ≠ 0
  H_an : AnalyticOnNhd ℂ H (ball 0 r)
  /-- the Abel integrals in the chart -/
  I : ℂ → (Fin g → ℂ)
  I_zero : I 0 = 0
  I_deriv : ∀ τ ∈ ball (0 : ℂ) r, HasDerivAt I (infVec g H τ) τ
  I_an : AnalyticOnNhd ℂ I (ball 0 r)

namespace InfChart

/-- **Existence of a chart at `∞`** when the coefficient `f_{2g+1}` is nonzero. -/
theorem exists_of_lc (hlc : f.coeff (2 * g + 1) ≠ 0) : Nonempty (InfChart f g) := by
  set a := f.coeff (2 * g + 1)
  set y₀ := a ^ ((2 : ℂ)⁻¹) with hy₀
  have hy : y₀ ^ 2 = (revPoly f g).eval 0 := by
    rw [revPoly_eval_zero, hy₀]
    have := Complex.cpow_nat_inv_pow a (n := 2) two_ne_zero
    push_cast at this; exact this
  have hy0 : y₀ ≠ 0 := by
    intro h; rw [h, revPoly_eval_zero] at hy; exact hlc (by simpa using hy.symm)
  obtain ⟨H, hHan, hH0, hHsq⟩ := exists_sqrt_branch (F := fun τ => (revPoly f g).eval τ)
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) _ 0 (Set.mem_univ _)) hy hy0
  obtain ⟨r₁, hr₁, hH₁⟩ := hHan.exists_ball_analyticOnNhd
  have hne : ∀ᶠ τ in 𝓝 (0 : ℂ), H τ ≠ 0 := hHan.continuousAt.eventually_ne (hH0 ▸ hy0)
  obtain ⟨r₂, hr₂, hH₂⟩ := Metric.eventually_nhds_iff_ball.mp hne
  have hb₁ : ball (0 : ℂ) (min r₁ r₂) ⊆ ball 0 r₁ := ball_subset_ball (min_le_left _ _)
  have hb₂ : ball (0 : ℂ) (min r₁ r₂) ⊆ ball 0 r₂ := ball_subset_ball (min_le_right _ _)
  have hw : DifferentiableOn ℂ (infVec g H) (ball 0 (min r₁ r₂)) := by
    intro τ hτ
    refine DifferentiableAt.differentiableWithinAt ?_
    rw [differentiableAt_pi]
    intro k
    exact (((differentiableAt_id.pow _).const_mul (-2)).div (hH₁ τ (hb₁ hτ)).differentiableAt
      (hH₂ τ (hb₂ hτ)))
  obtain ⟨I, hI0, hId, hIan⟩ := exists_primitive_ball hw
  exact ⟨⟨min r₁ r₂, lt_min hr₁ hr₂, H, fun τ _ => hHsq τ, fun τ hτ => hH₂ τ (hb₂ hτ),
    hH₁.mono hb₁, I, hI0, hId, hIan⟩⟩

/-- The affine points of the chart lie on the curve: `(τ^{−(2g+1)} H)² = f(τ⁻²)` for `τ ≠ 0`. -/
theorem mem_curve (C : InfChart f g) (hdeg : f.natDegree ≤ 2 * g + 1) {τ : ℂ}
    (hτ : τ ∈ ball (0 : ℂ) C.r) (hτ0 : τ ≠ 0) :
    ((τ⁻¹) ^ (2 * g + 1) * C.H τ) ^ 2 = f.eval ((τ⁻¹) ^ 2) := by
  rw [mul_pow, C.H_sq τ hτ, revPoly_eval hdeg hτ0, ← mul_assoc, ← pow_mul,
    show (2 * g + 1) * 2 = 4 * g + 2 by ring, ← mul_pow, inv_mul_cancel₀ hτ0, one_pow, one_mul]

/-- **Compatibility with `x`-branches**: where `τ⁻²` lies in the disc of `B` and
`B.Y (τ⁻²) = τ^{−(2g+1)} H(τ)`, `d/dτ B.I (τ⁻²) = infVec`. -/
theorem hasDerivAt_branch (C : InfChart f g) (B : LocalBranch f g) {τ : ℂ}
    (hτ : τ ∈ ball (0 : ℂ) C.r) (hτ0 : τ ≠ 0) (hB : (τ⁻¹) ^ 2 ∈ ball B.x₀ B.r)
    (hY : B.Y ((τ⁻¹) ^ 2) = (τ⁻¹) ^ (2 * g + 1) * C.H τ) :
    HasDerivAt (fun τ => B.I ((τ⁻¹) ^ 2)) (infVec g C.H τ) τ := by
  have hx : HasDerivAt (fun τ : ℂ => (τ⁻¹) ^ 2) (2 * τ⁻¹ * (-(τ ^ 2)⁻¹)) τ :=
    ((hasDerivAt_inv hτ0).pow 2).congr_deriv (by push_cast; ring)
  have h := (B.I_deriv _ hB).scomp τ hx
  refine h.congr_deriv ?_
  have hH := C.H_ne τ hτ
  funext k
  obtain ⟨j, hj⟩ : ∃ j, g = (k : ℕ) + 1 + j := ⟨g - 1 - k, by have := k.2; omega⟩
  have hexp : 2 * (g - 1 - (k : ℕ)) = 2 * j := by omega
  simp only [Pi.smul_apply, smul_eq_mul, omegaVec, infVec, hY, hexp]
  rw [show 2 * g + 1 = 2 * (k : ℕ) + 2 * j + 3 by omega]
  simp only [inv_pow, ← pow_mul]
  field_simp
  ring

end InfChart

end LSG.JacAn
