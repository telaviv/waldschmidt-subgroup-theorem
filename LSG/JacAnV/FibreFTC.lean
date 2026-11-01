/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.ThetaFollow
import LSG.JacAnV.PeriodKit

/-!
# M2.3 (N5, FTC): `ζ̄(z₀ + A(t)) + 3 A⁽³⁾(t) + R(t)` is constant along a moving divisor

For a path `(u, Y) + (α, y₀)` from the base with the `g = 2` and `g = 4` Abel integrals `A`, `A₄`:

  `Φ(t) = ζ̄(z₀ + A(t)) + 3 A₄(t)₃ + (y₀ − Y(t)) / (2 (u(t) − α))`   (`ThetaData.phiP`).

* **`ThetaData.phiP_locally_const`**: near every `s ∈ [0, 1]`, `Φ = Φ(s)`. In a local `x`-chart, `Φ = H(u(t)) + C`
  with `H' = 0`: `follow_theta_local` gives `℘_{j0}` on the moving divisor, `pd_zetaB`, and `zeta_path_identity`.
* **`ThetaData.phiP_one`**: `Φ(1) = Φ(0)`.
* `ThetaData.thetaN_zero_ne_path`: `θ₀(z₀ + A(s)) ≠ 0` along the path.
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

open LSG.JacAnV

/-- Two branches (for any `g`, `g'`) agreeing at a point agree nearby. -/
lemma branch_Y_eventually_eq {g g' : ℕ} {B : LocalBranch f₅ g} {B' : LocalBranch f₅ g'} {x₀ : ℂ}
    (h1 : x₀ ∈ ball B.x₀ B.r) (h2 : x₀ ∈ ball B'.x₀ B'.r) (hY : B.Y x₀ = B'.Y x₀) :
    ∀ᶠ x in 𝓝 x₀, B'.Y x = B.Y x := by
  have hc : ContinuousAt (fun x => B.Y x + B'.Y x) x₀ :=
    (B.Y_an _ h1).continuousAt.add (B'.Y_an _ h2).continuousAt
  have hne : B.Y x₀ + B'.Y x₀ ≠ 0 := by
    rw [← hY, ← two_mul]; exact mul_ne_zero two_ne_zero (B.Y_ne _ h1)
  filter_upwards [hc.eventually_ne hne, isOpen_ball.mem_nhds h1, isOpen_ball.mem_nhds h2] with x hx hx1 hx2
  have e : (B'.Y x - B.Y x) * (B.Y x + B'.Y x) = 0 := by
    have := B.Y_sq x hx1; have := B'.Y_sq x hx2
    linear_combination B'.Y_sq x hx2 - B.Y_sq x hx1
  exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hx)

/-- The derivative of a branch: `2 Y Y′ = 20 x⁴`. -/
lemma branch_hasDerivAt_Y {g : ℕ} (B : LocalBranch f₅ g) {x : ℂ} (hx : x ∈ ball B.x₀ B.r) :
    ∃ Y' : ℂ, HasDerivAt B.Y Y' x ∧ 2 * B.Y x * Y' = 20 * x ^ 4 * 1 := by
  have hY := (B.Y_an x hx).differentiableAt.hasDerivAt
  refine ⟨deriv B.Y x, hY, ?_⟩
  have h1 := hY.pow 2
  have h2 : HasDerivAt (fun x : ℂ => 4 * x ^ 5 + 1) (4 * (5 * x ^ 4)) x := by
    simpa using ((hasDerivAt_pow 5 x).const_mul 4).add_const 1
  have hev : (fun x => B.Y x ^ 2) =ᶠ[𝓝 x] fun x : ℂ => 4 * x ^ 5 + 1 := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    rw [B.Y_sq y hy, f₅_eval]
  have := (h1.congr_of_eventuallyEq hev.symm).unique h2
  simp only [Nat.cast_ofNat, pow_one] at this
  linear_combination this

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  (G₀ : GermRad A hp hx)
  {B₁' B₂' : LocalBranch f₅ 2} {p' : ℂ × ℂ} {hp' : p' ∈ dom2 B₁' B₂'} {hx' : p'.1 ≠ p'.2}
  {G : GermRad A hp' hx'} (D : ThetaData G)

/-- `Φ(t) = ζ̄(z₀ + A(t)) + 3 A₄(t)₃ + (y₀ − Y(t))/(2(u(t) − α))`. -/
def ThetaData.phiP (z₀ : Fin 2 → ℂ) (Ap : ℝ → (Fin 2 → ℂ)) (A₄ : ℝ → (Fin 4 → ℂ)) (u Y : ℝ → ℂ) (α y₀ : ℂ)
    (t : ℝ) : ℂ :=
  D.zetaB (z₀ + Ap t) + 3 * A₄ t 3 + (y₀ - Y t) / (2 * (u t - α))

section path

variable {z₀ : Fin 2 → ℂ} {b : ℂ} (hb : baseP hp hx = b • D.thetaN z₀) (k : ℕ)
  {α y₀ : ℂ} (hαB : α ∈ ball B₂.x₀ B₂.r) (hy₀ : B₂.Y α = y₀) (hy₀sq : y₀ ^ 2 = 4 * α ^ 5 + 1)
  {u Y : ℝ → ℂ} {Ap : ℝ → (Fin 2 → ℂ)} {A₄ : ℝ → (Fin 4 → ℂ)} (hA : IsAbelAlong f₅ 2 u Y Ap) (hA0 : Ap 0 = 0)
  (hA₄ : IsAbelAlong f₅ 4 u Y A₄)
  (hu : ContinuousOn u (Icc 0 1)) (hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u t ≠ α)
  (hstart : mumfordPts (u 0) (Y 0) α y₀ = mumford B₁ B₂ p)
  (hU : ∀ t ∈ Icc (0 : ℝ) 1, Ap t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G₀.ε))

include hb hαB hy₀ hA hA0 hu hdiag hstart hU in
/-- `θ₀ ≠ 0` along the path. -/
theorem ThetaData.thetaN_zero_ne_path {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : D.thetaN (z₀ + Ap s) 0 ≠ 0 := by
  obtain ⟨B, ε, hε, -, hev⟩ := follow_theta_local G₀ D hb k hαB hy₀ hA hA0 hu hdiag hstart hU hs
  obtain ⟨-, -, hpar⟩ := hev.self_of_nhds
  rw [sub_self, add_zero] at hpar
  exact hpar.zero_ne (grantJ_zero _) (D.thetaN_ne_zero _)

include hb hαB hy₀ hy₀sq hA hA0 hA₄ hu hdiag hstart hU in
/-- **`Φ` is locally constant on `[0, 1]`.** -/
theorem ThetaData.phiP_locally_const {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ t in 𝓝[Icc 0 1] s, D.phiP z₀ Ap A₄ u Y α y₀ t = D.phiP z₀ Ap A₄ u Y α y₀ s := by
  obtain ⟨B, ε, hε, hB, hev⟩ := follow_theta_local G₀ D hb k hαB hy₀ hA hA0 hu hdiag hstart hU hs
  obtain ⟨B4, ε4, hε4, hB4⟩ := hA₄ s hs
  have hs2 := hB s ⟨mem_ball_self hε, hs⟩
  have hs4 := hB4 s ⟨mem_ball_self hε4, hs⟩
  have hYY := branch_Y_eventually_eq hs2.1 hs4.1 (hs2.2.1.trans hs4.2.1.symm)
  set H : ℂ → ℂ := fun x => D.zetaB (z₀ + Ap s + (B.I x - B.I (u s))) + 3 * B4.I x 3 +
    (y₀ - B.Y x) / (2 * (x - α)) with hHdef
  have hder : ∀ᶠ x in 𝓝 (u s), HasDerivAt H 0 x := by
    filter_upwards [hev, hYY, isOpen_ball.mem_nhds hs4.1] with x ⟨hxB, hxα, hpar⟩ hxY hxB4
    set Z := z₀ + Ap s + (B.I x - B.I (u s)) with hZ
    have h0 : D.thetaN Z 0 ≠ 0 := hpar.zero_ne (grantJ_zero _) (D.thetaN_ne_zero _)
    have hn := hpar.normalize_eq (grantJ_zero _) h0
    have hm : ∀ m : Fin 9, D.thetaN Z m / D.thetaN Z 0 = grantJ (mumfordPts x (B.Y x) α y₀) m := by
      intro m; rw [← hn]; simp only [normalize, Pi.smul_apply, smul_eq_mul]; field_simp
    have hz : HasDerivAt (fun x => z₀ + Ap s + (B.I x - B.I (u s))) (omegaVec 2 B.Y x) x :=
      ((B.I_deriv x hxB).sub_const _).const_add _
    have hζ := (D.zetaB_differentiableAt h0).hasFDerivAt.comp_hasDerivAt x hz
    have hYx := B.Y_ne x hxB
    have hval : fderiv ℂ D.zetaB Z (omegaVec 2 B.Y x) =
        -(grantJ (mumfordPts x (B.Y x) α y₀) 1 * (1 / B.Y x) +
          grantJ (mumfordPts x (B.Y x) α y₀) 2 * (x / B.Y x)) := by
      have hsplit : omegaVec 2 B.Y x = (1 / B.Y x) • (Pi.single 0 1 : Fin 2 → ℂ) +
          (x / B.Y x) • (Pi.single 1 1 : Fin 2 → ℂ) := by
        funext j; fin_cases j <;> simp [omegaVec]
      have e0 := D.pd_zetaB 0 h0
      have e1 := D.pd_zetaB 1 h0
      unfold pd at e0 e1
      rw [hsplit, map_add, map_smul, map_smul, e0, e1, hm, hm]
      simp only [mIdx, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, Fin.isValue]
      ring
    have hI4 : HasDerivAt (fun x => B4.I x 3) (x ^ 3 / B.Y x) x := by
      have := hasDerivAt_pi.mp (B4.I_deriv x hxB4) 3
      simpa [omegaVec, hxY] using this
    obtain ⟨Y', hY', hY'eq⟩ := branch_hasDerivAt_Y B hxB
    have hd2 : 2 * (x - α) ≠ 0 := mul_ne_zero two_ne_zero (sub_ne_zero.mpr hxα)
    have hR : HasDerivAt (fun x => (y₀ - B.Y x) / (2 * (x - α)))
        ((-Y' * (x - α) - (y₀ - B.Y x) * 1) / (2 * (x - α) ^ 2)) x := by
      refine ((hY'.const_sub y₀).div (((hasDerivAt_id x).sub_const α).const_mul 2) hd2).congr_deriv ?_
      have : x - α ≠ 0 := sub_ne_zero.mpr hxα
      simp only [id]
      field_simp
    have hsum := (hζ.add (hI4.const_mul 3)).add hR
    refine hsum.congr_deriv ?_
    have hy : B.Y x ^ 2 = 4 * x ^ 5 + 1 := by rw [B.Y_sq x hxB, f₅_eval]
    have hid := zeta_path_identity hy hy₀sq hxα hYx hY'eq
    rw [hval]
    linear_combination -hid
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hder
  have hconst : ∀ x ∈ ball (u s) r, H x = H (u s) := fun x hx =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun y hy => (hball y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hball y hy).deriv) hx (mem_ball_self hr)
  have hut : ∀ᶠ t in 𝓝[Icc 0 1] s, u t ∈ ball (u s) r :=
    (hu s hs).preimage_mem_nhdsWithin (isOpen_ball.mem_nhds (mem_ball_self hr))
  filter_upwards [hut, inter_mem_nhdsWithin (Icc 0 1) (ball_mem_nhds s (lt_min hε hε4)),
    self_mem_nhdsWithin] with t ht hball' htI
  have htε : t ∈ ball s ε ∩ Icc 0 1 := ⟨ball_subset_ball (min_le_left _ _) hball'.2, htI⟩
  have htε4 : t ∈ ball s ε4 ∩ Icc 0 1 := ⟨ball_subset_ball (min_le_right _ _) hball'.2, htI⟩
  have ht2 := hB t htε
  have hAt : Ap t - Ap s = B.I (u t) - B.I (u s) := hs2.2.2 t htε
  have hA4t : A₄ t - A₄ s = B4.I (u t) - B4.I (u s) := hs4.2.2 t htε4
  have hA4t3 := congrFun hA4t 3
  simp only [Pi.sub_apply] at hA4t3
  have hHt := hconst (u t) ht
  simp only [hHdef, sub_self, add_zero] at hHt
  unfold ThetaData.phiP
  rw [show z₀ + Ap t = z₀ + Ap s + (B.I (u t) - B.I (u s)) by rw [← hAt]; abel, ← ht2.2.1, ← hs2.2.1]
  linear_combination hHt + 3 * hA4t3

include hb hαB hy₀ hy₀sq hA hA0 hA₄ hu hdiag hstart hU in
/-- **`Φ(1) = Φ(0)`.** -/
theorem ThetaData.phiP_one : D.phiP z₀ Ap A₄ u Y α y₀ 1 = D.phiP z₀ Ap A₄ u Y α y₀ 0 := by
  have h := const_of_locally_const_Icc (g := 1) (φ := fun t => fun _ : Fin 1 => D.phiP z₀ Ap A₄ u Y α y₀ t)
    (α := 0) (β := 1) (fun τ hτ => by
      filter_upwards [D.phiP_locally_const G₀ hb k hαB hy₀ hy₀sq hA hA0 hA₄ hu hdiag hstart hU hτ] with τ' h'
      rw [h']) (a := 1) (b := 0) ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
  exact congrFun h 0

end path

end LSG.JacAn
