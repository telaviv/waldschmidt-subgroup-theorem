/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.LocalExpDeriv

/-!
# The Mumford-coordinate ODE of the local exponential (ABVAR §2.2 a8)

For a quintic `f = a₅x⁵ + a₄x⁴ + a₃x³ + a₂x² + a₁x + a₀` (`quintic`), the Mumford coordinates
`m = (s₁, s₂, b₁, b₀)` of the local exponential satisfy the closed polynomial system (`odeVF`)

* `∂s₁ = b₀ dz₀ + b₁ dz₁`,
* `∂s₂ = (b₁s₂ + b₀s₁) dz₀ − b₀ dz₁`,
* `∂b₁ = ½(a₂ + a₃s₁ + a₄(s₁² − 2s₂) + a₅(s₁³ − 4s₁s₂) − b₁²) dz₀ + ½(a₃ + 2a₄s₁ + a₅(3s₁² − 2s₂)) dz₁`,
* `∂b₀ = −½(−a₁ + 2a₃s₂ + 2a₄s₁s₂ + a₅(2s₁²s₂ − 3s₂²) + 2b₀b₁) dz₀ + (∂b₁/∂z₀) dz₁`,

with coefficients in `ℚ[a₀, …, a₅]` (`hasFDerivAt_localExp` at the base point, `localExp_ode` on a neighbourhood).
For the model `f = 4x⁵ + 1` this gives e.g. `∂²b₁/∂z₁ = 6s₁² − 4s₂` (Grant's `℘₂₂₂₂ = 6℘₂₂² + 4℘₁₂`).
The polynomial right-hand sides were found by a weighted ansatz (`scripts/abvar_spike`-style sympy, not trusted);
Lean checks them.
-/

noncomputable section

open Polynomial Metric Filter Topology

namespace LSG.JacAn

variable {f : ℂ[X]} {g : ℕ}

/-- `Y' = f'/(2Y)` on a branch. -/
lemma LocalBranch.hasDerivAt_Y (B : LocalBranch f g) {x : ℂ} (hx : x ∈ ball B.x₀ B.r) :
    HasDerivAt B.Y ((derivative f).eval x / (2 * B.Y x)) x := by
  have hd := (B.Y_an x hx).differentiableAt.hasDerivAt
  have hf : HasDerivAt (fun x => B.Y x ^ 2) ((derivative f).eval x) x := by
    refine (f.hasDerivAt x).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy using B.Y_sq y hy
  have h := (hd.pow 2).unique hf
  have hY := B.Y_ne x hx
  convert hd using 1
  rw [← h]; field_simp; ring

/-- The quintic `a₅x⁵ + a₄x⁴ + a₃x³ + a₂x² + a₁x + a₀`. -/
def quintic (a₀ a₁ a₂ a₃ a₄ a₅ : ℂ) : ℂ[X] :=
  C a₅ * X ^ 5 + C a₄ * X ^ 4 + C a₃ * X ^ 3 + C a₂ * X ^ 2 + C a₁ * X + C a₀

lemma eval_quintic (a₀ a₁ a₂ a₃ a₄ a₅ x : ℂ) :
    (quintic a₀ a₁ a₂ a₃ a₄ a₅).eval x = a₅ * x ^ 5 + a₄ * x ^ 4 + a₃ * x ^ 3 + a₂ * x ^ 2 + a₁ * x + a₀ := by
  simp [quintic]

lemma eval_derivative_quintic (a₀ a₁ a₂ a₃ a₄ a₅ x : ℂ) :
    (derivative (quintic a₀ a₁ a₂ a₃ a₄ a₅)).eval x =
      5 * a₅ * x ^ 4 + 4 * a₄ * x ^ 3 + 3 * a₃ * x ^ 2 + 2 * a₂ * x + a₁ := by
  simp [quintic]; ring

/-- `∂b₁/∂z₀` (also `∂b₀/∂z₁`) as a polynomial in `m = (s₁, s₂, b₁, b₀)`. -/
def odeB1z0 (a₂ a₃ a₄ a₅ : ℂ) (m : Fin 4 → ℂ) : ℂ :=
  (a₂ + a₃ * m 0 + a₄ * m 0 ^ 2 - 2 * a₄ * m 1 + a₅ * m 0 ^ 3 - 4 * a₅ * m 0 * m 1 - m 2 ^ 2) / 2

/-- `∂b₁/∂z₁`. -/
def odeB1z1 (a₃ a₄ a₅ : ℂ) (m : Fin 4 → ℂ) : ℂ :=
  (a₃ + 2 * a₄ * m 0 + 3 * a₅ * m 0 ^ 2 - 2 * a₅ * m 1) / 2

/-- `∂b₀/∂z₀`. -/
def odeB0z0 (a₁ a₃ a₄ a₅ : ℂ) (m : Fin 4 → ℂ) : ℂ :=
  -(-a₁ + 2 * a₃ * m 1 + 2 * a₄ * m 0 * m 1 + 2 * a₅ * m 0 ^ 2 * m 1 - 3 * a₅ * m 1 ^ 2 +
    2 * m 3 * m 2) / 2

/-- **The vector field**: `odeVF a m i` is the differential of the `i`-th Mumford coordinate. -/
def odeVF (a₁ a₂ a₃ a₄ a₅ : ℂ) (m : Fin 4 → ℂ) : Fin 4 → ((Fin 2 → ℂ) →L[ℂ] ℂ) :=
  ![m 3 • pr0 + m 2 • pr1,
    (m 2 * m 1 + m 3 * m 0) • pr0 - m 3 • pr1,
    odeB1z0 a₂ a₃ a₄ a₅ m • pr0 + odeB1z1 a₃ a₄ a₅ m • pr1,
    odeB0z0 a₁ a₃ a₄ a₅ m • pr0 + odeB1z0 a₂ a₃ a₄ a₅ m • pr1]

variable {B₁ B₂ : LocalBranch f 2} {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2)

include hp hx in
theorem hasFDerivAt_localExp_b₁ {a₀ a₁ a₂ a₃ a₄ a₅ : ℂ} (hf : f = quintic a₀ a₁ a₂ a₃ a₄ a₅) :
    HasFDerivAt (fun z => localExp hp hx z 2)
      (odeB1z0 a₂ a₃ a₄ a₅ (mumford B₁ B₂ p) • pr0 + odeB1z1 a₃ a₄ a₅ (mumford B₁ B₂ p) • pr1)
      (abel2 B₁ B₂ p) := by
  have hf1 : HasFDerivAt (Prod.fst : ℂ × ℂ → ℂ) (ContinuousLinearMap.fst ℂ ℂ ℂ) p := hasFDerivAt_fst
  have hf2 : HasFDerivAt (Prod.snd : ℂ × ℂ → ℂ) (ContinuousLinearMap.snd ℂ ℂ ℂ) p := hasFDerivAt_snd
  have hY₁ := (B₁.hasDerivAt_Y hp.1).comp_hasFDerivAt p hf1
  have hY₂ := (B₂.hasDerivAt_Y hp.2).comp_hasFDerivAt p hf2
  have hI := (hasDerivAt_inv (sub_ne_zero.mpr hx)).comp_hasFDerivAt p (hf1.sub hf2)
  have hb := (hY₁.sub hY₂).mul hI
  rw [← abelInv_abel2_self hp hx] at hb
  have h := hb.comp (abel2 B₁ B₂ p) (hasFDerivAt_abelInv hp hx)
  rw [abelInv_abel2_self hp hx] at h
  convert h using 1
  · funext z; simp [localExp, mumford, div_eq_mul_inv]
  · have hx' : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
    have hx'' : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hx
    have hY1 := B₁.Y_ne _ hp.1
    have hY2 := B₂.Y_ne _ hp.2
    have h1 := B₁.Y_sq _ hp.1
    have h2 := B₂.Y_sq _ hp.2
    subst hf
    rw [eval_quintic] at h1 h2
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [odeB1z0, odeB1z1, mumford, abelJacInv, eval_derivative_quintic]
    simp
    linear_combination (norm := skip)
      ((-(v 0 * p.1) - v 0 * p.2 + 2 * v 1) / (2 * (p.1 - p.2) ^ 3)) * h1 +
      ((v 0 * p.1 + v 0 * p.2 - 2 * v 1) / (2 * (p.1 - p.2) ^ 3)) * h2
    field_simp
    ring

include hp hx in
theorem hasFDerivAt_localExp_b₀ {a₀ a₁ a₂ a₃ a₄ a₅ : ℂ} (hf : f = quintic a₀ a₁ a₂ a₃ a₄ a₅) :
    HasFDerivAt (fun z => localExp hp hx z 3)
      (odeB0z0 a₁ a₃ a₄ a₅ (mumford B₁ B₂ p) • pr0 + odeB1z0 a₂ a₃ a₄ a₅ (mumford B₁ B₂ p) • pr1)
      (abel2 B₁ B₂ p) := by
  have hf1 : HasFDerivAt (Prod.fst : ℂ × ℂ → ℂ) (ContinuousLinearMap.fst ℂ ℂ ℂ) p := hasFDerivAt_fst
  have hf2 : HasFDerivAt (Prod.snd : ℂ × ℂ → ℂ) (ContinuousLinearMap.snd ℂ ℂ ℂ) p := hasFDerivAt_snd
  have hY₁ := (B₁.hasDerivAt_Y hp.1).comp_hasFDerivAt p hf1
  have hY₂ := (B₂.hasDerivAt_Y hp.2).comp_hasFDerivAt p hf2
  have hI := (hasDerivAt_inv (sub_ne_zero.mpr hx)).comp_hasFDerivAt p (hf1.sub hf2)
  have hb := ((hf1.mul hY₂).sub (hf2.mul hY₁)).mul hI
  rw [← abelInv_abel2_self hp hx] at hb
  have h := hb.comp (abel2 B₁ B₂ p) (hasFDerivAt_abelInv hp hx)
  rw [abelInv_abel2_self hp hx] at h
  convert h using 1
  · funext z; simp [localExp, mumford, div_eq_mul_inv]
  · have hx' : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
    have hx'' : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hx
    have hY1 := B₁.Y_ne _ hp.1
    have hY2 := B₂.Y_ne _ hp.2
    have h1 := B₁.Y_sq _ hp.1
    have h2 := B₂.Y_sq _ hp.2
    subst hf
    rw [eval_quintic] at h1 h2
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [odeB0z0, odeB1z0, mumford, abelJacInv, eval_derivative_quintic]
    simp
    linear_combination (norm := skip)
      ((2 * v 0 * p.1 * p.2 - v 1 * p.1 - v 1 * p.2) / (2 * (p.1 - p.2) ^ 3)) * h1 +
      ((-(2 * v 0 * p.1 * p.2) + v 1 * p.1 + v 1 * p.2) / (2 * (p.1 - p.2) ^ 3)) * h2
    field_simp
    ring

include hp hx in
/-- **The ODE at the base point**: `D(localExp_i)(z₀) = odeVF a (localExp z₀) i`. -/
theorem hasFDerivAt_localExp {a₀ a₁ a₂ a₃ a₄ a₅ : ℂ} (hf : f = quintic a₀ a₁ a₂ a₃ a₄ a₅) (i : Fin 4) :
    HasFDerivAt (fun z => localExp hp hx z i) (odeVF a₁ a₂ a₃ a₄ a₅ (localExp hp hx (abel2 B₁ B₂ p)) i)
      (abel2 B₁ B₂ p) := by
  rw [localExp_abel2_self hp hx]
  fin_cases i
  · exact hasFDerivAt_localExp_s₁ hp hx
  · exact hasFDerivAt_localExp_s₂ hp hx
  · exact hasFDerivAt_localExp_b₁ hp hx hf
  · exact hasFDerivAt_localExp_b₀ hp hx hf

include hp hx in
/-- Change of base point: near `abel2 q` (`q = abelInv z`), the local inverses based at `p` and at `q` agree. -/
theorem abelInv_eventuallyEq_rebase {z : Fin 2 → ℂ}
    (hzt : z ∈ ((hasStrictFDerivAt_abel2 B₁ B₂ hp hx).toOpenPartialHomeomorph (abel2 B₁ B₂)).target)
    (hq : abelInv hp hx z ∈ dom2 B₁ B₂) (hqx : (abelInv hp hx z).1 ≠ (abelInv hp hx z).2) :
    abelInv hq hqx =ᶠ[𝓝 (abel2 B₁ B₂ (abelInv hp hx z))] abelInv hp hx := by
  set e := (hasStrictFDerivAt_abel2 B₁ B₂ hp hx).toOpenPartialHomeomorph (abel2 B₁ B₂) with he
  have hqs : abelInv hp hx z ∈ e.source := e.map_target hzt
  have hc : ContinuousAt (abelInv hq hqx) (abel2 B₁ B₂ (abelInv hp hx z)) :=
    HasStrictFDerivAt.localInverse_continuousAt _
  have hsrc : e.source ∈ 𝓝 (abelInv hq hqx (abel2 B₁ B₂ (abelInv hp hx z))) := by
    rw [abelInv_abel2_self hq hqx]; exact e.open_source.mem_nhds hqs
  filter_upwards [abel2_abelInv hq hqx, hc.preimage_mem_nhds hsrc] with z' h1 h2
  have h3 : e (abelInv hq hqx z') = z' := by
    rw [he, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]; exact h1
  have h4 : e.symm (e (abelInv hq hqx z')) = abelInv hq hqx z' := e.left_inv h2
  rw [h3] at h4
  exact h4.symm

include hp hx in
/-- **The ODE on a neighbourhood**: `D(localExp_i)(z) = odeVF a (localExp z) i` for all `z` near `z₀`. -/
theorem localExp_ode {a₀ a₁ a₂ a₃ a₄ a₅ : ℂ} (hf : f = quintic a₀ a₁ a₂ a₃ a₄ a₅) (i : Fin 4) :
    ∀ᶠ z in 𝓝 (abel2 B₁ B₂ p),
      HasFDerivAt (fun z => localExp hp hx z i) (odeVF a₁ a₂ a₃ a₄ a₅ (localExp hp hx z) i) z := by
  set e := (hasStrictFDerivAt_abel2 B₁ B₂ hp hx).toOpenPartialHomeomorph (abel2 B₁ B₂) with he
  have ht : e.target ∈ 𝓝 (abel2 B₁ B₂ p) :=
    e.open_target.mem_nhds (HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target _)
  filter_upwards [eventually_abelInv_good hp hx, ht] with z hz hzt
  have hqz : abel2 B₁ B₂ (abelInv hp hx z) = z := by
    have := e.right_inv hzt
    rwa [he, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at this
  have hD := hasFDerivAt_localExp hz.1 hz.2 hf i
  rw [localExp_abel2_self, hqz] at hD
  have hEq := abelInv_eventuallyEq_rebase hp hx hzt hz.1 hz.2
  rw [hqz] at hEq
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [hEq] with z' hz'
  simp only [localExp, Function.comp, hz']

end LSG.JacAn
