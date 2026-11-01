/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Stage A2 glue: several-variable complex analysis (risk R-SCV)

Mathlib v4.35 has no Hartogs/Osgood theorem (a `ℂ`-differentiable map `ℂ^g → ℂ^g` is not known to be analytic), but
the analytic objects of the Abel map can be built analytically from the start, and then the following suffice:

* `analyticAt_localInverse`: the inverse-function-theorem local inverse of an analytic map with invertible derivative
  is analytic (from `OpenPartialHomeomorph.hasFPowerSeriesAt_symm`, which is stated for arbitrary complete spaces);
* `exists_sqrt_branch`: a holomorphic branch of `√F` near a point where `F ≠ 0`;
* `exists_primitive_ball`: a vector-valued holomorphic function on a disc has a primitive vanishing at the centre, and
  the primitive is analytic (Morera/`DifferentiableOn.isExactOn_ball` + one-variable Cauchy).

The identity theorem on connected open subsets of `ℂ^g` is Mathlib's
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (any normed domain), and composition is `AnalyticAt.comp`; no
glue is needed for those.
-/

noncomputable section

open Filter Topology Metric

namespace LSG.JacAn

section InverseFunction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Analytic inverse function theorem.** If `f` is analytic at `a` with invertible strict derivative `f'`, the
local inverse `hf.localInverse` is analytic at `f a`. -/
theorem analyticAt_localInverse {f : E → F} {f' : E ≃L[𝕜] F} {a : E} (hfa : AnalyticAt 𝕜 f a)
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    AnalyticAt 𝕜 (hf.localInverse f f' a) (f a) := by
  obtain ⟨p, hp⟩ := hfa
  have h1 : continuousMultilinearCurryFin1 𝕜 E F (p 1) = (f' : E →L[𝕜] F) :=
    hp.hasStrictFDerivAt.hasFDerivAt.unique hf.hasFDerivAt
  have hp1 : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm (f' : E →L[𝕜] F) := by
    rw [← h1, LinearIsometryEquiv.symm_apply_apply]
  have := (hf.toOpenPartialHomeomorph f).hasFPowerSeriesAt_symm (i := f')
    hf.mem_toOpenPartialHomeomorph_source (p := p) (by simpa using hp) hp1
  exact ⟨_, by simpa [HasStrictFDerivAt.localInverse_def] using this⟩

/-- The local inverse is analytic on a neighbourhood of `f a`. -/
theorem eventually_analyticAt_localInverse [CompleteSpace F] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hfa : AnalyticAt 𝕜 f a) (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ z in 𝓝 (f a), AnalyticAt 𝕜 (hf.localInverse f f' a) z :=
  (analyticAt_localInverse hfa hf).eventually_analyticAt

omit [CompleteSpace E] in
/-- Strict differentiability of an analytic map, with a prescribed derivative. -/
theorem hasStrictFDerivAt_of_analyticAt {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hfa : AnalyticAt 𝕜 f a) (hf : HasFDerivAt f f' a) : HasStrictFDerivAt f f' a := by
  have := hfa.hasStrictFDerivAt
  rwa [hf.fderiv] at this

end InverseFunction

section Branch

/-- **A holomorphic branch of `√F`.** If `F` is analytic at `x₀` and `y₀² = F x₀ ≠ 0`, then
`Y x = y₀ (F x / y₀²)^{1/2}` (principal branch) is analytic at `x₀`, `Y x₀ = y₀`, and `Y² = F` everywhere. -/
theorem exists_sqrt_branch {F : ℂ → ℂ} {x₀ y₀ : ℂ} (hF : AnalyticAt ℂ F x₀) (hy : y₀ ^ 2 = F x₀)
    (hy0 : y₀ ≠ 0) :
    ∃ Y : ℂ → ℂ, AnalyticAt ℂ Y x₀ ∧ Y x₀ = y₀ ∧ ∀ x, Y x ^ 2 = F x := by
  have hy2 : y₀ ^ 2 ≠ 0 := pow_ne_zero 2 hy0
  refine ⟨fun x => y₀ * (F x / y₀ ^ 2) ^ ((2 : ℂ)⁻¹), ?_, ?_, ?_⟩
  · refine analyticAt_const.mul ?_
    refine (hF.div analyticAt_const hy2).cpow analyticAt_const ?_
    change F x₀ / y₀ ^ 2 ∈ _
    rw [← hy, div_self hy2]
    exact Complex.one_mem_slitPlane
  · simp only
    rw [← hy, div_self hy2, Complex.one_cpow, mul_one]
  · intro x
    have h := Complex.cpow_nat_inv_pow (F x / y₀ ^ 2) (n := 2) two_ne_zero
    push_cast at h
    rw [mul_pow, h]
    field_simp

end Branch

section Primitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Primitive on a disc.** A holomorphic `f : ℂ → E` on `ball c r` has a primitive `G` with `G c = 0`; `G` is
analytic on the disc. -/
theorem exists_primitive_ball {f : ℂ → E} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) :
    ∃ G : ℂ → E, G c = 0 ∧ (∀ z ∈ ball c r, HasDerivAt G (f z) z) ∧
      AnalyticOnNhd ℂ G (ball c r) := by
  obtain ⟨G₀, hG₀⟩ := hf.isExactOn_ball
  refine ⟨fun z => G₀ z - G₀ c, by simp, fun z hz => (hG₀ z hz).sub_const _, ?_⟩
  have hd : DifferentiableOn ℂ (fun z => G₀ z - G₀ c) (ball c r) := fun z hz =>
    ((hG₀ z hz).sub_const _).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd isOpen_ball

end Primitive

end LSG.JacAn
