/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Abel2

/-!
# Derivatives of the local exponential (seed of ABVAR §2.2 a8)

At a generic pair `p = (x₁, x₂)` (base point of `localExp`, `z₀ = abel2 p`):

* `hasFDerivAt_abelInv`: `D(abelInv)(z₀) = abelJacInv p`, i.e.
  `∂x₁ = y₁ (x₂ dz₀ − dz₁)/(x₂ − x₁)`, `∂x₂ = y₂ (dz₁ − x₁ dz₀)/(x₂ − x₁)` — rational in `(xᵢ, yᵢ)` over `ℚ`;
* `hasFDerivAt_localExp_s₁`: `∂s₁ = b₀ dz₀ + b₁ dz₁`;
* `hasFDerivAt_localExp_s₂`: `∂s₂ = (b₁s₂ + b₀s₁) dz₀ − b₀ dz₁`.

With Grant's dictionary (ABVAR A0.1: `℘₂₂ = s₁`, `℘₁₂ = −s₂`, `℘₂₂₂ = b₁`, `℘₁₂₂ = b₀`,
`℘₁₁₂ = −b₀s₁ − b₁s₂`, and `z₀, z₁` = Grant's `u₁, u₂`) these read `∂ᵢ℘ⱼₖ = ℘ᵢⱼₖ`: a consistency check of the A0.1
model against the analytic construction.
-/

noncomputable section

open Polynomial Metric Filter Topology

namespace LSG.JacAn

variable {f : ℂ[X]} {B₁ B₂ : LocalBranch f 2} {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2)

include hp hx in
/-- The derivative of the local inverse of the Abel map at its base point is the explicit inverse Jacobian. -/
theorem hasFDerivAt_abelInv : HasFDerivAt (abelInv hp hx) (abelJacInv B₁ B₂ p) (abel2 B₁ B₂ p) := by
  have h := (hasStrictFDerivAt_abel2 B₁ B₂ hp hx).to_localInverse.hasFDerivAt
  refine h.congr_fderiv ?_
  rw [abelJacEquiv, ContinuousLinearEquiv.symm_equivOfInverse]
  rfl

/-- `0`-th coordinate projection on `ℂ²`. -/
abbrev pr0 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0

/-- `1`-st coordinate projection on `ℂ²`. -/
abbrev pr1 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1

include hp hx in
/-- **`∂s₁ = b₀ dz₀ + b₁ dz₁`** (`∂ᵢ℘₂₂ = ℘ᵢ₂₂`). -/
theorem hasFDerivAt_localExp_s₁ :
    HasFDerivAt (fun z => localExp hp hx z 0)
      (mumford B₁ B₂ p 3 • pr0 + mumford B₁ B₂ p 2 • pr1) (abel2 B₁ B₂ p) := by
  have hs : HasFDerivAt (fun q : ℂ × ℂ => q.1 + q.2)
      (ContinuousLinearMap.fst ℂ ℂ ℂ + ContinuousLinearMap.snd ℂ ℂ ℂ) (abelInv hp hx (abel2 B₁ B₂ p)) :=
    hasFDerivAt_fst.add hasFDerivAt_snd
  have h := hs.comp (abel2 B₁ B₂ p) (hasFDerivAt_abelInv hp hx)
  convert h using 1
  · funext z; simp [localExp, mumford]
  · have hx' : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
    have hx'' : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hx
    refine ContinuousLinearMap.ext fun v => ?_
    simp [abelJacInv, mumford]
    field_simp
    ring

include hp hx in
/-- **`∂s₂ = (b₁s₂ + b₀s₁) dz₀ − b₀ dz₁`** (`∂ᵢ℘₁₂ = ℘ᵢ₁₂`). -/
theorem hasFDerivAt_localExp_s₂ :
    HasFDerivAt (fun z => localExp hp hx z 1)
      ((mumford B₁ B₂ p 2 * mumford B₁ B₂ p 1 + mumford B₁ B₂ p 3 * mumford B₁ B₂ p 0) • pr0 -
        mumford B₁ B₂ p 3 • pr1) (abel2 B₁ B₂ p) := by
  have hs : HasFDerivAt (fun q : ℂ × ℂ => q.1 * q.2)
      ((abelInv hp hx (abel2 B₁ B₂ p)).1 • ContinuousLinearMap.snd ℂ ℂ ℂ +
        (abelInv hp hx (abel2 B₁ B₂ p)).2 • ContinuousLinearMap.fst ℂ ℂ ℂ)
      (abelInv hp hx (abel2 B₁ B₂ p)) :=
    hasFDerivAt_fst.mul hasFDerivAt_snd
  have h := hs.comp (abel2 B₁ B₂ p) (hasFDerivAt_abelInv hp hx)
  rw [abelInv_abel2_self hp hx] at h
  convert h using 1
  · funext z; simp [localExp, mumford]
  · have hx' : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
    have hx'' : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hx
    refine ContinuousLinearMap.ext fun v => ?_
    simp [abelJacInv, mumford]
    field_simp
    ring

end LSG.JacAn
