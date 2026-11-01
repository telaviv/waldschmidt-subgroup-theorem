/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.Fibre

/-!
# M2.4b: the fibre cocycle on all of `kerE` (generalising `ThetaData.fibT_add`)

`ThetaData.fibT_add` (`LSG.JacAnV.Fibre`) is stated for `ω ∈ latt`, but its ingredients (`thetaN_add`,
`fac_affine`, `pd_shift`) need only `IsPer G ω`, and `kerE G ⊆ IsPer` (`isPer_of_mem_kerE`). The `VBlock` field
`lift_per` quantifies over `base.per = kerE G`, so it needs this version.

* `ThetaData.facN_aff_isPer`: `facN ω z = a_ω · exp (L_ω z)` for `IsPer G ω`;
* `ThetaData.facN_ne_zero_isPer`;
* **`ThetaData.fibT_add_isPer`**: `T_k(z + ω, w + η̄(ω)) = facN(ω, z) · T_k(z, w)` for `IsPer G ω`.
-/

noncomputable section

namespace LSG.JacAn

open LSG.JacAnV

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

lemma ThetaData.facN_aff_isPer {ω : Fin 2 → ℂ} (hω : IsPer G ω) (z : Fin 2 → ℂ) :
    D.facN ω z = Complex.exp (-D.lamN ω) * D.fac ω 0 * Complex.exp (D.Lf ω z) := by
  rw [ThetaData.facN, D.fac_affine hω]; ring

lemma ThetaData.facN_ne_zero_isPer {ω : Fin 2 → ℂ} (hω : IsPer G ω) (z : Fin 2 → ℂ) : D.facN ω z ≠ 0 := by
  rw [ThetaData.facN]
  exact mul_ne_zero (Complex.exp_ne_zero _) (D.fac_ne_zero hω z)

/-- **The cocycle on `IsPer`**: `T_k(z + ω, w + η̄(ω)) = facN(ω, z) · T_k(z, w)`. -/
theorem ThetaData.fibT_add_isPer {ω : Fin 2 → ℂ} (hω : IsPer G ω) (k : Fin 9) (z : Fin 2 → ℂ) (w : ℂ) :
    D.fibT k (z + ω) (w + D.etaB ω) = D.facN ω z * D.fibT k z w := by
  have h0 : ∀ z, cmpV D.thetaN k (z + ω) =
      Complex.exp (-D.lamN ω) * D.fac ω 0 * Complex.exp (D.Lf ω z) * cmpV D.thetaN k z := fun z => by
    simp only [cmpV, D.thetaN_add hω z, D.facN_aff_isPer hω z, Pi.smul_apply, smul_eq_mul]
  have hd := KHyp.pd_shift (ent_cmp D.analyticAt_thetaN k) h0 0 z
  have h0z := h0 z
  simp only [cmpV] at h0z hd
  unfold ThetaData.fibT ThetaData.etaB
  rw [hd, map_add, h0z, D.facN_aff_isPer hω]
  ring

end LSG.JacAn
