/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.Fibre

/-!
# M2.2 (N5, kit): the pieces of the fibre-period formula that do not need the continuation

The fibre period `η̄([ζ^e]γ) = (3/5) ζ^{4e} perB5` (M2.md §2.2 N5) is assembled from:

1. `ThetaData.zetaB_add` (`Fibre.lean`): `η̄(ω) = ζ̄(z + ω) − ζ̄(z)` wherever `θ₀(z) ≠ 0`;
2. **`ThetaData.hasDerivAt_zetaB_comp`** (here): along a real path `c(t)` with `θ₀(c(t)) ≠ 0`,
   `d/dt ζ̄(c(t)) = −(℘₀₀(c) c₀′ + ℘₁₀(c) c₁′)` with `℘_{j0} = θ_{m(j,0)}/θ₀` (from `pd_zetaB`);
3. **`zeta_path_identity`** (here; the spike `scripts/m2_spike/zeta_path.*`): along a moving divisor `(x, y) + (x₀, y₀)`
   on `y² = 4x⁵ + 1` (Mumford chart, `℘₀₀ = X₁`, `℘₁₀ = X₂` of `grantJ`),
   `(℘₀₀ + x ℘₁₀) · x′/y = 3 x³ · x′/y + d/dt [(y₀ − y)/(2(x − x₀))]`;
4. `Beta.curveIntegral_cycleE e 3` (existing): `∫_{[ζ^e]γ} x³ dx/y = −(1/5)(ζ^{4e} − ζ^{4(e+1)}) B(4/5, 4/5)`.

The assembly is in `ThetaFollow.lean` (continuation), `FibreFTC.lean` (FTC) and `FibrePeriod.lean`
(`ThetaData.etaB_perVec`).
-/

noncomputable section

open Filter

namespace LSG.JacAn

open LSG.JacAnV

/-- **The second-kind identity along a moving divisor** (spike `zeta_path`, `c = 3`,
`R = (y₀ − y)/(2(x − x₀))`). Here `x′, y′` are the velocities of `(x, y)` on the curve (`2 y y′ = 20 x⁴ x′`). -/
theorem zeta_path_identity {x y x₀ y₀ x' y' : ℂ} (hy : y ^ 2 = 4 * x ^ 5 + 1) (hy₀ : y₀ ^ 2 = 4 * x₀ ^ 5 + 1)
    (hx : x ≠ x₀) (hy0 : y ≠ 0) (hv : 2 * y * y' = 20 * x ^ 4 * x') :
    (grantJ (mumfordPts x y x₀ y₀) 1 + x * grantJ (mumfordPts x y x₀ y₀) 2) * (x' / y) =
      3 * x ^ 3 * (x' / y) + (-y' * (x - x₀) - (y₀ - y) * x') / (2 * (x - x₀) ^ 2) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have key : (grantJ (mumfordPts x y x₀ y₀) 1 + x * grantJ (mumfordPts x y x₀ y₀) 2) * (x' / y) -
      (3 * x ^ 3 * (x' / y) + (-y' * (x - x₀) - (y₀ - y) * x') / (2 * (x - x₀) ^ 2)) =
      ((x - x₀) * (2 * y * y' - 20 * x ^ 4 * x') - x' * (y ^ 2 - 4 * x ^ 5 - 1) +
        x' * (y₀ ^ 2 - 4 * x₀ ^ 5 - 1)) / (4 * y * (x - x₀) ^ 2) := by
    simp only [grantJ, mumfordPts, Matrix.cons_val, Fin.isValue]
    field_simp
    ring
  have hnum : (x - x₀) * (2 * y * y' - 20 * x ^ 4 * x') - x' * (y ^ 2 - 4 * x ^ 5 - 1) +
      x' * (y₀ ^ 2 - 4 * x₀ ^ 5 - 1) = 0 := by
    linear_combination (x - x₀) * hv - x' * hy + x' * hy₀
  rw [hnum, zero_div] at key
  exact sub_eq_zero.mp key

/-- The derivative of the exact term `R(t) = (y₀ − Y(t))/(2(u(t) − x₀))`. -/
theorem hasDerivAt_exactTerm {u Y : ℝ → ℂ} {u' Y' : ℂ} {t : ℝ} (x₀ y₀ : ℂ) (hu : HasDerivAt u u' t)
    (hY : HasDerivAt Y Y' t) (hx : u t ≠ x₀) :
    HasDerivAt (fun t => (y₀ - Y t) / (2 * (u t - x₀)))
      ((-Y' * (u t - x₀) - (y₀ - Y t) * u') / (2 * (u t - x₀) ^ 2)) t := by
  have hd : 2 * (u t - x₀) ≠ 0 := mul_ne_zero two_ne_zero (sub_ne_zero.mpr hx)
  have h := ((hY.const_sub y₀).div ((hu.sub_const x₀).const_mul 2) hd)
  refine h.congr_deriv ?_
  have hd' : u t - x₀ ≠ 0 := sub_ne_zero.mpr hx
  field_simp

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- **`ζ̄` along a real path**: `d/dt ζ̄(c(t)) = −(℘₀₀ c₀′ + ℘₁₀ c₁′)`. -/
theorem ThetaData.hasDerivAt_zetaB_comp {c : ℝ → (Fin 2 → ℂ)} {c' : Fin 2 → ℂ} {t : ℝ}
    (hc : HasDerivAt c c' t) (hz : D.thetaN (c t) 0 ≠ 0) :
    HasDerivAt (fun t => D.zetaB (c t))
      (-(D.thetaN (c t) (mIdx 0 0) / D.thetaN (c t) 0 * c' 0 +
        D.thetaN (c t) (mIdx 1 0) / D.thetaN (c t) 0 * c' 1)) t := by
  have hf := ((D.zetaB_differentiableAt hz).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hc
  refine hf.congr_deriv ?_
  have hsplit : c' = c' 0 • (Pi.single 0 1 : Fin 2 → ℂ) + c' 1 • (Pi.single 1 1 : Fin 2 → ℂ) := by
    funext j; fin_cases j <;> simp
  have e0 := D.pd_zetaB 0 hz
  have e1 := D.pd_zetaB 1 hz
  unfold pd at e0 e1
  change (fderiv ℂ D.zetaB (c t)) c' = _
  conv_lhs => rw [hsplit, map_add, map_smul, map_smul, e0, e1]
  simp only [smul_eq_mul]
  ring

end LSG.JacAn
