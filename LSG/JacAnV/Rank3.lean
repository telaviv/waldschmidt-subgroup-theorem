/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.FibrePeriod

/-!
# M2.2 (N6): the periods of `A_σ̄^♮` span `ℂ³`

With `perVec_eq` (`z_j([ζ^e]γ) = c_j (ζ^{j+1})^e`) and the fibre period formula
(`η̄([ζ^e]γ) = −3 c₃ (ζ⁴)^e`, `etaB_perVec_cJ`), the 3 × 3 period matrix of `[ζ^e]γ`, `e = 0, 1, 2`, is
`diag(c₀, c₁, −3c₃)` times a Vandermonde matrix in the distinct characters `ζ, ζ², ζ⁴`:

* **`ThetaData.period_det_ne_zero`**: `det [z₀, z₁, η̄]([ζ^e]γ)_{e<3} ≠ 0`.

The Legendre relation is not needed (M2.md N6).
-/

noncomputable section

namespace LSG.JacAn

open LSG.JacAnV Beta

variable {A : A1Facts} {B₁' B₂' : LocalBranch f₅ 2} {p' : ℂ × ℂ} {hp' : p' ∈ dom2 B₁' B₂'} {hx' : p'.1 ≠ p'.2}
  {G : GermRad A hp' hx'} (D : ThetaData G)

/-- `η̄([ζ^e]γ) = −3 c₃ (ζ⁴)^e`. -/
theorem ThetaData.etaB_perVec_cJ (SF : SurjFacts A) (e : Fin 4) :
    D.etaB (perVec (e : ℕ)) = -3 * cJ 3 * (zetaN 5 ^ 4) ^ (e : ℕ) := by
  rw [D.etaB_perVec SF e, perB5, cJ]
  have hB := betaG_eq 3
  have h45 : (((3 : ℕ) : ℂ) + 1) / 5 = 4 / 5 := by norm_num
  simp only [h45] at hB
  rw [hB, ← pow_mul, ← pow_mul, mul_comm 4 (e : ℕ)]
  norm_num
  ring

/-- **The period matrix of `A_σ̄^♮` has rank 3.** -/
theorem ThetaData.period_det_ne_zero (SF : SurjFacts A) :
    Matrix.det !![perVec 0 0, perVec 0 1, D.etaB (perVec 0);
      perVec 1 0, perVec 1 1, D.etaB (perVec 1);
      perVec 2 0, perVec 2 1, D.etaB (perVec 2)] ≠ 0 := by
  have h0 := D.etaB_perVec_cJ SF 0
  have h1 := D.etaB_perVec_cJ SF 1
  have h2 := D.etaB_perVec_cJ SF 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  set ζ := zetaN 5 with hζdef
  have hζ := zetaN_prim 5 (by norm_num)
  have hne : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have n1 : ζ - 1 ≠ 0 :=
    sub_ne_zero.mpr (by simpa using hζ.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num) (by norm_num))
  have n2 : ζ ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  have n3 : ζ ^ 3 - 1 ≠ 0 := sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  have hdet : Matrix.det !![perVec 0 0, perVec 0 1, D.etaB (perVec 0);
      perVec 1 0, perVec 1 1, D.etaB (perVec 1);
      perVec 2 0, perVec 2 1, D.etaB (perVec 2)] =
      -3 * cJ 0 * cJ 1 * cJ 3 * (ζ * (ζ - 1)) * (ζ * (ζ ^ 3 - 1)) * (ζ ^ 2 * (ζ ^ 2 - 1)) := by
    rw [h0, h1, h2, perVec_eq, perVec_eq, perVec_eq, perVec_eq, perVec_eq, perVec_eq, Matrix.det_fin_three]
    simp
    ring
  rw [hdet]
  have c0 := cJ_ne_zero (j := 0) (by norm_num)
  have c1 := cJ_ne_zero (j := 1) (by norm_num)
  have c3 := cJ_ne_zero (j := 3) (by norm_num)

  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) c0) c1) c3)
    (mul_ne_zero hne n1)) (mul_ne_zero hne n3)) (mul_ne_zero (pow_ne_zero 2 hne) n2)

end LSG.JacAn
