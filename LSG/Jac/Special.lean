/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.A1Facts
import LSG.Jac.Laws
import LSG.Jac.Model

/-!
# (P3) The special base point is nondegenerate

`P₀ = grantJ (mumfordPts' 0 (−1) α 3)`, the divisor `(0, −1) + (α, 3)` with `α⁵ = 2`. In `ℚ(α)` its Grant
coordinates are `(1, α³, 0, α, −2α², α, −1, 2α⁴, −α⁴)`, and `law0 P₀ [−1]P₀ = 128 α · e₄` (only the `X₄` coordinate
is computed here: `X₄ = 128 α ≠ 0`). Any fifth root of 2 works; we take one from algebraic closedness.
-/

namespace LSG.Jac

open LSG.JacAn Data

/-- The Grant coordinates of `P₀` (for any `α` with `α⁵ = 2`). -/
lemma grantJ_P0 {α : ℂ} (h : α ^ 5 = 2) :
    grantJ (mumfordPts' 0 (-1) α 3) = ![1, α ^ 3, 0, α, -2 * α ^ 2, α, -1, 2 * α ^ 4, -α ^ 4] := by
  have hα : α ≠ 0 := by rintro rfl; norm_num at h
  have h2 : ((-1 : ℂ) - 3) / (0 - α) = 2 * α ^ 4 := by
    rw [div_eq_iff (by simpa using hα)]; linear_combination (2 : ℂ) * h
  have h3 : ((0 : ℂ) * 3 - α * (-1)) / (0 - α) = -1 := by
    field_simp; ring
  funext i
  fin_cases i <;> simp only [grantJ, mumfordPts', Matrix.cons_val, h2, h3] <;> simp <;>
    first | ring1 | linear_combination (α ^ 3) * h | linear_combination (-2 * α ^ 2) * h |
      linear_combination (2 * α ^ 3 - 1) * h | linear_combination (8 * α ^ 2 - 8 * α ^ 7) * h |
      linear_combination (2 : ℂ) * α ^ 3 * h | linear_combination (-2 * α ^ 7 - 2 * α ^ 2) * h

/-- `X₄` of `law0 P₀ [−1]P₀` is `128 α`. -/
lemma law0_P0_four {α : ℂ} (h : α ^ 5 = 2) :
    lawPt 0 (grantJ (mumfordPts' 0 (-1) α 3)) (negP (grantJ (mumfordPts' 0 (-1) α 3))) 4 = 128 * α := by
  rw [grantJ_P0 h]
  have hL : law 4 0 = L40 := rfl
  simp only [lawPt, A32, show ((4 : Fin 9) : ℕ) = 4 from rfl, show ((0 : Fin 9) : ℕ) = 0 from rfl, hL]
  simp [L40, evalSP, evalRow, xmono, digit, Fin.prod_univ_succ, sval, negP]
  linear_combination (-64 * α ^ 11 + 288 * α ^ 6 + 64 * α) * h

/-- **(P3) `special_hP₀`**, in the exact form of the `A1Facts` field. -/
theorem special_hP0 : ∃ α : ℂ, α ^ 5 = 2 ∧
    lawPt 0 (grantJ (mumfordPts' 0 (-1) α 3)) (negP (grantJ (mumfordPts' 0 (-1) α 3))) 4 ≠ 0 := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℂ) (by norm_num : 0 < 5)
  refine ⟨α, hα, ?_⟩
  rw [law0_P0_four hα]
  have : α ≠ 0 := by rintro rfl; norm_num at hα
  exact mul_ne_zero (by norm_num) this

end LSG.Jac
