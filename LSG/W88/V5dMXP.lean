/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dMXGcm
import LSG.W88.MStarCopyMXP
import LSG.W88.V5d2Iso

/-!
# Theorem MX′: the group of `gmXP` in the class `𝒞`

`G'' = G_i × G_ρ` of `lean_mstar`'s `gmXP b` is in the class `𝒞` with `d₀ = d₁ = 0`, the curves
`mxLs r = (E_i)^n ++ (E_ρ)^n` of Theorem MX, `r = 2` and the push-out matrix `mxpM b`:
row `0` (the coordinate `s₁`) is `θᵀ` on the `E_ρ` block, row `1` (`s₂`) is `θᵀ` on the `E_i` block.
`mxpIota : TanV 0 0 (n + n) 2 ≅ TXP r` reindexes the elliptic coordinates.
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy

variable {r : ℕ}

/-- The push-out matrix: `s₁ = θᵀ w_ρ`, `s₂ = θᵀ w_i`. -/
noncomputable def mxpM {r : ℕ} (b : Fin r → ℂ) : Matrix (Fin 2) (Fin (mxN r + mxN r)) ℂ :=
  ![Fin.append (fun _ => 0) (fun i => theta I b ((mxE r).symm i)),
    Fin.append (fun i => theta I b ((mxE r).symm i)) (fun _ => 0)]

/-- `TanV 0 0 (n + n) 2 ≅ TXP r`. -/
noncomputable def mxpIota (r : ℕ) : TanV 0 0 (mxN r + mxN r) 2 ≃ₗ[ℂ] TXP r where
  toFun x := (fun h => x.2.2.1 (Fin.castAdd _ (mxE r h)),
    fun h => x.2.2.1 (Fin.natAdd _ (mxE r h)), x.2.2.2 0, x.2.2.2 1)
  invFun v := (0, 0, Fin.append (fun i => v.1 ((mxE r).symm i))
    (fun i => v.2.1 ((mxE r).symm i)), ![v.2.2.1, v.2.2.2])
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i; exact i.elim0
    · funext i; exact i.elim0
    · simp only [Equiv.apply_symm_apply]; exact Fin.append_castAdd_natAdd
    · funext i; fin_cases i <;> rfl
  right_inv v := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl))
    · funext h
      change Fin.append (fun i => v.1 ((mxE r).symm i)) (fun i => v.2.1 ((mxE r).symm i))
        (Fin.castAdd (mxN r) (mxE r h)) = v.1 h
      rw [Fin.append_left, Equiv.symm_apply_apply]
    · funext h
      change Fin.append (fun i => v.1 ((mxE r).symm i)) (fun i => v.2.1 ((mxE r).symm i))
        (Fin.natAdd (mxN r) (mxE r h)) = v.2.1 h
      rw [Fin.append_right, Equiv.symm_apply_apply]

lemma mxpIota_apply (x : TanV 0 0 (mxN r + mxN r) 2) : mxpIota r x =
    (fun h => x.2.2.1 (Fin.castAdd _ (mxE r h)), fun h => x.2.2.1 (Fin.natAdd _ (mxE r h)),
      x.2.2.2 0, x.2.2.2 1) := rfl

lemma mxpIota_symm_apply (v : TXP r) : (mxpIota r).symm v = (0, 0,
    Fin.append (fun i => v.1 ((mxE r).symm i)) (fun i => v.2.1 ((mxE r).symm i)),
    ![v.2.2.1, v.2.2.2]) := rfl

variable (b : Fin r → ℂ)

lemma mxpM_mulVec0 (x : Fin (mxN r + mxN r) → ℂ) : (mxpM b).mulVec x 0 =
    ∑ h, theta I b h * x (Fin.natAdd _ (mxE r h)) := by
  simp only [Matrix.mulVec, dotProduct, mxpM, Matrix.cons_val_zero, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, zero_mul, Finset.sum_const_zero, zero_add]
  rw [sum_mxE]
  simp

lemma mxpM_mulVec1 (x : Fin (mxN r + mxN r) → ℂ) : (mxpM b).mulVec x 1 =
    ∑ h, theta I b h * x (Fin.castAdd _ (mxE r h)) := by
  simp only [Matrix.mulVec, dotProduct, mxpM, Matrix.cons_val_one, Matrix.cons_val_zero,
    Fin.sum_univ_add, Fin.append_left, Fin.append_right, zero_mul, Finset.sum_const_zero, add_zero]
  rw [sum_mxE]
  simp

lemma psiP1_apply' (v : TXP r) : psiP1 b v = ∑ h, theta I b h * v.1 h + v.2.2.1 := rfl

lemma psiP2_apply' (v : TXP r) : psiP2 b v = ∑ h, theta I b h * v.2.1 h + v.2.2.2 := rfl

lemma mxpM_alg (hb : IsAdaptedFieldBasis I b) : AlgMat (mxpM b) := by
  intro i j
  fin_cases i
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [mxpM, Fin.zero_eta, Matrix.cons_val_zero, Fin.append_left]
      exact isAlgebraic_zero
    · simp only [mxpM, Fin.zero_eta, Matrix.cons_val_zero, Fin.append_right]
      exact theta_alg hb.alg _
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [mxpM, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.append_left]
      exact theta_alg hb.alg _
    · simp only [mxpM, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.append_right]
      exact isAlgebraic_zero

end LSG.W88.V5d
