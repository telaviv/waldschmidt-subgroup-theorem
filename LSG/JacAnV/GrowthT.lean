/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.Fibre

/-!
# M2.2: order-2 growth of the fibre coordinates

* `pd_norm_le`: Cauchy's estimate for a partial derivative on the unit disc in the direction `e_j`;
* **`ThetaData.fibT_growth`**: `‖T_k(z, w)‖ ≤ (1 + ‖w‖) · exp(c (1 + ‖z‖)²)` (linear in `w`, order 2 in `z`), the
  input `MonoV`-style monomials need for Prop 2.1.
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

open LSG.JacAnV

/-- **Cauchy's estimate** for `∂_j f(z)` on the unit disc in the direction `e_j`. -/
lemma pd_norm_le {f : (Fin 2 → ℂ) → ℂ} (hf : Ent f) (j : Fin 2) (z : Fin 2 → ℂ) {M : ℝ}
    (hM : ∀ t : ℂ, ‖t‖ = 1 → ‖f (z + t • Pi.single j 1)‖ ≤ M) : ‖pd j f z‖ ≤ M := by
  set g : ℂ → ℂ := fun t => f (z + t • Pi.single j 1)
  have hl : ∀ t : ℂ, HasDerivAt (fun t : ℂ => z + t • (Pi.single j 1 : Fin 2 → ℂ)) (Pi.single j 1) t :=
    fun t => by simpa using ((hasDerivAt_id t).smul_const (Pi.single j 1 : Fin 2 → ℂ)).const_add z
  have hg : ∀ t, HasDerivAt g (fderiv ℂ f (z + t • Pi.single j 1) (Pi.single j 1)) t := fun t =>
    (hf _).differentiableAt.hasFDerivAt.comp_hasDerivAt t (hl t)
  have hgd : Differentiable ℂ g := fun t => (hg t).differentiableAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := 1) (C := M) one_pos
    hgd.diffContOnCl (fun t ht => hM t (by simpa using ht))
  rw [(hg 0).deriv, zero_smul, add_zero] at h
  simpa [pd] using h

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- **Order-2 growth of `T`.** -/
theorem ThetaData.fibT_growth : ∃ c : ℝ, 0 ≤ c ∧ ∀ (k : Fin 9) (z : Fin 2 → ℂ) (w : ℂ),
    ‖D.fibT k z w‖ ≤ (1 + ‖w‖) * Real.exp (c * (1 + ‖z‖) ^ 2) := by
  obtain ⟨a, C, hθ⟩ := D.thetaN_order2
  set a' := |a|
  set C' := |C|
  set L := ‖D.ellK‖
  have hθ' : ∀ y, ‖D.thetaN y‖ ≤ Real.exp (a' * (1 + ‖y‖) ^ 2 + C') := fun y =>
    (hθ y).trans (Real.exp_le_exp.mpr (by
      have h1 : a * ‖y‖ ^ 2 ≤ a' * (1 + ‖y‖) ^ 2 :=
        (le_abs_self a |> fun h => mul_le_mul h (by nlinarith [norm_nonneg y]) (sq_nonneg _) (abs_nonneg _))
      linarith [le_abs_self C]))
  refine ⟨4 * (a' + L + C'), by positivity, fun k z w => ?_⟩
  set E := Real.exp (a' * (2 + ‖z‖) ^ 2 + C')
  have hE0 : 0 < E := Real.exp_pos _
  have hθk : ‖D.thetaN z k‖ ≤ E := (norm_le_pi_norm (D.thetaN z) k).trans
    ((hθ' z).trans (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg z, abs_nonneg a])))
  have hpd : ‖pd 0 (cmpV D.thetaN k) z‖ ≤ E := by
    refine pd_norm_le (ent_cmp D.analyticAt_thetaN k) 0 z fun t ht => ?_
    have hn : ‖z + t • (Pi.single 0 1 : Fin 2 → ℂ)‖ ≤ ‖z‖ + 1 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, ht, one_mul]
      have : ‖(Pi.single 0 1 : Fin 2 → ℂ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
        fin_cases i <;> simp
      linarith
    have ha' : 0 ≤ a' := abs_nonneg a
    have h1 : 1 + ‖z + t • (Pi.single 0 1 : Fin 2 → ℂ)‖ ≤ 2 + ‖z‖ := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    exact (norm_le_pi_norm _ k).trans ((hθ' _).trans (Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left h2 ha'])))
  have hl : ‖D.ellK z‖ ≤ L * ‖z‖ := D.ellK.le_opNorm z
  have hT : ‖D.fibT k z w‖ ≤ E * (‖w‖ + L * ‖z‖ + 1) := by
    unfold ThetaData.fibT
    calc ‖D.thetaN z k * (w + D.ellK z) - 1 / 3 * pd 0 (cmpV D.thetaN k) z‖
        ≤ ‖D.thetaN z k‖ * (‖w‖ + ‖D.ellK z‖) + 1 / 3 * ‖pd 0 (cmpV D.thetaN k) z‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
          · rw [norm_mul]; norm_num
      _ ≤ E * (‖w‖ + L * ‖z‖) + 1 / 3 * E := by
          gcongr
      _ ≤ E * (‖w‖ + L * ‖z‖ + 1) := by nlinarith
  have hL0 : 0 ≤ L := norm_nonneg _
  have hz0 := norm_nonneg z
  have hw0 := norm_nonneg w
  have hlin : ‖w‖ + L * ‖z‖ + 1 ≤ (1 + ‖w‖) * Real.exp (L * (1 + ‖z‖) ^ 2) := by
    have h1 : 1 + L * (1 + ‖z‖) ^ 2 ≤ Real.exp (L * (1 + ‖z‖) ^ 2) := by
      linarith [Real.add_one_le_exp (L * (1 + ‖z‖) ^ 2)]
    have h2 : L * ‖z‖ ≤ L * (1 + ‖z‖) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hL0
    nlinarith [mul_nonneg hw0 (mul_nonneg hL0 (sq_nonneg (1 + ‖z‖)))]
  calc ‖D.fibT k z w‖ ≤ E * ((1 + ‖w‖) * Real.exp (L * (1 + ‖z‖) ^ 2)) :=
        hT.trans (mul_le_mul_of_nonneg_left hlin hE0.le)
    _ = (1 + ‖w‖) * Real.exp (a' * (2 + ‖z‖) ^ 2 + C' + L * (1 + ‖z‖) ^ 2) := by
        rw [Real.exp_add]; ring
    _ ≤ (1 + ‖w‖) * Real.exp ((a' + L + C') * (1 + ‖z‖) ^ 2 * 4) := by
        gcongr
        have ha' : 0 ≤ a' := abs_nonneg a
        have hC' : 0 ≤ C' := abs_nonneg C
        have hq : (2 + ‖z‖) ^ 2 ≤ 4 * (1 + ‖z‖) ^ 2 := by nlinarith
        have hq1 : 1 ≤ (1 + ‖z‖) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hq ha', mul_le_mul_of_nonneg_left hq1 hC',
          mul_nonneg hL0 (sq_nonneg (1 + ‖z‖))]
    _ = (1 + ‖w‖) * Real.exp ((4 * (a' + L + C')) * (1 + ‖z‖) ^ 2) := by congr 2; ring

end LSG.JacAn
