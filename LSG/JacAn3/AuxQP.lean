/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.Normalize

/-!
# A3.7: quasi-periodicity in the shape of the Tier-3 Prop 2.1 hypothesis (STAGE_A3 §3.1)

`prop21Gen_of_interp` (`LSG/AuxFun/Prop21Gen.lean`) asks, for periods `ω` of the block, for a common multiplier
`ψ_l(z + ω) = m ψ_l(z)` with `‖m‖ ≤ exp (b (‖z‖ + ‖ω‖)²)`, and for entire `ψ_l` with `Σ ‖ψ_l‖ ≤ e^U` on balls.
For `ψ_l` = monomials of degree `D` in the coordinates of `θ_N`:
* **`thetaN_monomial_qp`**: the multiplier is `facN^D`, with `b' = D b`;
* `thetaN_monomial_differentiable`, and the growth `‖θ_N z‖ ≤ exp (a ‖z‖² + C)` (`thetaN_order2`).
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- **Common multiplier for degree-`Dg` monomials in `θ_N`.** -/
theorem ThetaData.thetaN_monomial_qp {L Dg : ℕ} (σ : Fin L → Fin Dg → Fin 9) :
    ∃ b ≥ 0, ∀ c ∈ latt, ∀ z : Fin 2 → ℂ, ∃ m : ℂ, ‖m‖ ≤ Real.exp (b * (‖z‖ + ‖c‖) ^ 2) ∧
      ∀ l, (∏ i, D.thetaN (z + c) (σ l i)) = m * ∏ i, D.thetaN z (σ l i) := by
  obtain ⟨b, hb, hfac⟩ := D.facN_bound
  refine ⟨Dg * b, by positivity, fun c hc z => ⟨D.facN c z ^ Dg, ?_, fun l => ?_⟩⟩
  · rw [norm_pow]
    calc ‖D.facN c z‖ ^ Dg ≤ Real.exp (b * (‖z‖ + ‖c‖) ^ 2) ^ Dg :=
          pow_le_pow_left₀ (norm_nonneg _) (hfac c hc z) Dg
      _ = Real.exp (Dg * b * (‖z‖ + ‖c‖) ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf
  · rw [D.thetaN_add (isPer_of_mem_latt hc) z]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

theorem ThetaData.thetaN_monomial_differentiable {Dg : ℕ} (τ : Fin Dg → Fin 9) :
    Differentiable ℂ (fun z => ∏ i, D.thetaN z (τ i)) := fun z => by
  have := (Finset.analyticAt_prod Finset.univ fun i _ =>
    (analyticAt_pi_iff.mp (D.analyticAt_thetaN z)) (τ i)).differentiableAt
  convert this using 1
  ext x; simp [Finset.prod_apply]

end LSG.JacAn
