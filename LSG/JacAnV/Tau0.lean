/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.Laws

/-!
# M2.2 (N3): `θ_N` is `[−1]`-symmetric with constant `−1`, and `τ₀ = 0`

* `ThetaData.negC`: `θ_N(−v) = c(v) · negP θ_N(v)` (from `neg_N`); `c` is entire, `|c|` is `latt`-periodic
  (`norm_facN`), so `c` is constant (Liouville), and `c(0) = −1` (`θ_N(0) ∥ e₄`, `negP e₄ = −e₄`);
* **`ThetaData.thetaN_neg`**: `θ_N(−v) = −negP θ_N(v)`; so `θ_{N,4}` is even (`thetaN_four_neg`);
* **`ThetaData.fibT_four_origin`**: `T₄(0, 0) = 0`, i.e. `τ₀ = T₄(0,0)/θ₄(0) = −⅓ ∂₀ log θ₄(0) = 0`
  (the identity's fibre coordinate is algebraic; M2.md N3, spike M2.1.7). No certificate is needed.
-/

noncomputable section

open Metric Set Filter Topology Bornology

namespace LSG.JacAn

open LSG.JacAnV

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

lemma negL_ne_zero {X : P9} (hX : X ≠ 0) : negL X ≠ 0 := by
  intro h
  apply hX
  funext i
  have := congrFun h i
  fin_cases i <;> simpa [negL] using this

/-- The `[−1]`-multiplier `c(v)` with `θ_N(−v) = c(v) • negL θ_N(v)`. -/
def ThetaData.negC (v : Fin 2 → ℂ) : ℂ :=
  D.thetaN (-v) (nzIdx (negL (D.thetaN v))) / negL (D.thetaN v) (nzIdx (negL (D.thetaN v)))

lemma ThetaData.par_negL (v : Fin 2 → ℂ) : Par (negL (D.thetaN v)) (D.thetaN (-v)) := by
  rw [negL_apply A]; exact D.neg_N v

lemma ThetaData.negC_spec_k (v : Fin 2 → ℂ) {k : Fin 9} (hk : negL (D.thetaN v) k ≠ 0) :
    D.negC v = D.thetaN (-v) k / negL (D.thetaN v) k := by
  have h1 := nzIdx_spec (negL_ne_zero (D.thetaN_ne_zero v))
  have hp := D.par_negL v
  unfold ThetaData.negC
  rw [div_eq_div_iff h1 hk]
  linear_combination hp k (nzIdx (negL (D.thetaN v)))

theorem ThetaData.negC_spec (v : Fin 2 → ℂ) : D.thetaN (-v) = D.negC v • negL (D.thetaN v) := by
  funext m
  have h1 := nzIdx_spec (negL_ne_zero (D.thetaN_ne_zero v))
  have hp := D.par_negL v
  simp only [Pi.smul_apply, smul_eq_mul, ThetaData.negC]
  field_simp
  linear_combination hp (nzIdx (negL (D.thetaN v))) m

lemma ThetaData.analyticAt_negC (v₀ : Fin 2 → ℂ) : AnalyticAt ℂ D.negC v₀ := by
  set k := nzIdx (negL (D.thetaN v₀))
  have hk := nzIdx_spec (negL_ne_zero (D.thetaN_ne_zero v₀))
  have hN : AnalyticAt ℂ (fun v => negL (D.thetaN v) k) v₀ :=
    (analyticAt_pi_iff.mp ((negL.analyticAt _).comp (D.analyticAt_thetaN v₀))) k
  have hM : AnalyticAt ℂ (fun v => D.thetaN (-v) k) v₀ :=
    (analyticAt_pi_iff.mp ((D.analyticAt_thetaN _).comp analyticAt_id.neg)) k
  refine (hM.div hN hk).congr ?_
  filter_upwards [hN.continuousAt.eventually_ne hk] with v hv
  exact (D.negC_spec_k v hv).symm

lemma ThetaData.norm_negC_add {ω : Fin 2 → ℂ} (hω : ω ∈ latt) (v : Fin 2 → ℂ) :
    ‖D.negC (v + ω)‖ = ‖D.negC v‖ := by
  have pω := isPer_of_mem_latt (G := G) hω
  have pnω := isPer_of_mem_latt (G := G) (neg_mem hω)
  have e1 := D.negC_spec (v + ω)
  rw [neg_add, D.thetaN_add pnω, D.negC_spec v, D.thetaN_add pω, map_smul, smul_smul, smul_smul] at e1
  have hne := negL_ne_zero (D.thetaN_ne_zero v)
  have e2 := smul_cancel_of_ne hne e1
  have hn1 : ‖D.facN (-ω) (-v)‖ = ‖D.facN ω v‖ := by
    rw [D.norm_facN (neg_mem hω), D.norm_facN hω, D.Lf_neg pω pnω]
    congr 1
    simp only [ContinuousLinearMap.neg_apply, map_neg, neg_neg]
  have hf : 0 < ‖D.facN ω v‖ := by
    rw [ThetaData.facN, norm_mul]
    exact mul_pos (norm_pos_iff.mpr (Complex.exp_ne_zero _)) (norm_pos_iff.mpr (D.fac_ne_zero pω v))
  have := congrArg norm e2
  rw [norm_mul, norm_mul, hn1, mul_comm] at this
  exact (mul_right_cancel₀ hf.ne' this).symm

/-- **`c` is constant** (Liouville). -/
theorem ThetaData.negC_const (v w : Fin 2 → ℂ) : D.negC v = D.negC w := by
  have hcont : Continuous D.negC := continuous_iff_continuousAt.mpr fun x => (D.analyticAt_negC x).continuousAt
  obtain ⟨M, hM⟩ := isCompact_fundDom.exists_bound_of_continuousOn hcont.continuousOn
  have hb : IsBounded (range D.negC) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨u, rfl⟩
    obtain ⟨f, hf, c, hc, rfl⟩ := exists_fund u
    rw [D.norm_negC_add hc]
    exact hM f hf
  have hdiff : Differentiable ℂ D.negC := fun x => (D.analyticAt_negC x).differentiableAt
  exact hdiff.apply_eq_apply_of_bounded hb v w

/-- **`θ_N(−v) = −negP θ_N(v)`.** -/
theorem ThetaData.thetaN_neg (v : Fin 2 → ℂ) : D.thetaN (-v) = -A.negP (D.thetaN v) := by
  obtain ⟨a, ha, h0⟩ := D.theta_zero
  have hθ0 : D.thetaN 0 = (Complex.exp (-D.lamN 0) * a) • origin9 := by
    rw [ThetaData.thetaN, h0, smul_smul]
  have hc0 : D.negC 0 = -1 := by
    have e := D.negC_spec 0
    have hn : negL origin9 = -origin9 := by ext i; fin_cases i <;> simp [negL, origin9]
    rw [neg_zero, hθ0, map_smul, smul_smul, hn] at e
    have e4 := congrFun e 4
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, origin9, Pi.single_eq_same] at e4
    have hμ : Complex.exp (-D.lamN 0) * a ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) ha
    have : (Complex.exp (-D.lamN 0) * a) * (1 + D.negC 0) = 0 := by linear_combination e4
    linear_combination (mul_eq_zero.mp this).resolve_left hμ
  rw [D.negC_spec v, D.negC_const v 0, hc0, neg_one_smul, negL_apply A]

theorem ThetaData.thetaN_four_neg (v : Fin 2 → ℂ) : D.thetaN (-v) 4 = D.thetaN v 4 := by
  rw [D.thetaN_neg, Pi.neg_apply, A.negP_eq]; simp

/-- **`∂₀ θ_{N,4}(0) = 0`.** -/
theorem ThetaData.pd_thetaN_four_zero (j : Fin 2) : pd j (cmpV D.thetaN 4) 0 = 0 := by
  have hf := ent_cmp D.analyticAt_thetaN 4
  have h := pd_comp_sub_left (f := cmpV D.thetaN 4) (ω := 0) (y := 0) ((hf (0 - 0)).differentiableAt) j
  have e : (fun y => cmpV D.thetaN 4 (0 - y)) = cmpV D.thetaN 4 := funext fun y => by
    simp only [cmpV, zero_sub, D.thetaN_four_neg]
  rw [e, sub_zero] at h
  linear_combination h / 2

/-- **`τ₀ = 0`**: the identity's fibre coordinate `T₄(0, 0)` vanishes. -/
theorem ThetaData.fibT_four_origin : D.fibT 4 0 0 = 0 := by
  unfold ThetaData.fibT
  rw [D.pd_thetaN_four_zero, map_zero]; ring

end LSG.JacAn
