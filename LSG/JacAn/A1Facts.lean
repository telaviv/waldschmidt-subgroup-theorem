/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.FlowGrant

/-!
# The A1 → A2 interface for a4 (`A1Facts`), and the transport lemmas

`A1Facts` collects, as hypotheses, the algebraic facts about Grant's P⁸ model that a4 needs from A1 (STAGE_A2 §6,
route 1 of the coordinator's decision). Every field is a statement A1 certifies (or a definitional/glue fact about
A1's polynomial maps); a4 builds against this interface, and the fields are discharged when A1 delivers (instantiate
`law0 := LSG.Jac.lawPt 0`, `dup := LSG.Jac.dup`, `negP := LSG.Jac.negP`, `OnQ := LSG.Jac.OnQ`, …; the factor 32 in
`lawPt` is harmless since every identity is homogeneous).

* `derivAlong W j dF X = Σ_i W_j(X)_i · ∂_i F(X)`: the formal derivative `D_j` of a polynomial map along the field
  `W_j` (the `D_j` of STAGE_A1 §4.2), with `dF i` the formal partials.
* Fields (all on `V(Q)`): (E1) for (input, output) charts (0,4), (4,0), (4,4), (E2) in chart 4, the chart-4 fields `W4`, the pointwise
  facts (P), homogeneity, and the analyticity glue (`HasFDerivAt` of the polynomial maps is given by their formal
  partials).

Transport lemmas (proved here from the interface):
* `hasFDerivAt_normalize`: if `Z` is analytic and `Z_c D_jZ_l − Z_l D_jZ_c = κ W_{jl}(Z)` (projective flow equation),
  then the chart-`c` normalisation `Z / Z_c` solves `DV = κ W(V)`, for `W` homogeneous of degree 2.
* `A1Facts.law0_transport₄`: law 0 with a fixed second argument maps chart-0 solutions to chart-4 solutions (E1).
* `A1Facts.dup_transport₄`: `dup` maps chart-4 solutions to chart-4 solutions of speed 2 (E2).
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

/-- The `i`-th coordinate projection on `ℂ⁹`. -/
abbrev prj (i : Fin 9) : P9 →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 9 => ℂ) i

/-- The origin `e₄` of Grant's model. -/
def origin9 : P9 := Pi.single 4 1

/-- The formal derivative `D_j F (X) = Σ_i W_j(X)_i ∂_i F(X)` (`dF i` = formal `∂/∂X_i` of `F`). -/
def derivAlong (W : Fin 2 → P9 → P9) (j : Fin 2) (dF : Fin 9 → P9 → P9) (X : P9) : P9 :=
  ∑ i : Fin 9, W j X i • dF i X

/-- The 9 quadrics of the model (copy of A1's `LSG.Jac.quad`). -/
def quadA (X : P9) : Fin 9 → ℂ :=
  ![-X 0 * X 8 - X 1 * X 3 + X 2 ^ 2,
    X 0 * X 7 - 2 * X 1 * X 5 + 2 * X 2 * X 4,
    -2 * X 1 * X 6 + X 2 * X 5 + X 3 * X 4,
    -X 0 * X 4 - X 1 * X 7 - X 2 * X 6 + 2 * X 3 * X 5,
    X 0 * X 5 - X 2 * X 7 + X 3 * X 6,
    -X 0 * X 2 - 2 * X 1 * X 8 - 3 * X 3 ^ 2 - X 4 * X 6 + X 5 ^ 2,
    X 0 * X 3 - 4 * X 1 ^ 2 - 4 * X 2 * X 8 - X 4 * X 7 + X 5 * X 6,
    -X 0 ^ 2 + 8 * X 1 * X 2 - 2 * X 3 * X 8 - X 5 * X 7 + X 6 ^ 2,
    8 * X 0 * X 1 + 4 * X 2 * X 3 + 4 * X 4 * X 5 - X 7 ^ 2 + 4 * X 8 ^ 2]

/-- Mumford coordinates `(s₁, s₂, b₁, b₀)` of `(x₁, y₁) + (x₂, y₂)` (same as `mumfordPts` of `Follow.lean`). -/
def mumfordPts' (x₁ y₁ x₂ y₂ : ℂ) : Fin 4 → ℂ :=
  ![x₁ + x₂, x₁ * x₂, (y₁ - y₂) / (x₁ - x₂), (x₁ * y₂ - x₂ * y₁) / (x₁ - x₂)]

/-- **The algebraic facts a4 needs from A1** (STAGE_A2 §6). -/
structure A1Facts where
  /-- the model `V(Q)` (A1: `LSG.Jac.OnQ`) -/
  OnQ : P9 → Prop
  onQ_smul : ∀ (a : ℂ) (X : P9), OnQ X → OnQ (a • X)
  /-- law 0 (A1: `lawPt 0`, = 32·A^{(0)}) -/
  law0 : P9 → P9 → P9
  /-- duplication (A1: `dup = lawPt 4 x x`) -/
  dup : P9 → P9
  /-- `[−1]` (A1: `negP`) -/
  negP : P9 → P9
  /-- formal partials of law 0 in the first argument -/
  dlaw0 : Fin 9 → P9 → P9 → P9
  /-- formal partials of `dup` -/
  ddup : Fin 9 → P9 → P9
  /-- analyticity glue -/
  hasFDerivAt_law0 : ∀ X Y : P9,
    HasFDerivAt (fun X => law0 X Y) (∑ i : Fin 9, (prj i).smulRight (dlaw0 i X Y)) X
  hasFDerivAt_dup : ∀ X : P9, HasFDerivAt dup (∑ i : Fin 9, (prj i).smulRight (ddup i X)) X
  /-- the flow in the chart `X₄ = 1` (Wronskians with respect to `X₄`) -/
  W4 : Fin 2 → P9 → P9
  W4_contDiff : ∀ j, ContDiff ℝ 1 (W4 j)
  W4_analytic : ∀ j, AnalyticOnNhd ℂ (W4 j) Set.univ
  W4_smul : ∀ j (a : ℂ) (X : P9), W4 j (a • X) = a ^ 2 • W4 j X
  W4_four : ∀ j (X : P9), W4 j X 4 = 0
  /-- (E1), input chart 4 (`D = derivAlong W4`), output chart 0 -/
  E1_40 : ∀ X Y : P9, OnQ X → OnQ Y → ∀ (j : Fin 2) (l : Fin 9),
    law0 X Y 0 * derivAlong W4 j (fun i X => dlaw0 i X Y) X l -
      law0 X Y l * derivAlong W4 j (fun i X => dlaw0 i X Y) X 0 = X 4 * flowW j (law0 X Y) l
  /-- (E1), input chart 4, output chart 4 -/
  E1_44 : ∀ X Y : P9, OnQ X → OnQ Y → ∀ (j : Fin 2) (l : Fin 9),
    law0 X Y 4 * derivAlong W4 j (fun i X => dlaw0 i X Y) X l -
      law0 X Y l * derivAlong W4 j (fun i X => dlaw0 i X Y) X 4 = X 4 * W4 j (law0 X Y) l
  /-- (E1), input chart 0 (`D = derivAlong flowW`), output chart 4 -/
  E1_4 : ∀ X Y : P9, OnQ X → OnQ Y → ∀ (j : Fin 2) (l : Fin 9),
    law0 X Y 4 * derivAlong flowW j (fun i X => dlaw0 i X Y) X l -
      law0 X Y l * derivAlong flowW j (fun i X => dlaw0 i X Y) X 4 = X 0 * W4 j (law0 X Y) l
  /-- (E2), chart 4 -/
  E2_4 : ∀ X : P9, OnQ X → ∀ (j : Fin 2) (l : Fin 9),
    dup X 4 * derivAlong W4 j ddup X l - dup X l * derivAlong W4 j ddup X 4 = 2 * X 4 * W4 j (dup X) l
  /-- the model is preserved -/
  law0_onQ : ∀ X Y : P9, OnQ X → OnQ Y → OnQ (law0 X Y)
  dup_onQ : ∀ X : P9, OnQ X → OnQ (dup X)
  negP_onQ : ∀ X : P9, OnQ X → OnQ (negP X)
  origin_onQ : OnQ origin9
  /-- the Mumford chart lands in the model (A1: `grant_onQ`) -/
  grantJ_onQ : ∀ m : Fin 4 → ℂ, chartR1J m = 0 → chartR0J m = 0 → OnQ (grantJ m)
  /-- (P) `law0(X, −X) ∝ e₄` -/
  law0_neg : ∀ X : P9, OnQ X → ∀ k : Fin 9, k ≠ 4 → law0 X (negP X) k = 0
  /-- (P) `dup(e₄) = c e₄`, `c ≠ 0` -/
  dup_origin : ∃ c : ℂ, c ≠ 0 ∧ dup origin9 = c • origin9
  /-- `law0_origin` (A1, proved): `law0(X, e₄) = −8 X₀ X` -/
  law0_origin : ∀ X : P9, law0 X origin9 = (-8 * X 0) • X
  /-- analyticity glue (polynomial maps) -/
  law0_analytic : AnalyticOnNhd ℂ (fun XY : P9 × P9 => law0 XY.1 XY.2) Set.univ
  dup_analytic : AnalyticOnNhd ℂ dup Set.univ
  /-- `dup` is homogeneous of degree 4 -/
  dup_smul : ∀ (a : ℂ) (X : P9), dup (a • X) = a ^ 4 • dup X
  /-- (P2) `dup` has no base point on the model (completeness of law 4 on the diagonal) -/
  dup_ne_zero : ∀ X : P9, OnQ X → X ≠ 0 → dup X ≠ 0
  /-- (for the homomorphism step) law 0 is bihomogeneous of bidegree `(2, 2)` -/
  law0_smul_left : ∀ (a : ℂ) (X Y : P9), law0 (a • X) Y = a ^ 2 • law0 X Y
  law0_smul_right : ∀ (a : ℂ) (X Y : P9), law0 X (a • Y) = a ^ 2 • law0 X Y
  /-- (S2) symmetry of law 0 (`swapSign = ±1`) -/
  swapSign : ℂ
  swapSign_ne : swapSign ≠ 0
  law0_swap : ∀ X Y : P9, law0 Y X = swapSign • law0 X Y
  /-- (W4i) the flow is transversal at the origin: `DF(0)` composed with the projection to `(X₁, X₈)` is invertible
  (A1: `W4 0 e₄ 1 = −1/2`, `W4 1 e₄ 8 = 1`) -/
  W4_origin_indep : W4 0 origin9 1 * W4 1 origin9 8 - W4 0 origin9 8 * W4 1 origin9 1 ≠ 0
  /-- (P3) the special base `P₀ = (0, −1) + (α, 3)`, `α⁵ = 2`, is nondegenerate: `law0 P₀ (negP P₀)` has
  nonzero `X₄` (an evaluation in `ℚ(2^{1/5})`; one fifth root `α` of 2 suffices, e.g. the real one) -/
  special_hP₀ : ∃ α : ℂ, α ^ 5 = 2 ∧
    law0 (grantJ (mumfordPts' 0 (-1) α 3)) (negP (grantJ (mumfordPts' 0 (-1) α 3))) 4 ≠ 0
  /-- (W4rel) the Wronskian relation between the charts `X₀ = 1` and `X₄ = 1`, on the model -/
  W4rel : ∀ X : P9, OnQ X → ∀ (j : Fin 2) (l : Fin 9),
    X 4 * flowW j X l = X 0 * W4 j X l - X l * W4 j X 0
  -- Fields for A3 (STAGE_A3 §4; batch added 2026-10-31)
  /-- the model is closed (A1: `onQ_iff`, polynomial equations) -/
  onQ_closed : IsClosed {X : P9 | OnQ X}
  /-- `[−1]` explicitly (A1: `negP` is definitionally this) -/
  negP_eq : ∀ X : P9, negP X = ![X 0, X 1, X 2, X 3, -X 4, -X 5, -X 6, -X 7, X 8]
  /-- the 81 law coordinates `A_k^{(m)}` (A1: `A32 k m`), with law `m` = `fun k => lawK k m X Y` -/
  lawK : Fin 9 → Fin 9 → P9 → P9 → ℂ
  /-- law 0 is column 0 (A1: `lawPt 0 x y k = A32 k 0 x y`) -/
  law0_lawK : ∀ (X Y : P9) (k : Fin 9), law0 X Y k = lawK k 0 X Y
  /-- (S1) (A1: `law_S1`) -/
  lawK_S1 : ∀ (k m : Fin 9) (X Y : P9), lawK k m X (negP Y) = lawK m k X Y
  /-- (V2′) rank one on the model (A1: `rank_one`, `V2.lean`) -/
  rank_one : ∀ (k m : Fin 9) (X Y : P9), OnQ X → OnQ Y →
    lawK k m X Y * lawK 0 0 X Y = lawK k 0 X Y * lawK 0 m X Y
  /-- bihomogeneity of bidegree `(2, 2)` -/
  lawK_smul_left : ∀ (k m : Fin 9) (a : ℂ) (X Y : P9), lawK k m (a • X) Y = a ^ 2 * lawK k m X Y
  lawK_smul_right : ∀ (k m : Fin 9) (a : ℂ) (X Y : P9), lawK k m X (a • Y) = a ^ 2 * lawK k m X Y
  /-- analyticity glue (polynomials) -/
  lawK_analytic : ∀ k m : Fin 9, AnalyticOnNhd ℂ (fun XY : P9 × P9 => lawK k m XY.1 XY.2) Set.univ
  /-- `[−1]`-equivariance of the chart-4 flow on the model (sign forced by `W4rel`; A1: data check) -/
  W4_negP : ∀ (j : Fin 2) (X : P9), OnQ X → W4 j (negP X) = negP (W4 j X)
  -- Fields for the Taylor coefficients (STAGE_A3 §8; batch added 2026-10-31)
  /-- the model points satisfy the explicit quadrics (A1: `onQ_iff`) -/
  onQ_quad : ∀ X : P9, OnQ X → ∀ j, quadA X j = 0
  /-- `W4` as an explicit quadratic table `W4 j X l = Σ (W4num j l a b / W4den) X_a X_b`, `|W4num| ≤ W4H` -/
  W4num : Fin 2 → Fin 9 → Fin 9 → Fin 9 → ℤ
  W4den : ℕ
  W4den_pos : 0 < W4den
  W4H : ℕ
  W4num_bound : ∀ j l a b, |W4num j l a b| ≤ W4H
  W4_table : ∀ (j : Fin 2) (X : P9) (l : Fin 9),
    W4 j X l = ∑ a, ∑ b, ((W4num j l a b : ℂ) / W4den) * (X a * X b)
  /-- the chart `X₈ = 1`: Wronskian quadratics `W8` with respect to `X₈`, as an explicit table -/
  W8 : Fin 2 → P9 → P9
  W8num : Fin 2 → Fin 9 → Fin 9 → Fin 9 → ℤ
  W8den : ℕ
  W8den_pos : 0 < W8den
  W8H : ℕ
  W8num_bound : ∀ j l a b, |W8num j l a b| ≤ W8H
  W8_table : ∀ (j : Fin 2) (X : P9) (l : Fin 9),
    W8 j X l = ∑ a, ∑ b, ((W8num j l a b : ℂ) / W8den) * (X a * X b)
  /-- (W8rel) the Wronskian relation between the charts `X₀ = 1` and `X₈ = 1`, on the model -/
  W8rel : ∀ X : P9, OnQ X → ∀ (j : Fin 2) (l : Fin 9),
    X 8 * flowW j X l = X 0 * W8 j X l - X l * W8 j X 0
  W8_eight : ∀ (j : Fin 2) (X : P9), W8 j X 8 = 0

/-- `flowW` is homogeneous of degree 2. -/
lemma flowW_smul (j : Fin 2) (a : ℂ) (X : P9) : flowW j (a • X) = a ^ 2 • flowW j X := by
  funext i
  unfold flowW
  split_ifs <;> fin_cases i <;> simp <;> ring

/-- The chart-`c` normalisation `Z / Z_c`. -/
def normalize (c : Fin 9) (Z : P9) : P9 := (Z c)⁻¹ • Z

/-- **Normalisation lemma.** If `Z` has derivative `L` at `w`, `Z_c ≠ 0`, and the projective flow equation
`Z_c L(v)_l − Z_l L(v)_c = κ (v₀ W₀(Z)_l + v₁ W₁(Z)_l)` holds, then `Z / Z_c` has derivative
`flowCLM W κ (Z / Z_c)` at `w`, for `W` homogeneous of degree 2. -/
theorem hasFDerivAt_normalize (W : Fin 2 → P9 → P9) (hW : ∀ j (a : ℂ) X, W j (a • X) = a ^ 2 • W j X)
    (κ : ℂ) (c : Fin 9) {Z : (Fin 2 → ℂ) → P9} {L : (Fin 2 → ℂ) →L[ℂ] P9} {w : Fin 2 → ℂ}
    (hZ : HasFDerivAt Z L w) (hc : Z w c ≠ 0)
    (hE : ∀ v l, Z w c * L v l - Z w l * L v c = κ * (v 0 * W 0 (Z w) l + v 1 * W 1 (Z w) l)) :
    HasFDerivAt (fun w => normalize c (Z w)) (flowCLM W κ (normalize c (Z w))) w := by
  have hZc : HasFDerivAt (fun w => Z w c) ((prj c).comp L) w := (prj c).hasFDerivAt.comp w hZ
  have hinv := (hasDerivAt_inv hc).comp_hasFDerivAt w hZc
  have h := hinv.smul hZ
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  funext l
  have e := hE v l
  simp only [normalize, flowCLM_apply, hW, Function.comp, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [prj, ContinuousLinearMap.proj_apply]
  field_simp
  linear_combination e

lemma normalize_self (c : Fin 9) {Z : P9} (hc : Z c ≠ 0) : normalize c Z c = 1 := by
  simp [normalize, hc]

namespace A1Facts

variable (A : A1Facts)

/-- The derivative of `w ↦ law0 (V w) Y` along a flow solution `V`. -/
lemma hasFDerivAt_law0_comp {W : Fin 2 → P9 → P9} {V : (Fin 2 → ℂ) → P9} {w : Fin 2 → ℂ} (Y : P9)
    (hV : HasFDerivAt V (flowCLM W 1 (V w)) w) :
    ∃ L : (Fin 2 → ℂ) →L[ℂ] P9, HasFDerivAt (fun w => A.law0 (V w) Y) L w ∧
      ∀ v, L v = v 0 • derivAlong W 0 (fun i X => A.dlaw0 i X Y) (V w) +
        v 1 • derivAlong W 1 (fun i X => A.dlaw0 i X Y) (V w) := by
  refine ⟨_, (A.hasFDerivAt_law0 (V w) Y).comp w hV, fun v => ?_⟩
  simp only [ContinuousLinearMap.comp_apply, flowCLM_apply, derivAlong, sum_apply,
    ContinuousLinearMap.smulRight_apply, prj, ContinuousLinearMap.proj_apply, one_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_smul, smul_smul, smul_smul]

/-- **Transport by law 0, output chart 4** (E1). -/
theorem law0_transport₄ {V : (Fin 2 → ℂ) → P9} {w : Fin 2 → ℂ} {Y : P9}
    (hV : IsFlowSol flowW 1 0 V w) (hVQ : A.OnQ (V w)) (hY : A.OnQ Y) (hc : A.law0 (V w) Y 4 ≠ 0) :
    HasFDerivAt (fun w => normalize 4 (A.law0 (V w) Y))
      (flowCLM A.W4 1 (normalize 4 (A.law0 (V w) Y))) w := by
  obtain ⟨L, hL, hLv⟩ := A.hasFDerivAt_law0_comp Y hV.2
  refine hasFDerivAt_normalize A.W4 A.W4_smul 1 4 hL hc fun v l => ?_
  have e0 := A.E1_4 (V w) Y hVQ hY 0 l
  have e1 := A.E1_4 (V w) Y hVQ hY 1 l
  rw [hV.1] at e0 e1
  simp only [hLv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination v 0 * e0 + v 1 * e1

/-- **Transport by `dup`, chart 4** (E2): a chart-4 solution is mapped to a chart-4 solution of speed 2. -/
theorem dup_transport₄ {U : (Fin 2 → ℂ) → P9} {w : Fin 2 → ℂ}
    (hU : IsFlowSol A.W4 1 4 U w) (hUQ : A.OnQ (U w)) (hc : A.dup (U w) 4 ≠ 0) :
    HasFDerivAt (fun w => normalize 4 (A.dup (U w))) (flowCLM A.W4 2 (normalize 4 (A.dup (U w)))) w := by
  have hL := (A.hasFDerivAt_dup (U w)).comp w hU.2
  refine hasFDerivAt_normalize A.W4 A.W4_smul 2 4 hL hc fun v l => ?_
  have e0 := A.E2_4 (U w) hUQ 0 l
  have e1 := A.E2_4 (U w) hUQ 1 l
  rw [hU.1] at e0 e1
  have hexp : ∀ m, ((∑ i : Fin 9, (prj i).smulRight (A.ddup i (U w))).comp (flowCLM A.W4 1 (U w)) v) m =
      v 0 * derivAlong A.W4 0 A.ddup (U w) m + v 1 * derivAlong A.W4 1 A.ddup (U w) m := by
    intro m
    simp only [ContinuousLinearMap.comp_apply, flowCLM_apply, derivAlong, sum_apply,
      ContinuousLinearMap.smulRight_apply, prj, ContinuousLinearMap.proj_apply, one_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp l, hexp 4]
  linear_combination v 0 * e0 + v 1 * e1

end A1Facts

end LSG.JacAn
