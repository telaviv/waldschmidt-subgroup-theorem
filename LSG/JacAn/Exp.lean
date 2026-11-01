/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Germ

/-!
# a4, step 2: the global exponential `E : ℂ² → P⁸` by doubling the germ

With `F = germ` (chart `X₄ = 1`, `F 0 = e₄`), let `expLift k z = dupᵏ(F(z / 2ᵏ))`.

* `germ_good`: on a ball `ball 0 ε`, `F` is an analytic chart-4 flow solution on the model, `dup (F v)` has nonzero
  `X₄`, and `normalize 4 (dup (F v)) = F (2v)` (from `eventually_germ_flow`, `germ_dup` and analyticity).
* `expLift_succ`: `expLift (k+1) z = μ • expLift k z` with `μ ≠ 0` whenever `z / 2^{k+1} ∈ ball 0 ε`.
* `expLift_ne_zero`: the lifts never vanish (by (P2) `dup_ne_zero`).
* **`expP`**: the global exponential as a map to the projectivisation `ℙ(ℂ⁹)`; **`expP_eq`**: `expP z` is the class of
  `expLift k z` for every `k` with `z / 2ᵏ ∈ ball 0 ε` (independence of `k`);
  **`analyticAt_expLift`**: the local lifts are analytic, so `expP` is a projective-analytic map.
-/

noncomputable section

open Polynomial Metric Set Filter Topology
open scoped LinearAlgebra.Projectivization

namespace LSG.JacAn

variable (A : A1Facts) {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2)

include hp hx in
lemma eventually_analyticAt_psiJ :
    ∀ᶠ z in 𝓝 (abel2 B₁ B₂ p), AnalyticAt ℂ (psiJ hp hx) z := by
  filter_upwards [eventually_analyticAt_localExp hp hx] with z hz
  rw [analyticAt_pi_iff] at hz ⊢
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  intro i
  fin_cases i <;> simp only [psiJ, grantJ] <;> simp <;> fun_prop

include hp hx in
lemma eventually_analyticAt_germ (hP₀ : A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 ≠ 0) :
    ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), AnalyticAt ℂ (germ A hp hx) w := by
  set Y := A.negP (baseP hp hx)
  set V : (Fin 2 → ℂ) → P9 := fun w => psiJ hp hx (abel2 B₁ B₂ p + w)
  have ht : Tendsto (fun w : Fin 2 → ℂ => abel2 B₁ B₂ p + w) (𝓝 0) (𝓝 (abel2 B₁ B₂ p)) := by
    have hc : Continuous (fun w : Fin 2 → ℂ => abel2 B₁ B₂ p + w) := continuous_const.add continuous_id
    simpa using hc.tendsto 0
  have hVan : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), AnalyticAt ℂ V w := by
    filter_upwards [ht.eventually (eventually_analyticAt_psiJ hp hx)] with w hw
    exact hw.comp (analyticAt_const.add analyticAt_id)
  have hZan : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), AnalyticAt ℂ (fun w => A.law0 (V w) Y) w := by
    filter_upwards [hVan] with w hw
    have hpr : AnalyticAt ℂ (fun w => (V w, Y)) w := hw.prod analyticAt_const
    exact AnalyticAt.comp (g := fun XY : P9 × P9 => A.law0 XY.1 XY.2) (f := fun w => (V w, Y))
      (A.law0_analytic _ (mem_univ _)) hpr
  have hVc : ContinuousAt V 0 := hVan.self_of_nhds.continuousAt
  have hne : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), A.law0 (V w) Y 4 ≠ 0 := by
    have hc : ContinuousAt (fun w => A.law0 (V w) Y 4) 0 :=
      (continuous_apply 4).continuousAt.comp hZan.self_of_nhds.continuousAt
    exact hc.eventually_ne (by simpa [V, baseP] using hP₀)
  filter_upwards [hZan, hne] with w hw hw4
  have h4 : AnalyticAt ℂ (fun w => A.law0 (V w) Y 4) w := (analyticAt_pi_iff.mp hw) 4
  exact (h4.inv hw4).smul hw

include hp hx in
/-- **The germ data** on a ball. -/
theorem germ_good (hP₀ : A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 ≠ 0) :
    ∃ ε > 0, ∀ v ∈ ball (0 : Fin 2 → ℂ) ε,
      IsFlowSol A.W4 1 4 (germ A hp hx) v ∧ A.OnQ (germ A hp hx v) ∧ AnalyticAt ℂ (germ A hp hx) v ∧
        A.dup (germ A hp hx v) 4 ≠ 0 ∧
        normalize 4 (A.dup (germ A hp hx v)) = germ A hp hx ((2 : ℂ) • v) := by
  obtain ⟨ε₁, hε₁, hdup⟩ := germ_dup A hp hx hP₀
  have hF := (eventually_germ_flow A hp hx hP₀).and (eventually_analyticAt_germ A hp hx hP₀)
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.eventually_nhds_iff_ball.mp hF
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun v hv => ?_⟩
  have hv₁ : v ∈ ball (0 : Fin 2 → ℂ) ε₁ := ball_subset_ball (min_le_left _ _) hv
  have hv₂ : v ∈ ball (0 : Fin 2 → ℂ) ε₂ := ball_subset_ball (min_le_right _ _) hv
  obtain ⟨⟨hflow, hQ⟩, han⟩ := hball v hv₂
  exact ⟨hflow, hQ, han, (hdup v hv₁).1, (hdup v hv₁).2⟩

/-! ## The lifts `dupᵏ(F(z/2ᵏ))` -/

/-- `dupᵏ` is homogeneous of degree `4ᵏ`. -/
lemma A1Facts.dup_iter_smul (k : ℕ) (a : ℂ) (X : P9) : A.dup^[k] (a • X) = a ^ (4 ^ k) • A.dup^[k] X := by
  induction k generalizing a X with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, A.dup_smul, ih, ← pow_mul, pow_succ 4 k,
      mul_comm]

lemma A1Facts.dup_iter_onQ (k : ℕ) {X : P9} (h : A.OnQ X) : A.OnQ (A.dup^[k] X) := by
  induction k generalizing X with
  | zero => simpa
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (A.dup_onQ _ h)

lemma A1Facts.dup_iter_ne_zero (k : ℕ) {X : P9} (h : A.OnQ X) (h0 : X ≠ 0) : A.dup^[k] X ≠ 0 := by
  induction k generalizing X with
  | zero => simpa
  | succ k ih =>
    rw [Function.iterate_succ_apply]; exact ih (A.dup_onQ _ h) (A.dup_ne_zero _ h h0)

lemma A1Facts.analyticAt_dup_iter (k : ℕ) {g : (Fin 2 → ℂ) → P9} {z : Fin 2 → ℂ}
    (hg : AnalyticAt ℂ g z) : AnalyticAt ℂ (fun z => A.dup^[k] (g z)) z := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact (A.dup_analytic _ (mem_univ _)).comp ih

/-- The `k`-th lift `dupᵏ(F(z/2ᵏ))`. -/
def expLift (k : ℕ) (z : Fin 2 → ℂ) : P9 := A.dup^[k] (germ A hp hx (((2 : ℂ) ^ k)⁻¹ • z))

variable {A hp hx}

/-- The germ radius (from `germ_good`). -/
structure GermRad (A : A1Facts) (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2) where
  ε : ℝ
  pos : 0 < ε
  good : ∀ v ∈ ball (0 : Fin 2 → ℂ) ε,
      IsFlowSol A.W4 1 4 (germ A hp hx) v ∧ A.OnQ (germ A hp hx v) ∧ AnalyticAt ℂ (germ A hp hx) v ∧
        A.dup (germ A hp hx v) 4 ≠ 0 ∧
        normalize 4 (A.dup (germ A hp hx v)) = germ A hp hx ((2 : ℂ) • v)

include hp hx in
/-- A germ radius exists (under the base nondegeneracy `hP₀`). -/
theorem exists_germRad (hP₀ : A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 ≠ 0) :
    Nonempty (GermRad A hp hx) := by
  obtain ⟨ε, hε, h⟩ := germ_good A hp hx hP₀
  exact ⟨⟨ε, hε, h⟩⟩

variable (G : GermRad A hp hx)

lemma GermRad.mem_succ {k : ℕ} {z : Fin 2 → ℂ} (h : ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε) :
    ((2 : ℂ) ^ (k + 1))⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε := by
  rw [mem_ball_zero_iff] at h ⊢
  have : ((2 : ℂ) ^ (k + 1))⁻¹ • z = (2 : ℂ)⁻¹ • (((2 : ℂ) ^ k)⁻¹ • z) := by
    rw [smul_smul, pow_succ, mul_inv, mul_comm]
  rw [this, norm_smul]
  have h2 : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by simp
  rw [h2]; linarith [norm_nonneg (((2 : ℂ) ^ k)⁻¹ • z)]

/-- **Independence of `k`**: consecutive lifts differ by a nonzero scalar. -/
theorem expLift_succ {k : ℕ} {z : Fin 2 → ℂ}
    (h : ((2 : ℂ) ^ (k + 1))⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε) :
    ∃ μ : ℂ, μ ≠ 0 ∧ expLift A hp hx (k + 1) z = μ • expLift A hp hx k z := by
  set v := ((2 : ℂ) ^ (k + 1))⁻¹ • z
  obtain ⟨-, -, -, hd4, heq⟩ := G.good v h
  have h2v : (2 : ℂ) • v = ((2 : ℂ) ^ k)⁻¹ • z := by
    simp only [v, smul_smul, pow_succ, mul_inv]
    congr 1; field_simp
  set d := A.dup (germ A hp hx v) 4 with hd
  have hdup : A.dup (germ A hp hx v) = d • germ A hp hx ((2 : ℂ) • v) := by
    rw [← heq, normalize, smul_smul, ← hd, mul_inv_cancel₀ hd4, one_smul]
  refine ⟨d ^ (4 ^ k), pow_ne_zero _ hd4, ?_⟩
  simp only [expLift]
  rw [Function.iterate_succ_apply, hdup, A.dup_iter_smul, h2v]

/-- The lifts never vanish. -/
theorem expLift_ne_zero {k : ℕ} {z : Fin 2 → ℂ} (h : ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε) :
    expLift A hp hx k z ≠ 0 := by
  obtain ⟨hflow, hQ, -⟩ := G.good _ h
  refine A.dup_iter_ne_zero k hQ fun h0 => ?_
  have := congrFun h0 4
  rw [hflow.1] at this
  exact one_ne_zero this

lemma exists_mem_ball (z : Fin 2 → ℂ) : ∃ k : ℕ, ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖z‖ / G.ε) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_⟩
  rw [mem_ball_zero_iff, norm_smul, norm_inv, norm_pow]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, inv_mul_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ G.pos] at hk
  linarith

open scoped Classical in
/-- The least admissible `k` at `z`. -/
def kAt (z : Fin 2 → ℂ) : ℕ := Nat.find (exists_mem_ball G z)

open scoped Classical in
lemma kAt_spec (z : Fin 2 → ℂ) : ((2 : ℂ) ^ kAt G z)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε :=
  Nat.find_spec (exists_mem_ball G z)

lemma mem_ball_of_le {k k' : ℕ} {z : Fin 2 → ℂ} (h : ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε)
    (hk : k ≤ k') : ((2 : ℂ) ^ k')⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε := by
  induction hk with
  | refl => exact h
  | step _ ih => exact G.mem_succ ih

/-- **The global exponential**, as a map to the projectivisation of `ℂ⁹`. -/
def expP (z : Fin 2 → ℂ) : ℙ ℂ P9 :=
  Projectivization.mk ℂ (expLift A hp hx (kAt G z) z) (expLift_ne_zero G (kAt_spec G z))

open scoped Classical in
/-- **`expP z` is the class of every admissible lift.** -/
theorem expP_eq {k : ℕ} {z : Fin 2 → ℂ} (h : ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε) :
    expP G z = Projectivization.mk ℂ (expLift A hp hx k z) (expLift_ne_zero G h) := by
  have hk : kAt G z ≤ k := Nat.find_min' _ h
  unfold expP
  induction hk with
  | refl => rfl
  | @step m hm ih =>
    have hm' := mem_ball_of_le G (kAt_spec G z) hm
    rw [ih hm']
    obtain ⟨μ, hμ, hμe⟩ := expLift_succ G (G.mem_succ hm')
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨μ⁻¹, by rw [hμe, smul_smul, inv_mul_cancel₀ hμ, one_smul]⟩

/-- **The local lifts are analytic.** -/
theorem analyticAt_expLift {k : ℕ} {z : Fin 2 → ℂ}
    (h : ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε) : AnalyticAt ℂ (expLift A hp hx k) z := by
  obtain ⟨-, -, han, -⟩ := G.good _ h
  have hl : AnalyticAt ℂ (fun z : Fin 2 → ℂ => ((2 : ℂ) ^ k)⁻¹ • z) z := by fun_prop
  have hF : AnalyticAt ℂ (fun z => germ A hp hx (((2 : ℂ) ^ k)⁻¹ • z)) z := han.comp hl
  exact A.analyticAt_dup_iter k hF

end LSG.JacAn
