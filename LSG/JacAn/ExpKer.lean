/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.ExpFollow

/-!
# a5: the kernel of `E` (discreteness, group property, periods from two paths) and translated surjectivity

* `germ_locInj`: the germ is locally injective at `0` (its derivative composed with `X ↦ (X₁, X₈)` is invertible,
  `W4_origin_indep`).
* **`expP_ker_small`**: `E c = E 0` and `c` small imply `c = 0`.
* **`expP_periodic_of_ker`**: if `E c = E 0` then `E (z + c) = E z` for all `z` (so `ker E` is a subgroup).
* **`expP_ker_discrete`**: `ker E` is discrete (uniformly: distinct kernel elements are `≥ r` apart).
* **`expP_periodic_of_two_paths`**: if two path translates end at the same affine divisor, `T a ∥ X`, `T b ∥ X`, then
  `E (z + (a − b)) = E z`. This is how the periods `z([ζᵉ]γ) = A_e(1) − A_{e+1}(1)` enter the kernel, given
  `follow_trans` along the two lifts (`period_eq_abelAlong`).
* **`surj_trans`**: every generic divisor `D` reachable from the base pair by a nondegenerate path is hit:
  `E c ∥ law0 (grantJ D) (negP P₀)` (i.e. `E c = D ⊖ P₀`) and `T c ∥ grantJ D`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology
open scoped LinearAlgebra.Projectivization

namespace LSG.JacAn

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  (G : GermRad A hp hx)

/-- The projection `X ↦ (X₁, X₈)`. -/
def pr18 : P9 →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.pi ![prj 1, prj 8]

/-- The derivative of `pr18 ∘ germ` at `0`. -/
def germDer (A : A1Facts) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi ![A.W4 0 origin9 1 • pr0 + A.W4 1 origin9 1 • pr1,
    A.W4 0 origin9 8 • pr0 + A.W4 1 origin9 8 • pr1]

/-- The determinant (`≠ 0` by `W4_origin_indep`). -/
def germDet (A : A1Facts) : ℂ :=
  A.W4 0 origin9 1 * A.W4 1 origin9 8 - A.W4 0 origin9 8 * A.W4 1 origin9 1

/-- Its explicit inverse. -/
def germDerInv (A : A1Facts) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi
    ![(A.W4 1 origin9 8 / germDet A) • pr0 -
        (A.W4 1 origin9 1 / germDet A) • pr1,
      (A.W4 0 origin9 1 / germDet A) • pr1 -
        (A.W4 0 origin9 8 / germDet A) • pr0]

/-- The derivative is invertible. -/
def germDerEquiv (A : A1Facts) : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse (germDer A) (germDerInv A)
    (by
      have hd : germDet A ≠ 0 := A.W4_origin_indep
      intro v; funext i; fin_cases i <;> simp [germDer, germDerInv] <;> field_simp <;> unfold germDet <;> ring)
    (by
      have hd : germDet A ≠ 0 := A.W4_origin_indep
      intro v; funext i; fin_cases i <;> simp [germDer, germDerInv] <;> field_simp <;> unfold germDet <;> ring)

include G in
/-- **The germ is locally injective at `0`** (modulo `pr18`). -/
theorem germ_locInj : ∃ r > 0, ∀ c ∈ ball (0 : Fin 2 → ℂ) r,
    pr18 (germ A hp hx c) = pr18 (germ A hp hx 0) → c = 0 := by
  obtain ⟨hflow, -, han, -⟩ := G.good 0 (mem_ball_self G.pos)
  have hg : HasFDerivAt (fun c => pr18 (germ A hp hx c)) (germDer A) 0 := by
    have h := pr18.hasFDerivAt.comp 0 hflow.2
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    funext i
    rw [G.germ_zero]
    fin_cases i <;> simp [pr18, germDer, flowCLM_apply, prj] <;> ring
  have hgan : AnalyticAt ℂ (fun c => pr18 (germ A hp hx c)) 0 := pr18.analyticAt _ |>.comp han
  have hs : HasStrictFDerivAt (fun c => pr18 (germ A hp hx c))
      ((germDerEquiv A : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ)) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) 0 :=
    hasStrictFDerivAt_of_analyticAt hgan hg
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hs.eventually_left_inverse
  refine ⟨r, hr, fun c hc he => ?_⟩
  have h1 := hball c hc
  have h0 := hball 0 (mem_ball_self hr)
  rw [he] at h1
  exact h1.symm.trans h0

lemma expLift_zero_eq (z : Fin 2 → ℂ) : expLift A hp hx 0 z = germ A hp hx z := by simp [expLift]

lemma pr18_origin : pr18 origin9 = 0 := by
  funext i; fin_cases i <;> simp [pr18, origin9, prj]

include G in
/-- **Small kernel elements vanish.** -/
theorem expP_ker_small : ∃ r > 0, ∀ c ∈ ball (0 : Fin 2 → ℂ) r, expP G c = expP G 0 → c = 0 := by
  obtain ⟨r, hr, hinj⟩ := germ_locInj G
  refine ⟨min r G.ε, lt_min hr G.pos, fun c hc he => ?_⟩
  have hcε : c ∈ ball (0 : Fin 2 → ℂ) G.ε := ball_subset_ball (min_le_right _ _) hc
  have hm : ∀ z ∈ ball (0 : Fin 2 → ℂ) G.ε, ((2 : ℂ) ^ 0)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε := by simp
  rw [expP_eq G (hm c hcε), expP_eq G (hm 0 (mem_ball_self G.pos)), Projectivization.mk_eq_mk_iff'] at he
  obtain ⟨a, ha⟩ := he
  rw [expLift_zero_eq, expLift_zero_eq, G.germ_zero] at ha
  refine hinj c (ball_subset_ball (min_le_left _ _) hc) ?_
  rw [← ha, G.germ_zero, map_smul, pr18_origin, smul_zero]

/-- Finitely many points lie in a common admissible ball. -/
lemma exists_k_mem (z : Fin 2 → ℂ) (R : ℝ) (hR : 0 < R) :
    ∃ k : ℕ, ∀ k' ≥ k, ‖z‖ < 2 ^ k' * R := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖z‖ / R) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, fun k' hk' => ?_⟩
  have : (2 : ℝ) ^ k ≤ 2 ^ k' := pow_le_pow_right₀ (by norm_num) hk'
  rw [div_lt_iff₀ hR] at hk
  nlinarith [norm_nonneg z]

lemma exists_k_mem3 (z₁ z₂ z₃ : Fin 2 → ℂ) : ∃ k : ℕ, z₁ ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) ∧
    z₂ ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) ∧ z₃ ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) := by
  obtain ⟨k₁, h₁⟩ := exists_k_mem z₁ G.ε G.pos
  obtain ⟨k₂, h₂⟩ := exists_k_mem z₂ G.ε G.pos
  obtain ⟨k₃, h₃⟩ := exists_k_mem z₃ G.ε G.pos
  refine ⟨max k₁ (max k₂ k₃), ?_, ?_, ?_⟩ <;> rw [mem_ball_zero_iff]
  · exact h₁ _ (le_max_left _ _)
  · exact h₂ _ ((le_max_left _ _).trans (le_max_right _ _))
  · exact h₃ _ ((le_max_right _ _).trans (le_max_right _ _))

/-- **Kernel elements are periods**: `E c = E 0` implies `E (z + c) = E z`. -/
theorem expP_periodic_of_ker {c : Fin 2 → ℂ} (hc : expP G c = expP G 0) (z : Fin 2 → ℂ) :
    expP G (z + c) = expP G z := by
  obtain ⟨k, hcU, hzU, hzcU⟩ := exists_k_mem3 G c z (z + c)
  refine expP_periodic G k hcU ?_ hzU hzcU
  have h0U : (0 : Fin 2 → ℂ) ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε) :=
    mem_ball_self (by have := G.pos; positivity)
  rw [expP_eq G (G.mem_small hcU), expP_eq G (G.mem_small h0U), Projectivization.mk_eq_mk_iff'] at hc
  obtain ⟨a, ha⟩ := hc
  obtain ⟨μ, hμ, he⟩ := expLift_zero G k
  have hne := expLift_ne_zero G (G.mem_small hcU)
  have hcμ : expLift A hp hx k c = (a * μ) • origin9 := by rw [← ha, he, smul_smul]
  have haμ : a * μ ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hcμ; exact hne hcμ
  refine ⟨(a * μ) ^ 2 * (A.swapSign * (-8 * baseP hp hx 0)), ?_, ?_⟩
  · rw [baseP_zero]; exact mul_ne_zero (pow_ne_zero 2 haμ) (mul_ne_zero A.swapSign_ne (by norm_num))
  · rw [transP, hcμ, A.law0_smul_left, A.law0_origin_left, smul_smul]

/-- **The kernel is discrete.** -/
theorem expP_ker_discrete : ∃ r > 0, ∀ c c' : Fin 2 → ℂ, expP G c = expP G 0 → expP G c' = expP G 0 →
    dist c c' < r → c = c' := by
  obtain ⟨r, hr, h⟩ := expP_ker_small G
  refine ⟨r, hr, fun c c' hc hc' hd => ?_⟩
  have h1 : expP G (c - c') = expP G 0 := by
    have := expP_periodic_of_ker G hc' (c - c')
    rw [sub_add_cancel] at this
    rw [← this, hc]
  have := h (c - c') (by rw [mem_ball_zero_iff, ← dist_eq_norm]; exact hd) h1
  exact sub_eq_zero.mp this

/-- `Par` of two nonzero lifts gives equal classes in `ℙ(ℂ⁹)`. -/
lemma mk_eq_of_par {X Y : P9} (hX : X ≠ 0) (hY : Y ≠ 0) (h : Par X Y) :
    Projectivization.mk ℂ X hX = Projectivization.mk ℂ Y hY := by
  obtain ⟨m, hm⟩ : ∃ m, X m ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hX (funext hcon)
  have he := h.eq_smul hm
  set σ := Y m / X m
  have hσ : σ ≠ 0 := by intro h0; rw [h0, zero_smul] at he; exact hY he
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨σ⁻¹, by rw [he, smul_smul, inv_mul_cancel₀ hσ, one_smul]⟩

/-- **Periods from two paths with a common end**: if `T a ∥ X` and `T b ∥ X` for an affine `X` (`X₀ = 1`), with
`T a, T b ≠ 0` and `law0 X (negP P₀)` not zero, then `E (z + (a − b)) = E z` whenever `z, z + (a − b) ∈ U`. -/
theorem expP_periodic_of_two_paths (k : ℕ) {a b : Fin 2 → ℂ} {X : P9}
    (haU : a ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) (hbU : b ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hX0 : X 0 = 1) (hXn : A.law0 X (A.negP (baseP hp hx)) ≠ 0)
    (hTa : transP (A := A) (hp := hp) (hx := hx) k a ≠ 0) (hTb : transP (A := A) (hp := hp) (hx := hx) k b ≠ 0)
    (hpa : Par (transP (A := A) (hp := hp) (hx := hx) k a) X)
    (hpb : Par (transP (A := A) (hp := hp) (hx := hx) k b) X)
    {z : Fin 2 → ℂ} (hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hzc : z + (a - b) ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    expP G (z + (a - b)) = expP G z := by
  set R := 2 ^ k * G.ε
  set c := a - b
  have hTan : ∀ w ∈ ball (0 : Fin 2 → ℂ) R, AnalyticAt ℂ (transP (A := A) (hp := hp) (hx := hx) k) w :=
    fun w hw => analyticOn_transP G k w hw
  have ha0 : transP (A := A) (hp := hp) (hx := hx) k a 0 ≠ 0 := hpa.zero_ne hX0 hTa
  have hb0 : transP (A := A) (hp := hp) (hx := hx) k b 0 ≠ 0 := hpb.zero_ne hX0 hTb
  obtain ⟨m, hm⟩ : ∃ m, A.law0 X (A.negP (baseP hp hx)) m ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hXn (funext hcon)
  -- the local comparison near `b`
  have hmemD : ∀ u, u + c ∈ ball (0 : Fin 2 → ℂ) R ↔ u ∈ ball (-c) R := fun u => by
    rw [mem_ball_zero_iff, mem_ball, dist_eq_norm, sub_neg_eq_add]
  set D : Set (Fin 2 → ℂ) := ball 0 R ∩ ball (-c) R
  have hbD : b ∈ D := ⟨hbU, (hmemD b).mp (by simpa [c] using haU)⟩
  have key : ∀ᶠ u in 𝓝 b, Par (expLift A hp hx k (u + c)) (expLift A hp hx k u) := by
    -- continuity facts near `w = 0`
    have hcU : ∀ y ∈ ({a, b} : Set (Fin 2 → ℂ)), ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ),
        w + y ∈ ball (0 : Fin 2 → ℂ) R ∧ transP (A := A) (hp := hp) (hx := hx) k (w + y) 0 ≠ 0 := by
      intro y hy
      have hyU : y ∈ ball (0 : Fin 2 → ℂ) R := by rcases hy with rfl | rfl <;> assumption
      have hy0 : transP (A := A) (hp := hp) (hx := hx) k y 0 ≠ 0 := by
        rcases hy with rfl | rfl <;> assumption
      have hc1 : ContinuousAt (fun w : Fin 2 → ℂ => w + y) 0 := (continuous_id.add continuous_const).continuousAt
      have hb1 : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), w + y ∈ ball (0 : Fin 2 → ℂ) R :=
        hc1.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hyU)
      have hb2 : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), transP (A := A) (hp := hp) (hx := hx) k (w + y) 0 ≠ 0 := by
        have h1 : ContinuousAt (transP (A := A) (hp := hp) (hx := hx) k) (0 + y) := by
          rw [zero_add]; exact (hTan y hyU).continuousAt
        exact ((continuous_apply 0).continuousAt.comp (h1.comp_of_eq hc1 rfl)).eventually_ne (by simpa using hy0)
      exact hb1.and hb2
    have hpiv : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ),
        A.law0 (transP (A := A) (hp := hp) (hx := hx) k (w + b)) (A.negP (baseP hp hx)) m ≠ 0 := by
      have h1 : ContinuousAt (fun u => A.law0 (transP (A := A) (hp := hp) (hx := hx) k u)
          (A.negP (baseP hp hx)) m) (0 + b) := by
        rw [zero_add]
        exact (continuous_apply m).continuousAt.comp (analyticAt_law0_comp (hTan b hbU)).continuousAt
      have hc1 : ContinuousAt (fun w : Fin 2 → ℂ => w + b) 0 := (continuous_id.add continuous_const).continuousAt
      refine (h1.comp_of_eq hc1 rfl).eventually_ne ?_
      show A.law0 (transP (A := A) (hp := hp) (hx := hx) k (0 + b)) (A.negP (baseP hp hx)) m ≠ 0
      rw [zero_add, hpb.symm.eq_smul (by rw [hX0]; exact one_ne_zero), hX0, div_one, A.law0_smul_left]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero (pow_ne_zero 2 hb0) hm
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (((hcU a (by simp)).and (hcU b (by simp))).and hpiv)
    -- both normalised translates are chart-0 flow solutions with the same value at `0`
    have hsol : ∀ w ∈ ball (0 : Fin 2 → ℂ) ρ,
        normalize 0 (transP (A := A) (hp := hp) (hx := hx) k (w + a)) =
          normalize 0 (transP (A := A) (hp := hp) (hx := hx) k (w + b)) := by
      have hflow : ∀ y ∈ ({a, b} : Set (Fin 2 → ℂ)), ∀ w ∈ ball (0 : Fin 2 → ℂ) ρ,
          w + y ∈ ball (0 : Fin 2 → ℂ) R ∧ transP (A := A) (hp := hp) (hx := hx) k (w + y) 0 ≠ 0 →
          HasFDerivAt (fun w => normalize 0 (transP (A := A) (hp := hp) (hx := hx) k (w + y)))
            (flowCLM flowW 1 (normalize 0 (transP (A := A) (hp := hp) (hx := hx) k (w + y)))) w := by
        intro y _ w _ ⟨hwU, hw0⟩
        have hPF := (PF0_transP G k _ hwU).comp_add (hTan _ hwU).differentiableAt
        have hd : DifferentiableAt ℂ (fun w => transP (A := A) (hp := hp) (hx := hx) k (w + y)) w :=
          ((hTan _ hwU).comp_of_eq (analyticAt_id.add analyticAt_const) rfl).differentiableAt
        exact hPF.hasFDerivAt_normalize flowW_smul hd hw0
      refine flow_unique flowW contDiff_flowW 1
        (fun w hw => hflow a (by simp) w hw (hball w hw).1.1)
        (fun w hw => hflow b (by simp) w hw (hball w hw).1.2) ?_
      rw [zero_add, zero_add, hpa.normalize_eq hX0 ha0, hpb.normalize_eq hX0 hb0]
    have hc1 : ContinuousAt (fun u : Fin 2 → ℂ => u - b) b := (continuous_id.sub continuous_const).continuousAt
    have hnb : ball (0 : Fin 2 → ℂ) ρ ∈ 𝓝 ((fun u : Fin 2 → ℂ => u - b) b) := by
      simpa using ball_mem_nhds (0 : Fin 2 → ℂ) hρ
    filter_upwards [hc1.preimage_mem_nhds hnb] with u hu
    set w := u - b
    have hw : w ∈ ball (0 : Fin 2 → ℂ) ρ := hu
    obtain ⟨⟨⟨hwaU, hwa0⟩, ⟨hwbU, hwb0⟩⟩, hwm⟩ := hball w hw
    have hub : w + b = u := sub_add_cancel u b
    have hua : w + a = u + c := by simp only [w, c]; abel
    have hs := hsol w hw
    rw [hua, hub] at hs
    rw [hua] at hwaU hwa0
    rw [hub] at hwbU hwb0 hwm
    -- `T (u + c) = ν • T u`
    have hpar : Par (transP (A := A) (hp := hp) (hx := hx) k (u + c))
        (transP (A := A) (hp := hp) (hx := hx) k u) := by
      have h1 := par_normalize 0 (transP (A := A) (hp := hp) (hx := hx) k (u + c))
      have h2 := par_normalize 0 (transP (A := A) (hp := hp) (hx := hx) k u)
      rw [hs] at h1
      exact h1.symm.trans h2 (m := 0) (by rw [normalize_self 0 hwb0]; exact one_ne_zero)
    set ν := transP (A := A) (hp := hp) (hx := hx) k (u + c) 0 / transP (A := A) (hp := hp) (hx := hx) k u 0
    have hν : ν ≠ 0 := div_ne_zero hwa0 hwb0
    have hTν := hpar.symm.eq_smul hwb0
    have hi1 := inv_trans G k hwaU
    have hi2 := inv_trans G k hwbU
    rw [hTν, A.law0_smul_left] at hi1
    exact (hi1.of_smul_right (pow_ne_zero 2 hν)).trans hi2.symm hwm
  have hpar := par_of_eventually ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    (F₁ := fun u => expLift A hp hx k (u + c)) (F₂ := expLift A hp hx k)
    (fun u hu => AnalyticAt.comp (g := expLift A hp hx k) (f := fun u => u + c)
      (analyticOn_expLift G k (u + c) ((hmemD u).mpr hu.2)) (analyticAt_id.add analyticAt_const))
    (fun u hu => analyticOn_expLift G k u hu.1) hbD key z ⟨hz, (hmemD z).mp hzc⟩
  rw [expP_eq G (G.mem_small hzc), expP_eq G (G.mem_small hz)]
  exact mk_eq_of_par _ _ hpar

/-- **Translated surjectivity**: a generic divisor `D(1)` reachable from the base pair by a nondegenerate path is
`E(c) ⊖ P₀`-represented: `T c ∥ grantJ D(1)` and `Ẽ c ∥ law0 (grantJ D(1)) (negP P₀)`, with `c = A₁ 1 + A₂ 1`. -/
theorem surj_trans (k : ℕ) {u₁ Y₁ u₂ Y₂ : ℝ → ℂ} {A₁ A₂ : ℝ → (Fin 2 → ℂ)}
    (hA₁ : IsAbelAlong f₅ 2 u₁ Y₁ A₁) (hA₂ : IsAbelAlong f₅ 2 u₂ Y₂ A₂) (hA₁0 : A₁ 0 = 0) (hA₂0 : A₂ 0 = 0)
    (hu₁ : ContinuousOn u₁ (Icc 0 1)) (hu₂ : ContinuousOn u₂ (Icc 0 1))
    (hY₁ : ContinuousOn Y₁ (Icc 0 1)) (hY₂ : ContinuousOn Y₂ (Icc 0 1))
    (hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u₁ t ≠ u₂ t)
    (hstart : mumfordPts (u₁ 0) (Y₁ 0) (u₂ 0) (Y₂ 0) = mumford B₁ B₂ p)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, A₁ t + A₂ t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hT : ∀ t ∈ Icc (0 : ℝ) 1, transP (A := A) (hp := hp) (hx := hx) k (A₁ t + A₂ t) ≠ 0) :
    Par (transP (A := A) (hp := hp) (hx := hx) k (A₁ 1 + A₂ 1)) (grantJ (mumfordPts (u₁ 1) (Y₁ 1) (u₂ 1) (Y₂ 1))) ∧
    Par (expLift A hp hx k (A₁ 1 + A₂ 1))
      (A.law0 (grantJ (mumfordPts (u₁ 1) (Y₁ 1) (u₂ 1) (Y₂ 1))) (A.negP (baseP hp hx))) := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hpar := follow_trans G k hA₁ hA₂ hA₁0 hA₂0 hu₁ hu₂ hY₁ hY₂ hdiag hstart hU hT 1 h1
  refine ⟨hpar, ?_⟩
  have h0 := hpar.zero_ne (grantJ_zero _) (hT 1 h1)
  have he := hpar.symm.eq_smul (m := 0) (by rw [grantJ_zero]; exact one_ne_zero)
  rw [grantJ_zero, div_one] at he
  have hi := inv_trans G k (hU 1 h1)
  rw [he, A.law0_smul_left] at hi
  exact hi.of_smul_right (pow_ne_zero 2 h0)

/-- **Periods of divisor loops are in the kernel**: two nondegenerate generic paths from the base pair to a common
end divisor, with path Abel integrals `A = A₁ + A₂`, `A' = A₁' + A₂'`, give `E (z + (A 1 − A' 1)) = E z`. -/
theorem expP_periodic_of_loop (k : ℕ) {u₁ Y₁ u₂ Y₂ v₁ Z₁ v₂ Z₂ : ℝ → ℂ} {A₁ A₂ A₁' A₂' : ℝ → (Fin 2 → ℂ)}
    (hA₁ : IsAbelAlong f₅ 2 u₁ Y₁ A₁) (hA₂ : IsAbelAlong f₅ 2 u₂ Y₂ A₂) (hA₁0 : A₁ 0 = 0) (hA₂0 : A₂ 0 = 0)
    (hu₁ : ContinuousOn u₁ (Icc 0 1)) (hu₂ : ContinuousOn u₂ (Icc 0 1))
    (hY₁ : ContinuousOn Y₁ (Icc 0 1)) (hY₂ : ContinuousOn Y₂ (Icc 0 1))
    (hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u₁ t ≠ u₂ t)
    (hstart : mumfordPts (u₁ 0) (Y₁ 0) (u₂ 0) (Y₂ 0) = mumford B₁ B₂ p)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, A₁ t + A₂ t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hT : ∀ t ∈ Icc (0 : ℝ) 1, transP (A := A) (hp := hp) (hx := hx) k (A₁ t + A₂ t) ≠ 0)
    (hA₁' : IsAbelAlong f₅ 2 v₁ Z₁ A₁') (hA₂' : IsAbelAlong f₅ 2 v₂ Z₂ A₂') (hA₁0' : A₁' 0 = 0)
    (hA₂0' : A₂' 0 = 0)
    (hv₁ : ContinuousOn v₁ (Icc 0 1)) (hv₂ : ContinuousOn v₂ (Icc 0 1))
    (hZ₁ : ContinuousOn Z₁ (Icc 0 1)) (hZ₂ : ContinuousOn Z₂ (Icc 0 1))
    (hdiag' : ∀ t ∈ Icc (0 : ℝ) 1, v₁ t ≠ v₂ t)
    (hstart' : mumfordPts (v₁ 0) (Z₁ 0) (v₂ 0) (Z₂ 0) = mumford B₁ B₂ p)
    (hU' : ∀ t ∈ Icc (0 : ℝ) 1, A₁' t + A₂' t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hT' : ∀ t ∈ Icc (0 : ℝ) 1, transP (A := A) (hp := hp) (hx := hx) k (A₁' t + A₂' t) ≠ 0)
    (hend : mumfordPts (u₁ 1) (Y₁ 1) (u₂ 1) (Y₂ 1) = mumfordPts (v₁ 1) (Z₁ 1) (v₂ 1) (Z₂ 1))
    (hXn : A.law0 (grantJ (mumfordPts (u₁ 1) (Y₁ 1) (u₂ 1) (Y₂ 1))) (A.negP (baseP hp hx)) ≠ 0)
    {z : Fin 2 → ℂ} (hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hzc : z + ((A₁ 1 + A₂ 1) - (A₁' 1 + A₂' 1)) ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    expP G (z + ((A₁ 1 + A₂ 1) - (A₁' 1 + A₂' 1))) = expP G z := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hpa := follow_trans G k hA₁ hA₂ hA₁0 hA₂0 hu₁ hu₂ hY₁ hY₂ hdiag hstart hU hT 1 h1
  have hpb := follow_trans G k hA₁' hA₂' hA₁0' hA₂0' hv₁ hv₂ hZ₁ hZ₂ hdiag' hstart' hU' hT' 1 h1
  rw [← hend] at hpb
  exact expP_periodic_of_two_paths G k (hU 1 h1) (hU' 1 h1) (grantJ_zero _) hXn (hT 1 h1) (hT' 1 h1)
    hpa hpb hz hzc

end LSG.JacAn
