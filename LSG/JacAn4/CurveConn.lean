/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.ContinuationW
import LSG.JacAn.PeriodPath
import Mathlib.Analysis.Complex.CoveringMap

/-!
# A4.1b (S-b, topology): path-connectedness of the generic locus of `C × C`, `C : y² = 4x⁵ + 1`

* `CovB B = {(x, y) : y² = 4x⁵ + 1, x ∉ B}` for a finite `B` containing the roots of `4x⁵ + 1`;
* `lift_path`: paths in `ℂ ∖ B` (path-connected: countable complement, `Set.Countable.isPathConnected_compl_of_one_lt_rank`)
  lift to `CovB B` (path lifting for the covering `z ↦ z²` of `ℂ ∖ 0`, `isCoveringMap_npow`);
* `sign_swap`: `(x, y)` and `(x, −y)` are joined in `CovB B` (a half circle `y = ρe^{iπt}` in a Weierstrass chart
  `x = X_W(y)` at a root, with `X_W(−ρ) = X_W(ρ)`);
* **`isPathConnected_covB`**;
* **`isPathConnected_genPairs`**: pairs of points of `CovB R` (`R` = the roots) with distinct `x` form a path-connected set.
-/

noncomputable section

open Metric Set Filter Topology Polynomial Complex

namespace LSG.JacAn

/-- `4x⁵ + 1`. -/
def fc (x : ℂ) : ℂ := 4 * x ^ 5 + 1

lemma fc_eq (x : ℂ) : fc x = f₅.eval x := by rw [f₅_eval]; rfl

/-- The curve over the complement of `B`. -/
def CovB (B : Set ℂ) : Set (ℂ × ℂ) := {q | q.2 ^ 2 = fc q.1 ∧ q.1 ∉ B}

/-- The roots of `4x⁵ + 1`. -/
def rootsC : Set ℂ := {x | fc x = 0}

lemma rootsC_finite : rootsC.Finite := by
  have hne : f₅ ≠ 0 := by
    intro h; have := congrArg (fun p => p.eval 0) h; simp [f₅_eval] at this
  refine (Polynomial.finite_setOf_isRoot hne).subset fun x hx => ?_
  simp only [rootsC, mem_setOf_eq, fc_eq] at hx
  exact hx

variable {B : Set ℂ}

lemma ne_zero_of_mem_covB {q : ℂ × ℂ} (hq : q ∈ CovB B) (hroot : rootsC ⊆ B) : q.2 ≠ 0 := by
  intro h
  apply hq.2 (hroot _)
  show fc q.1 = 0
  rw [← hq.1, h]; ring

/-- **Path lifting.** -/
theorem lift_path (hBc : B.Countable) (hroot : rootsC ⊆ B) {q : ℂ × ℂ} (hq : q ∈ CovB B) {x' : ℂ}
    (hx' : x' ∉ B) : ∃ y' : ℂ, y' ^ 2 = fc x' ∧ JoinedIn (CovB B) q (x', y') := by
  have hpc : IsPathConnected Bᶜ := hBc.isPathConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]; norm_num)
  have hJ := hpc.joinedIn q.1 hq.2 x' hx'
  set γ := hJ.somePath
  have hγ : ∀ t, γ t ∈ Bᶜ := hJ.somePath_mem
  have hfne : ∀ t, fc (γ t) ≠ 0 := fun t h => hγ t (hroot h)
  let g : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ⟨fc (γ t), hfne t⟩, by
      refine Continuous.subtype_mk ?_ _
      unfold fc; fun_prop⟩
  have hq2 := ne_zero_of_mem_covB hq hroot
  have cov := isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num)
  obtain ⟨Γ, hΓ, hΓ0⟩ := cov.exists_path_lifts g ⟨q.2, hq2⟩ (by
    apply Subtype.ext
    show fc (γ 0) = q.2 ^ 2
    rw [γ.source, hq.1])
  have hsq : ∀ t, ((Γ t : ℂ)) ^ 2 = fc (γ t) := fun t => by
    have := congrArg Subtype.val (congrFun hΓ t)
    simpa [g] using this
  refine ⟨Γ 1, by rw [hsq 1, γ.target], ?_⟩
  let P : Path q (x', (Γ 1 : ℂ)) :=
    { toFun := fun t => (γ t, (Γ t : ℂ))
      continuous_toFun := γ.continuous.prodMk (continuous_subtype_val.comp Γ.continuous)
      source' := by
        refine Prod.ext γ.source ?_
        show ((Γ 0 : ℂ)) = q.2
        rw [hΓ0]
      target' := by
        refine Prod.ext γ.target rfl }
  exact ⟨P, fun t => ⟨hsq t, hγ t⟩⟩

/-- `y ↦ −y`. -/
def negY (q : ℂ × ℂ) : ℂ × ℂ := (q.1, -q.2)

lemma negY_joined {q q' : ℂ × ℂ} (h : JoinedIn (CovB B) q q') : JoinedIn (CovB B) (negY q) (negY q') := by
  have := h.map (f := negY) (by unfold negY; fun_prop)
  refine this.mono ?_
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨by simp [negY, hr.1], hr.2⟩

/-- **Sign swap.** -/
theorem sign_swap (hfin : B.Finite) (hroot : rootsC ⊆ B) {q : ℂ × ℂ} (hq : q ∈ CovB B) :
    JoinedIn (CovB B) q (negY q) := by
  -- a simple root and a Weierstrass chart
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (-1 / 4 : ℂ) (by norm_num : 0 < 5)
  have hfe : f₅.eval e = 0 := by rw [f₅_eval, he]; ring
  have he0 : e ≠ 0 := by rintro rfl; norm_num at he
  have hde : (derivative f₅).eval e ≠ 0 := by
    rw [f₅_deriv_eval]; exact mul_ne_zero (by norm_num) (pow_ne_zero 4 he0)
  obtain ⟨W, hWe⟩ := WeierChart.exists_of_root (g := 2) hfe hde
  obtain ⟨δ₁, hδ₁, hinj⟩ := exists_injOn_ball f₅ hde
  have hT : (B \ {e}).Finite := hfin.diff
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.mem_nhds_iff.mp
    (hT.isClosed.isOpen_compl.mem_nhds (fun h : e ∈ B \ {e} => h.2 rfl))
  have hXc : ContinuousAt W.X 0 := (W.X_an 0 (mem_ball_self W.r_pos)).continuousAt
  obtain ⟨ρ₀, hρ₀, hX⟩ := Metric.continuousAt_iff.mp hXc (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
  set ρ : ℝ := min ρ₀ W.r / 2
  have hρ : 0 < ρ := half_pos (lt_min hρ₀ W.r_pos)
  have hρ1 : ρ < ρ₀ := (half_lt_self (lt_min hρ₀ W.r_pos)).trans_le (min_le_left _ _)
  have hρ2 : ρ < W.r := (half_lt_self (lt_min hρ₀ W.r_pos)).trans_le (min_le_right _ _)
  have hXball : ∀ y : ℂ, ‖y‖ = ρ → W.X y ∈ ball e δ₁ ∧ W.X y ∈ ball e δ₂ := fun y hy => by
    have h := hX (x := y) (by rw [dist_zero_right, hy]; exact hρ1)
    rw [W.X_zero, hWe] at h
    exact ⟨mem_ball.mpr (h.trans_le (min_le_left _ _)), mem_ball.mpr (h.trans_le (min_le_right _ _))⟩
  have hmem : ∀ y : ℂ, ‖y‖ = ρ → (W.X y, y) ∈ CovB B := fun y hy => by
    have hyr : y ∈ ball (0 : ℂ) W.r := by rw [mem_ball_zero_iff, hy]; exact hρ2
    have hsq : f₅.eval (W.X y) = y ^ 2 := W.X_sq y hyr
    refine ⟨by rw [fc_eq, hsq], fun hB => ?_⟩
    by_cases hXe : W.X y = e
    · have : y ^ 2 = 0 := by rw [← hsq, hXe, hfe]
      have : y = 0 := pow_eq_zero_iff (by norm_num) |>.mp this
      rw [this, norm_zero] at hy; linarith
    · exact hball₂ (hXball y hy).2 ⟨hB, hXe⟩
  -- the half circle
  set c : ℝ → ℂ := fun t => (ρ : ℂ) * Complex.exp (Real.pi * I * t)
  have hcn : ∀ t : ℝ, ‖c t‖ = ρ := fun t => by
    simp only [c, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    rw [show (Real.pi : ℂ) * I * t = ((Real.pi * t : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
      mul_one]
  have hc0 : c 0 = ρ := by simp [c]
  have hc1 : c 1 = -ρ := by
    simp only [c, Complex.ofReal_one, mul_one, Complex.exp_pi_mul_I]; ring
  have hXeven : W.X (-(ρ : ℂ)) = W.X ρ := by
    have h1 := hXball (-(ρ : ℂ)) (by simp [abs_of_pos hρ])
    have h2 := hXball (ρ : ℂ) (by simp [abs_of_pos hρ])
    refine hinj h1.1 h2.1 ?_
    have hr1 : (-(ρ : ℂ)) ∈ ball (0 : ℂ) W.r := by rw [mem_ball_zero_iff]; simpa [abs_of_pos hρ] using hρ2
    have hr2 : (ρ : ℂ) ∈ ball (0 : ℂ) W.r := by rw [mem_ball_zero_iff]; simpa [abs_of_pos hρ] using hρ2
    simp only
    rw [W.X_sq _ hr1, W.X_sq _ hr2]; ring
  have hcont : Continuous c := by unfold c; fun_prop
  have hcircle : JoinedIn (CovB B) (W.X ρ, (ρ : ℂ)) (W.X ρ, -(ρ : ℂ)) := by
    refine JoinedIn.ofLine (f := fun t => (W.X (c t), c t)) ?_ (by simp [hc0]) (by simp [hc1, hXeven]) ?_
    · refine ContinuousOn.prodMk ?_ hcont.continuousOn
      intro t _
      have hct : c t ∈ ball (0 : ℂ) W.r := by rw [mem_ball_zero_iff, hcn]; exact hρ2
      exact ((W.X_an _ hct).continuousAt.comp hcont.continuousAt).continuousWithinAt
    · rintro _ ⟨t, -, rfl⟩
      exact hmem _ (hcn t)
  -- lift a path from `q` to the base point
  have hx0 : W.X ρ ∉ B := (hmem ρ (by simp [abs_of_pos hρ])).2
  obtain ⟨y₀, hy₀, hJ⟩ := lift_path hfin.countable hroot hq hx0
  have hy₀' : y₀ ^ 2 = (ρ : ℂ) ^ 2 := by
    have hr : (ρ : ℂ) ∈ ball (0 : ℂ) W.r := by rw [mem_ball_zero_iff]; simpa [abs_of_pos hρ] using hρ2
    rw [hy₀, fc_eq, W.X_sq _ hr]
  have hJn := negY_joined hJ
  simp only [negY] at hJn
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy₀' with h | h
  · subst h
    exact (hJ.trans hcircle).trans hJn.symm
  · subst h
    simp only [neg_neg] at hJn
    exact (hJ.trans hcircle.symm).trans hJn.symm

/-- **The curve over `ℂ ∖ B` is path-connected.** -/
theorem isPathConnected_covB (hfin : B.Finite) (hroot : rootsC ⊆ B) : IsPathConnected (CovB B) := by
  rw [isPathConnected_iff]
  refine ⟨?_, fun q hq q' hq' => ?_⟩
  · obtain ⟨x, hx⟩ := hfin.infinite_compl.nonempty
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (fc x) (by norm_num : 0 < 2)
    exact ⟨(x, y), hy, hx⟩
  · obtain ⟨y', hy', hJ⟩ := lift_path hfin.countable hroot hq hq'.2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy'.trans hq'.1.symm) with h | h
    · rw [h] at hJ; exact hJ
    · rw [h] at hJ
      have hs := sign_swap hfin hroot (q := (q'.1, -q'.2)) ⟨by rw [neg_sq]; exact hq'.1, hq'.2⟩
      simp only [negY, neg_neg] at hs
      exact hJ.trans hs

/-- Pairs of points with distinct `x`. -/
def GenPairs : Set ((ℂ × ℂ) × (ℂ × ℂ)) :=
  {P | P.1 ∈ CovB rootsC ∧ P.2 ∈ CovB rootsC ∧ P.1.1 ≠ P.2.1}

lemma move_first {P₁ Q₁ R : ℂ × ℂ} (hR : R ∈ CovB rootsC) (hP : P₁ ∈ CovB (rootsC ∪ {R.1}))
    (hQ : Q₁ ∈ CovB (rootsC ∪ {R.1})) : JoinedIn GenPairs (P₁, R) (Q₁, R) := by
  have hJ := (isPathConnected_covB (rootsC_finite.union (finite_singleton _)) subset_union_left).joinedIn
    P₁ hP Q₁ hQ
  have := hJ.map (f := fun Q => (Q, R)) (by fun_prop)
  refine this.mono ?_
  rintro _ ⟨Q, hQ', rfl⟩
  exact ⟨⟨hQ'.1, fun h => hQ'.2 (Or.inl h)⟩, hR, fun h => hQ'.2 (Or.inr h)⟩

lemma move_second {P R R' : ℂ × ℂ} (hP : P ∈ CovB rootsC) (hR : R ∈ CovB (rootsC ∪ {P.1}))
    (hR' : R' ∈ CovB (rootsC ∪ {P.1})) : JoinedIn GenPairs (P, R) (P, R') := by
  have hJ := (isPathConnected_covB (rootsC_finite.union (finite_singleton _)) subset_union_left).joinedIn
    R hR R' hR'
  have := hJ.map (f := fun Q => (P, Q)) (by fun_prop)
  refine this.mono ?_
  rintro _ ⟨Q, hQ', rfl⟩
  exact ⟨hP, ⟨hQ'.1, fun h => hQ'.2 (Or.inl h)⟩, fun h => hQ'.2 (Or.inr h.symm)⟩

/-- **The generic locus of `C × C` is path-connected.** -/
theorem isPathConnected_genPairs : IsPathConnected GenPairs := by
  rw [isPathConnected_iff]
  have hex : ∀ S : Set ℂ, S.Finite → ∃ R : ℂ × ℂ, R ∈ CovB S := fun S hS => by
    obtain ⟨x, hx⟩ := hS.infinite_compl.nonempty
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (fc x) (by norm_num : 0 < 2)
    exact ⟨(x, y), hy, hx⟩
  refine ⟨?_, fun P hP Q hQ => ?_⟩
  · obtain ⟨R₁, hR₁⟩ := hex rootsC rootsC_finite
    obtain ⟨R₂, hR₂⟩ := hex (rootsC ∪ {R₁.1}) (rootsC_finite.union (finite_singleton _))
    exact ⟨(R₁, R₂), ⟨hR₁.1, hR₁.2⟩, ⟨hR₂.1, fun h => hR₂.2 (Or.inl h)⟩,
      fun h => hR₂.2 (Or.inr h.symm)⟩
  · -- an auxiliary second point `R` with `x(R) ∉ {x(P₁), x(Q₁)}`
    obtain ⟨R, hR⟩ := hex (rootsC ∪ {P.1.1, Q.1.1})
      (rootsC_finite.union ((finite_singleton _).insert _))
    have hRr : R ∈ CovB rootsC := ⟨hR.1, fun h => hR.2 (Or.inl h)⟩
    have hRP : R.1 ≠ P.1.1 := fun h => hR.2 (Or.inr (Or.inl h))
    have hRQ : R.1 ≠ Q.1.1 := fun h => hR.2 (Or.inr (Or.inr h))
    -- `(P₁, P₂) → (P₁, R)`
    have h1 : JoinedIn GenPairs (P.1, P.2) (P.1, R) :=
      move_second hP.1 ⟨hP.2.1.1, fun h => h.elim hP.2.1.2 fun h' => hP.2.2 h'.symm⟩
        ⟨hR.1, fun h => h.elim (fun h' => hR.2 (Or.inl h')) hRP⟩
    -- `(P₁, R) → (Q₁, R)`
    have h2 : JoinedIn GenPairs (P.1, R) (Q.1, R) :=
      move_first hRr ⟨hP.1.1, fun h => h.elim hP.1.2 fun h' => hRP h'.symm⟩
        ⟨hQ.1.1, fun h => h.elim hQ.1.2 fun h' => hRQ h'.symm⟩
    -- `(Q₁, R) → (Q₁, Q₂)`
    have h3 : JoinedIn GenPairs (Q.1, R) (Q.1, Q.2) :=
      move_second hQ.1 ⟨hR.1, fun h => h.elim (fun h' => hR.2 (Or.inl h')) hRQ⟩
        ⟨hQ.2.1.1, fun h => h.elim hQ.2.1.2 fun h' => hQ.2.2 h'.symm⟩
    exact (h1.trans h2).trans h3

end LSG.JacAn
