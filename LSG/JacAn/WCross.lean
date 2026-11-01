/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.PeriodPath

/-!
# Crossing a Weierstrass point: perturbing a path inside a `y`-chart without changing its Abel integral

* `IsAbelAlong.toW`: branch Abel integrals are mixed-chart Abel integrals;
* `abelAlongW_agree`: two mixed Abel integrals of paths that agree on `[α, β]` have the same increment there;
* `abelAlongW_chart`: a chart carrying the path on `[α, β]` computes the increment;
* `exists_perturbation`: a path with `y = 2t − 1` (crossing `y = 0` only at `t = 1/2`) carried near `t = 1/2` by a
  `y`-chart `W` is replaced, on `[1/2 − η, 1/2 + η]`, by `y' = 2t − 1 + i·max(0, η − |t − 1/2|)`, `x' = X_W(y')`: a
  continuous path on the curve with `y' ≠ 0`, the same endpoints, and still carried by `W` there;
* **`abelAlong_perturb_eq`**: its Abel integral has the same value at `t = 1`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology Complex

namespace LSG.JacAn

variable {f : ℂ[X]} {g : ℕ}

lemma IsAbelAlong.toW {u Yp : ℝ → ℂ} {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlong f g u Yp A) :
    IsAbelAlongW f g u Yp A := fun s hs => by
  obtain ⟨B, ε, hε, h⟩ := hA s hs
  exact ⟨.br B, ε, hε, fun t ht => ⟨⟨(h t ht).1, (h t ht).2.1⟩, (h t ht).2.2⟩⟩

lemma PathChart.F_congr (C : PathChart f g) {u Yp u' Yp' : ℝ → ℂ} {t : ℝ} (hu : u' t = u t)
    (hY : Yp' t = Yp t) : C.F u' Yp' t = C.F u Yp t := by
  cases C <;> simp [PathChart.F, hu, hY]

lemma PathChart.carries_congr (C : PathChart f g) {u Yp u' Yp' : ℝ → ℂ} {t : ℝ} (hu : u' t = u t)
    (hY : Yp' t = Yp t) : C.Carries u' Yp' t ↔ C.Carries u Yp t := by
  cases C <;> simp [PathChart.Carries, hu, hY]

/-- Local constancy on an interval gives constancy. -/
lemma const_of_locally_const_Icc {α β : ℝ} {φ : ℝ → (Fin g → ℂ)}
    (h : ∀ τ ∈ Icc α β, ∀ᶠ τ' in 𝓝[Icc α β] τ, φ τ' = φ τ) {a b : ℝ} (ha : a ∈ Icc α β)
    (hb : b ∈ Icc α β) : φ a = φ b := by
  have := Subtype.preconnectedSpace (isPreconnected_Icc (a := α) (b := β))
  have hD : IsLocallyConstant (fun x : Icc α β => φ x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp (h x x.2)
    have hn : {y : Icc α β | (y : ℝ) ∈ ball (x : ℝ) δ} ∈ 𝓝 x :=
      (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hδ)
    filter_upwards [hn] with y hy using hball ⟨hy, y.2⟩
  exact hD.apply_eq_of_isPreconnected isPreconnected_univ (x := ⟨a, ha⟩) (y := ⟨b, hb⟩)
    (mem_univ _) (mem_univ _)

/-- Two mixed Abel integrals of paths agreeing on `[α, β]` have the same increment there. -/
theorem abelAlongW_agree {u Yp u' Yp' : ℝ → ℂ} {A A' : ℝ → (Fin g → ℂ)} (hA : IsAbelAlongW f g u Yp A)
    (hA' : IsAbelAlongW f g u' Yp' A') (hYc : ContinuousOn Yp (Icc 0 1)) {α β : ℝ}
    (hαβ : Icc α β ⊆ Icc 0 1) (hαβ' : α ≤ β) (hu : ∀ t ∈ Icc α β, u' t = u t)
    (hY : ∀ t ∈ Icc α β, Yp' t = Yp t) : A' β - A' α = A β - A α := by
  have key : ∀ τ ∈ Icc α β, ∀ᶠ τ' in 𝓝[Icc α β] τ, (A' τ' - A τ') = (A' τ - A τ) := by
    intro τ hτ
    have hτ1 := hαβ hτ
    obtain ⟨C, ε, hε, hC⟩ := hA τ hτ1
    obtain ⟨C', ε', hε', hC'⟩ := hA' τ hτ1
    have hCτ := hC τ ⟨mem_ball_self hε, hτ1⟩
    have hC'τ := hC' τ ⟨mem_ball_self hε', hτ1⟩
    have hC'τ' : C'.Carries u Yp τ := (C'.carries_congr (hu τ hτ) (hY τ hτ)).mp hC'τ.1
    have hcomp := PathChart.eventually_compat C' C (hYc τ hτ1) hC'τ' hCτ.1
    have hJ : 𝓝[Icc α β] τ ≤ 𝓝[Icc 0 1] τ := nhdsWithin_mono _ hαβ
    filter_upwards [hJ hcomp, inter_mem_nhdsWithin (Icc α β) (ball_mem_nhds τ (lt_min hε hε')),
      self_mem_nhdsWithin] with τ' hτ'c hτ'b hτ'J
    have hτ'1 := hαβ hτ'J
    have hb1 : τ' ∈ ball τ ε := ball_subset_ball (min_le_left _ _) hτ'b.2
    have hb2 : τ' ∈ ball τ ε' := ball_subset_ball (min_le_right _ _) hτ'b.2
    have i1 := hCτ.2 τ' ⟨hb1, hτ'1⟩
    have i2 := hC'τ.2 τ' ⟨hb2, hτ'1⟩
    have c1 := (hC τ' ⟨hb1, hτ'1⟩).1
    have c2 : C'.Carries u Yp τ' := (C'.carries_congr (hu τ' hτ'J) (hY τ' hτ'J)).mp (hC' τ' ⟨hb2, hτ'1⟩).1
    have hc := hτ'c c2 c1
    rw [C'.F_congr (hu τ' hτ'J) (hY τ' hτ'J), C'.F_congr (hu τ hτ) (hY τ hτ)] at i2
    rw [sub_eq_iff_eq_add.mp i1, sub_eq_iff_eq_add.mp i2, sub_eq_iff_eq_add.mp hc]; abel
  have := const_of_locally_const_Icc key ⟨le_rfl, hαβ'⟩ ⟨hαβ', le_rfl⟩
  rw [sub_eq_iff_eq_add.mp this]; abel

/-- A chart carrying the path on `[α, β]` computes the increment of the mixed Abel integral. -/
theorem abelAlongW_chart {u Yp : ℝ → ℂ} {A : ℝ → (Fin g → ℂ)} (hA : IsAbelAlongW f g u Yp A)
    (hYc : ContinuousOn Yp (Icc 0 1)) {α β : ℝ} (hαβ : Icc α β ⊆ Icc 0 1) (hαβ' : α ≤ β)
    (C₀ : PathChart f g) (hC₀ : ∀ t ∈ Icc α β, C₀.Carries u Yp t) :
    A β - A α = C₀.F u Yp β - C₀.F u Yp α := by
  have key : ∀ τ ∈ Icc α β, ∀ᶠ τ' in 𝓝[Icc α β] τ, (A τ' - C₀.F u Yp τ') = (A τ - C₀.F u Yp τ) := by
    intro τ hτ
    have hτ1 := hαβ hτ
    obtain ⟨C, ε, hε, hC⟩ := hA τ hτ1
    have hCτ := hC τ ⟨mem_ball_self hε, hτ1⟩
    have hcomp := PathChart.eventually_compat C₀ C (hYc τ hτ1) (hC₀ τ hτ) hCτ.1
    have hJ : 𝓝[Icc α β] τ ≤ 𝓝[Icc 0 1] τ := nhdsWithin_mono _ hαβ
    filter_upwards [hJ hcomp, inter_mem_nhdsWithin (Icc α β) (ball_mem_nhds τ hε),
      self_mem_nhdsWithin] with τ' hτ'c hτ'b hτ'J
    have hτ'1 := hαβ hτ'J
    have i1 := hCτ.2 τ' ⟨hτ'b.2, hτ'1⟩
    have hc := hτ'c (hC₀ τ' hτ'J) (hC τ' ⟨hτ'b.2, hτ'1⟩).1
    rw [sub_eq_iff_eq_add.mp i1, sub_eq_iff_eq_add.mp hc]; abel
  have := const_of_locally_const_Icc key ⟨le_rfl, hαβ'⟩ ⟨hαβ', le_rfl⟩
  rw [sub_eq_iff_eq_add.mp this]; abel

/-- The tent function `max 0 (η − |t − 1/2|)`. -/
def tent (η t : ℝ) : ℝ := max 0 (η - |t - 1 / 2|)

lemma continuous_tent (η : ℝ) : Continuous (tent η) :=
  continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).abs))

lemma tent_eq_zero {η t : ℝ} (h : η ≤ |t - 1 / 2|) : tent η t = 0 := by
  simp [tent]; linarith

lemma tent_pos {η t : ℝ} (h : |t - 1 / 2| < η) : 0 < tent η t := by
  simp only [tent]; exact lt_max_of_lt_right (by linarith)

lemma tent_le {η t : ℝ} (hη : 0 ≤ η) : tent η t ≤ η := by
  simp only [tent]; exact max_le hη (by linarith [abs_nonneg (t - 1 / 2)])

lemma tent_nonneg (η t : ℝ) : 0 ≤ tent η t := le_max_left _ _

/-- The perturbed `y`: `2t − 1 + i·tent η t`. -/
def pertY (η : ℝ) (t : ℝ) : ℂ := 2 * (t : ℂ) - 1 + I * (tent η t : ℂ)

/-- The perturbed `x`: `u + (X_W(y') − X_W(2t − 1))`, equal to `X_W(y')` near `1/2` and to `u` away from it. -/
def pertU (W : WeierChart f g) (u : ℝ → ℂ) (η : ℝ) (t : ℝ) : ℂ :=
  u t + (W.X (pertY η t) - W.X (2 * (t : ℂ) - 1))

lemma norm_two_t_sub_one (t : ℝ) : ‖2 * (t : ℂ) - 1‖ = 2 * |t - 1 / 2| := by
  have : 2 * (t : ℂ) - 1 = ((2 * (t - 1 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]

lemma pertY_eq_of_far {η t : ℝ} (h : η ≤ |t - 1 / 2|) : pertY η t = 2 * (t : ℂ) - 1 := by
  simp [pertY, tent_eq_zero h]

lemma pertU_eq_of_far (W : WeierChart f g) (u : ℝ → ℂ) {η t : ℝ} (h : η ≤ |t - 1 / 2|) :
    pertU W u η t = u t := by
  simp [pertU, pertY_eq_of_far h]

lemma norm_pertY_le (η t : ℝ) (hη : 0 ≤ η) : ‖pertY η t‖ ≤ 2 * |t - 1 / 2| + η := by
  calc ‖pertY η t‖ ≤ ‖2 * (t : ℂ) - 1‖ + ‖I * (tent η t : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * |t - 1 / 2| + η := by
      rw [norm_two_t_sub_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (tent_nonneg η t)]
      linarith [tent_le (t := t) hη]

lemma continuous_pertY (η : ℝ) : Continuous (pertY η) :=
  ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_tent η)))

section Perturb

variable (W : WeierChart f g) {u : ℝ → ℂ} {ε η : ℝ}
  (hW : ∀ t ∈ ball (1 / 2 : ℝ) ε ∩ Icc 0 1, (2 * (t : ℂ) - 1) ∈ ball (0 : ℂ) W.r ∧ W.X (2 * (t : ℂ) - 1) = u t)
  (h1 : 0 < η) (h2 : η < 1 / 2) (h3 : 2 * η < ε) (h4 : 5 * η < W.r)

include hW h2 h3 in
lemma carries_orig {t : ℝ} (ht : t ∈ Icc (1 / 2 - η) (1 / 2 + η)) :
    (2 * (t : ℂ) - 1) ∈ ball (0 : ℂ) W.r ∧ W.X (2 * (t : ℂ) - 1) = u t := by
  refine hW t ⟨?_, ?_⟩
  · rw [Real.ball_eq_Ioo]; constructor <;> linarith [ht.1, ht.2]
  · constructor <;> linarith [ht.1, ht.2]

include hW h1 h2 h3 h4 in
lemma carries_pert {t : ℝ} (ht : t ∈ Icc (1 / 2 - η) (1 / 2 + η)) :
    pertY η t ∈ ball (0 : ℂ) W.r ∧ W.X (pertY η t) = pertU W u η t := by
  have habs : |t - 1 / 2| ≤ η := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff]
    linarith [norm_pertY_le η t h1.le]
  · simp only [pertU, (carries_orig W hW h2 h3 ht).2]; ring

include hW h1 h2 h3 h4 in
lemma pert_sq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hsq : (2 * (t : ℂ) - 1) ^ 2 = f.eval (u t)) :
    pertY η t ^ 2 = f.eval (pertU W u η t) := by
  by_cases hfar : η ≤ |t - 1 / 2|
  · rw [pertY_eq_of_far hfar, pertU_eq_of_far W u hfar, hsq]
  · push Not at hfar
    have hI : t ∈ Icc (1 / 2 - η) (1 / 2 + η) := by
      have := abs_lt.mp hfar; constructor <;> linarith [this.1, this.2]
    obtain ⟨hb, hX⟩ := carries_pert W hW h1 h2 h3 h4 hI
    rw [← hX, W.X_sq _ hb]

include h1 in
lemma pertY_ne_zero {t : ℝ} : pertY η t ≠ 0 := by
  by_cases hfar : η ≤ |t - 1 / 2|
  · rw [pertY_eq_of_far hfar]
    intro h
    have := norm_two_t_sub_one t
    rw [h, norm_zero] at this
    linarith
  · push Not at hfar
    intro h
    have him : (pertY η t).im = tent η t := by simp [pertY]
    rw [h, Complex.zero_im] at him
    linarith [tent_pos hfar]

include hW h1 h2 h3 h4 in
lemma continuous_pertU_diff :
    Continuous (fun t => W.X (pertY η t) - W.X (2 * (t : ℂ) - 1)) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases hnear : |t - 1 / 2| < 2 * η
  · have hb1 : pertY η t ∈ ball (0 : ℂ) W.r := by
      rw [mem_ball_zero_iff]; linarith [norm_pertY_le η t h1.le]
    have hb2 : (2 * (t : ℂ) - 1) ∈ ball (0 : ℂ) W.r := by
      rw [mem_ball_zero_iff, norm_two_t_sub_one]; linarith
    have c1 := ((W.X_an _ hb1).continuousAt).comp (continuous_pertY η).continuousAt
    have c2 := ((W.X_an _ hb2).continuousAt).comp
      ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).continuousAt (x := t)
    exact c1.sub c2
  · push Not at hnear
    have hopen : IsOpen {t' : ℝ | η < |t' - 1 / 2|} :=
      isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)
    have hmem : t ∈ {t' : ℝ | η < |t' - 1 / 2|} := by simp only [mem_setOf_eq]; linarith
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hopen.mem_nhds hmem] with t' (ht' : η < |t' - 1 / 2|)
    rw [pertY_eq_of_far ht'.le, sub_self]

end Perturb

/-- **The perturbed path has the same Abel integral at `t = 1`.** -/
theorem abelAlong_perturb_eq (W : WeierChart f g) {u : ℝ → ℂ} {ε η : ℝ}
    (hW : ∀ t ∈ ball (1 / 2 : ℝ) ε ∩ Icc 0 1, (2 * (t : ℂ) - 1) ∈ ball (0 : ℂ) W.r ∧
      W.X (2 * (t : ℂ) - 1) = u t)
    (h1 : 0 < η) (h2 : η < 1 / 2) (h3 : 2 * η < ε) (h4 : 5 * η < W.r)
    {A A' : ℝ → (Fin g → ℂ)} (hA : IsAbelAlongW f g u (fun t => 2 * (t : ℂ) - 1) A) (hA0 : A 0 = 0)
    (hA' : IsAbelAlongW f g (pertU W u η) (pertY η) A') (hA'0 : A' 0 = 0) : A' 1 = A 1 := by
  have hYc : ContinuousOn (fun t : ℝ => 2 * (t : ℂ) - 1) (Icc 0 1) :=
    ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).continuousOn
  have hY'c : ContinuousOn (pertY η) (Icc 0 1) := (continuous_pertY η).continuousOn
  set t₁ : ℝ := 1 / 2 - η with ht₁
  set t₂ : ℝ := 1 / 2 + η with ht₂
  have hsub1 : Icc 0 t₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl (by linarith)
  have hsub2 : Icc t₂ 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (by linarith) le_rfl
  have hsub3 : Icc t₁ t₂ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (by linarith) (by linarith)
  have far1 : ∀ t ∈ Icc 0 t₁, η ≤ |t - 1 / 2| := fun t ht => by
    rw [abs_sub_comm, abs_of_pos (by linarith [ht.2])]; linarith [ht.2]
  have far2 : ∀ t ∈ Icc t₂ 1, η ≤ |t - 1 / 2| := fun t ht => by
    rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
  have e1 := abelAlongW_agree hA hA' hYc hsub1 (by linarith)
    (fun t ht => pertU_eq_of_far W u (far1 t ht)) (fun t ht => pertY_eq_of_far (far1 t ht))
  have e2 := abelAlongW_agree hA hA' hYc hsub2 (by linarith)
    (fun t ht => pertU_eq_of_far W u (far2 t ht)) (fun t ht => pertY_eq_of_far (far2 t ht))
  have e3 := abelAlongW_chart hA hYc hsub3 (by linarith) (.we W)
    (fun t ht => carries_orig W hW h2 h3 ht)
  have e4 := abelAlongW_chart hA' hY'c hsub3 (by linarith) (.we W)
    (fun t ht => carries_pert W hW h1 h2 h3 h4 ht)
  have hp1 : pertY η t₁ = 2 * (t₁ : ℂ) - 1 := pertY_eq_of_far (by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith)
  have hp2 : pertY η t₂ = 2 * (t₂ : ℂ) - 1 := pertY_eq_of_far (by rw [abs_of_pos (by linarith)]; linarith)
  simp only [PathChart.F, hp1, hp2] at e3 e4
  rw [hA0, hA'0, sub_zero, sub_zero] at e1
  have e34 : A' t₂ - A' t₁ = A t₂ - A t₁ := e4.trans e3.symm
  calc A' 1 = (A' 1 - A' t₂) + (A' t₂ - A' t₁) + A' t₁ := by abel
    _ = (A 1 - A t₂) + (A t₂ - A t₁) + A t₁ := by rw [e2, e34, e1]
    _ = A 1 := by abel

end LSG.JacAn
