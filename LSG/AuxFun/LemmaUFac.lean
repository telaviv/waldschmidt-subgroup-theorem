/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LemmaUId

/-!
# Lemma U: sizes and analytic bounds for the basic factors of `F_t` (Stage 3, D3b)

* **`ks_gfac`**: every basic factor `gfac f` is `KS` with base `B₁ = 2 (1 + 7 a_V H)` and explicit
  constants (`G_a`: `ks_lin`; `G_m`: `ks_expm`; elliptic: `ks_wpSeries` + `lawk_quad` + `ks_quad`).
* `exists_xi_bound`: a disc around `z₀ = ω₁/2` free of lattice points on which `℘, ℘'` are bounded.
* `differentiableAt_Fpoly`: `F_t` is differentiable where all `z₀ + v_k s` avoid the lattices.
-/

open Complex Finset LSG.Elliptic LSG.Weierstrass LSG.W88 PeriodPair

noncomputable section

namespace LSG.Aux

variable {d0 d1 m D : ℕ}
variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

/-- Size constants of the elliptic basic factors. -/
def AE (C HX' H : ℝ) : ℝ := 24 * (6 * C * HX' ^ 2) * H ^ 2

/-- Denominators of the elliptic basic factors. -/
def eE (l dX' d : ℕ) : ℕ := (l ^ 12 * dX' ^ 2 * 1 ^ 2) * (d * d)

/-- The constants of the basic factors. -/
def Afac (aT hM C HX' H : ℝ) : Fct d0 d1 m → ℝ
  | .inl _ => aT
  | .inr (.inl _) => hM
  | .inr (.inr _) => AE C HX' H

/-- The denominators of the basic factors. -/
def efac (d dM l dX' : ℕ) : Fct d0 d1 m → ℕ
  | .inl _ => d
  | .inr (.inl _) => dM
  | .inr (.inr _) => eE l dX' d

lemma sz_e3 (a : Fin 3) (i : Fin 3) : Sz ι 1 1 (e3 a i : ℂ) := by
  by_cases h : a = i
  · subst h; simpa [e3] using Sz.one (ι := ι)
  · simpa [e3, Pi.single_apply, Ne.symm h] using (Sz.zero (ι := ι) 1).mono_le zero_le_one

/-- **Sizes of the basic factors.** -/
theorem ks_gfac (Ls : Fin m → PeriodPair) (t v : Tan d0 d1 m) (κ : Fin m → Fin 2)
    (X' : Fin m → Fin 3 → ℂ) {H aT aV hM HX' C : ℝ} {d dM dX' l : ℕ} (hH : 1 ≤ H)
    (haT : 1 ≤ aT) (haV : 0 ≤ aV) (hC : 0 ≤ C)
    (hlaw : ∀ k (κ' : Fin 2) (P Q : Fin 3 → ℂ) (Hp Hq : ℝ) (dp dq : ℕ),
      (∀ i, Sz ι Hp dp (P i)) → (∀ i, Sz ι Hq dq (Q i)) → ∀ i,
        Sz ι (C * Hp ^ 2 * Hq ^ 2) (l ^ 12 * dp ^ 2 * dq ^ 2) (lawk κ' (Ls k).g₂ (Ls k).g₃ P Q i))
    (ht0 : ∀ i, Sz ι aT d (t.1 i)) (hv0 : ∀ i, Sz ι aV d (v.1 i))
    (ht1 : ∀ i, Sz ι hM dM (exp (t.2.1 i))) (hv1 : ∀ i, Sz ι aV d (v.2.1 i))
    (hv2 : ∀ k, Sz ι aV d (v.2.2 k)) (hX' : ∀ k i, Sz ι HX' dX' (X' k i))
    (he₁ : ∀ k, Sz ι H d (℘[Ls k] (zh (Ls k)))) (hg₂ : ∀ k, Sz ι H d ((Ls k).g₂ / 2)) :
    ∀ f : Fct d0 d1 m, KS ι (Afac (d0 := d0) (d1 := d1) (m := m) aT hM C HX' H f)
      (2 * (1 + 7 * aV * H)) (efac (d0 := d0) (d1 := d1) (m := m) d dM l dX' f) (d ^ 2)
      (gfac Ls t v κ X' f) := by
  set Bξ : ℝ := 1 + 7 * aV * H
  have hBξ1 : 1 ≤ Bξ := by simp only [Bξ]; nlinarith
  have hB₁ : aV ≤ 2 * Bξ := by simp only [Bξ]; nlinarith
  have hdd : d ∣ d ^ 2 := Dvd.intro_left _ (sq d).symm |>.trans (by rw [sq])
  intro f
  rcases f with i | i | ⟨k, c⟩
  · -- `G_a`
    refine ks_lin (ht0 i) ((hv0 i).mono_le ?_) (by positivity)
    show aV ≤ aT * (2 * Bξ)
    nlinarith
  · -- `G_m`
    exact (ks_expm (ht1 i) (hv1 i)).mono le_rfl haV hB₁ dvd_rfl hdd
  · -- elliptic
    set L := Ls k
    have hξ := ks_wpSeries L (hv2 k) (he₁ k) ((hg₂ k).mono le_rfl (Dvd.intro_left _ rfl |>.trans
      (by rw [sq]))) hH le_rfl hBξ1 (by simp only [Bξ]; nlinarith)
    have hξa : ∀ a, KS ι H Bξ d (d ^ 2) (fun s => xiV L (v.2.2 k) s a) := by
      intro a
      fin_cases a
      · exact hξ.1
      · exact hξ.2
      · exact (KS.const (Sz.one (ι := ι)) (by positivity)).mono hH (by positivity) le_rfl
          (one_dvd d) dvd_rfl
    -- coefficients of the quadratic form
    have hq : ∀ a, Sz ι (6 * C * HX' ^ 2) (l ^ 12 * dX' ^ 2 * 1 ^ 2)
        (lawk (κ k) L.g₂ L.g₃ (X' k) (e3 a) (cidx c)) := by
      intro a
      refine (hlaw k (κ k) (X' k) (e3 a) HX' 1 dX' 1 (hX' k) (sz_e3 a) (cidx c)).mono_le ?_
      nlinarith [sq_nonneg HX']
    have hr : ∀ a b, Sz ι (6 * C * HX' ^ 2) (l ^ 12 * dX' ^ 2 * 1 ^ 2)
        (lawk (κ k) L.g₂ L.g₃ (X' k) (e3 a + e3 b) (cidx c) -
          lawk (κ k) L.g₂ L.g₃ (X' k) (e3 a) (cidx c) -
          lawk (κ k) L.g₂ L.g₃ (X' k) (e3 b) (cidx c)) := by
      intro a b
      have h1 := hlaw k (κ k) (X' k) (e3 a + e3 b) HX' 2 dX' 1 (hX' k)
        (fun i => ((sz_e3 (ι := ι) a i).add (sz_e3 b i)).mono_le (by norm_num)) (cidx c)
      have h2 := hlaw k (κ k) (X' k) (e3 a) HX' 1 dX' 1 (hX' k) (sz_e3 a) (cidx c)
      have h3 := hlaw k (κ k) (X' k) (e3 b) HX' 1 dX' 1 (hX' k) (sz_e3 b) (cidx c)
      refine ((h1.sub h2).sub h3).mono_le (le_of_eq ?_)
      ring
    have hquad := ks_quad (by positivity) hξa hq hr
    have hfun : gfac Ls t v κ X' (.inr (.inr (k, c))) = fun s =>
        ∑ a : Fin 3, lawk (κ k) L.g₂ L.g₃ (X' k) (e3 a) (cidx c) * xiV L (v.2.2 k) s a ^ 2 +
          ∑ a : Fin 3, ∑ b : Fin 3, (if a < b then
            (lawk (κ k) L.g₂ L.g₃ (X' k) (e3 a + e3 b) (cidx c) -
              lawk (κ k) L.g₂ L.g₃ (X' k) (e3 a) (cidx c) -
              lawk (κ k) L.g₂ L.g₃ (X' k) (e3 b) (cidx c)) *
              xiV L (v.2.2 k) s a * xiV L (v.2.2 k) s b else 0) := by
      funext s
      exact lawk_quad _ _ _ _ _ _
    rw [hfun]
    exact hquad

/-- A lattice-free disc around `z₀` with bounds for `℘, ℘'`. -/
lemma exists_xi_bound (L : PeriodPair) : ∃ ρ M : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ M ∧ ∀ u : ℂ, ‖u‖ ≤ ρ →
    zh L + u ∉ L.lattice ∧ ‖℘[L] (zh L + u)‖ ≤ M ∧ ‖℘'[L] (zh L + u)‖ ≤ M := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_compl_lattice L) (zh L) (zh_notMem L)
  set ρ := min (r / 2) 1
  have hρ : 0 < ρ := lt_min (by positivity) one_pos
  have hsub : Metric.closedBall (zh L) ρ ⊆ (L.lattice : Set ℂ)ᶜ := fun x hx =>
    hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx)
      ((min_le_left _ _).trans_lt (by linarith))))
  have hc1 : ContinuousOn ℘[L] (Metric.closedBall (zh L) ρ) := fun x hx =>
    (LSG.Weierstrass.hasDerivAt_weierstrassP L (hsub hx)).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn ℘'[L] (Metric.closedBall (zh L) ρ) := fun x hx =>
    (LSG.Weierstrass.differentiableAt_derivWeierstrassP L (hsub hx)).continuousAt.continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall (zh L) ρ).exists_bound_of_continuousOn hc1
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall (zh L) ρ).exists_bound_of_continuousOn hc2
  refine ⟨ρ, max 1 (max M₁ M₂), hρ, min_le_right _ _, le_max_left _ _, fun u hu => ?_⟩
  have hmem : zh L + u ∈ Metric.closedBall (zh L) ρ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  exact ⟨hsub hmem, (hM₁ _ hmem).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hM₂ _ hmem).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

lemma differentiableAt_lawk_xi (L : PeriodPair) (κ : Fin 2) (X' : Fin 3 → ℂ) (c : ℂ) (i : Fin 3)
    {s : ℂ} (hs : zh L + c * s ∉ L.lattice) :
    DifferentiableAt ℂ (fun s => lawk κ L.g₂ L.g₃ X' (xiV L c s) i) s := by
  have hP : DifferentiableAt ℂ (wpP L c) s := by
    have h := LSG.Weierstrass.hasDerivAt_weierstrassP L hs
    exact h.differentiableAt.comp s (by fun_prop)
  have hQ : DifferentiableAt ℂ (wpQ L c) s := by
    have h := LSG.Weierstrass.differentiableAt_derivWeierstrassP L hs
    exact h.comp s (by fun_prop)
  have hξ : ∀ a, DifferentiableAt ℂ (fun s => xiV L c s a) s := by
    intro a; fin_cases a
    · exact hP
    · exact hQ
    · exact differentiableAt_const _
  have hfun : (fun s => lawk κ L.g₂ L.g₃ X' (xiV L c s) i) = fun s =>
      ∑ a : Fin 3, lawk κ L.g₂ L.g₃ X' (e3 a) i * xiV L c s a ^ 2 +
        ∑ a : Fin 3, ∑ b : Fin 3, (if a < b then
          (lawk κ L.g₂ L.g₃ X' (e3 a + e3 b) i - lawk κ L.g₂ L.g₃ X' (e3 a) i -
            lawk κ L.g₂ L.g₃ X' (e3 b) i) * xiV L c s a * xiV L c s b else 0) := by
    funext s; exact lawk_quad _ _ _ _ _ _
  rw [hfun]
  refine DifferentiableAt.add (DifferentiableAt.fun_sum fun a _ => ?_)
    (DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ => ?_)
  · exact (differentiableAt_const _).mul ((hξ a).pow 2)
  · split_ifs
    · exact ((differentiableAt_const _).mul (hξ a)).mul (hξ b)
    · exact differentiableAt_const _

/-- `F_t` is differentiable where `z₀ + v_k s ∉ Λ_k` for all `k`. -/
lemma differentiableAt_Fpoly (Ls : Fin m → PeriodPair) (t v : Tan d0 d1 m) (κ : Fin m → Fin 2)
    (X' : Fin m → Fin 3 → ℂ) {L : ℕ} (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ) {s : ℂ}
    (hs : ∀ k, zh (Ls k) + v.2.2 k * s ∉ (Ls k).lattice) :
    DifferentiableAt ℂ (Fpoly Ls t v κ X' μs p) s := by
  have hg : ∀ f, DifferentiableAt ℂ (gfac Ls t v κ X' f) s := by
    intro f
    rcases f with i | i | ⟨k, c⟩
    · exact (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)
    · exact (differentiableAt_const _).mul ((differentiableAt_const _).mul
        differentiableAt_id).cexp
    · exact differentiableAt_lawk_xi (Ls k) (κ k) (X' k) (v.2.2 k) (cidx c) (hs k)
  unfold Fpoly
  exact DifferentiableAt.fun_sum fun l _ => (differentiableAt_const _).mul
    (DifferentiableAt.fun_finsetProd fun f _ => (hg f).pow _)

end LSG.Aux
