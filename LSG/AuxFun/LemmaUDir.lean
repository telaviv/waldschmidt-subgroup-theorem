/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LemmaU

/-!
# Lemma U along one direction (Stage 3, D3b)

**`lemmaU_dir`**: for a point `t`, a direction `v`, representatives `X'_k` of `exp(t_k + z₀)`
(with `law_{κ_k}(X'_k, (e₁, 0, 1)) ≠ 0`), the size hypotheses of `ks_gfac`, a lattice-free disc of
radius `ρ₁` around `z₀` with `|℘|, |℘'| ≤ M_ξ`, charts with `|ellV_j| ≥ e^{−c_r}` on `t_k + B(0, ρ₁)`,
`|Ψ(t + s v)| ≤ e^{−U}` on `|s| ≤ ρ₁/(1 + |v|)`, and the Liouville inequality `hQ`, all derivatives
of order `< T` of `s ↦ Ψ(t + s v)` vanish at `0`.
-/

open Complex Finset LSG.Elliptic LSG.Weierstrass LSG.W88 PeriodPair NumberField
open scoped ContDiff Topology

noncomputable section

namespace LSG.Aux

variable {d0 d1 m : ℕ}
variable {K : Type*} [Field K] [NumberField K]

/-- **Lemma U along one direction.** -/
theorem lemmaU_dir (Ls : Fin m → PeriodPair) (ι : K →+* ℂ) {L D : ℕ}
    (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ) {A₀ A₁ T : ℕ} {B U : ℝ}
    (hα : ∀ l i, (μs l).α i ≤ A₀) (hβ : ∀ l i, (μs l).β i ≤ A₁)
    (hp : ∀ l, |(p l : ℝ)| ≤ Real.exp B) (hB : 0 ≤ B)
    (t v : Tan d0 d1 m) (κ2 : Fin m → Fin 2) (X' : Fin m → Fin 3 → ℂ)
    (hX'rep : ∀ k, IsRep (Ls k) (t.2.2 k + zh (Ls k)) (X' k))
    (hκ2 : ∀ k, lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k) ![℘[Ls k] (zh (Ls k)), 0, 1] ≠ 0)
    {H aT aV hM HX' Cl : ℝ} {d dM dX' l : ℕ} (hH : 1 ≤ H) (hd : 1 ≤ d) (haT : 1 ≤ aT)
    (haV : 0 ≤ aV) (hhM : 1 ≤ hM) (hdM : 1 ≤ dM) (hHX' : 1 ≤ HX') (hdX' : 1 ≤ dX') (hl : 1 ≤ l)
    (hCl : 1 ≤ Cl)
    (hlaw : ∀ k (κ' : Fin 2) (P Q : Fin 3 → ℂ) (Hp Hq : ℝ) (dp dq : ℕ),
      (∀ i, Sz ι Hp dp (P i)) → (∀ i, Sz ι Hq dq (Q i)) → ∀ i,
        Sz ι (Cl * Hp ^ 2 * Hq ^ 2) (l ^ 12 * dp ^ 2 * dq ^ 2) (lawk κ' (Ls k).g₂ (Ls k).g₃ P Q i))
    (ht0 : ∀ i, Sz ι aT d (t.1 i)) (hv0 : ∀ i, Sz ι aV d (v.1 i))
    (ht1 : ∀ i, Sz ι hM dM (exp (t.2.1 i))) (hv1 : ∀ i, Sz ι aV d (v.2.1 i))
    (hv2 : ∀ k, Sz ι aV d (v.2.2 k)) (hX's : ∀ k i, Sz ι HX' dX' (X' k i))
    (he₁ : ∀ k, Sz ι H d (℘[Ls k] (zh (Ls k)))) (hg₂ : ∀ k, Sz ι H d ((Ls k).g₂ / 2))
    {ρ₁ C'l Mξ cr : ℝ} (hρ₁ : 0 < ρ₁) (hC'l : 0 ≤ C'l) (hMξ : 1 ≤ Mξ)
    (hlawB : ∀ k (κ' : Fin 2) (P Q : Fin 3 → ℂ) i,
      ‖lawk κ' (Ls k).g₂ (Ls k).g₃ P Q i‖ ≤ C'l * ‖P‖ ^ 2 * ‖Q‖ ^ 2)
    (hxi : ∀ k (u : ℂ), ‖u‖ ≤ ρ₁ → zh (Ls k) + u ∉ (Ls k).lattice ∧
      ‖℘[Ls k] (zh (Ls k) + u)‖ ≤ Mξ ∧ ‖℘'[Ls k] (zh (Ls k) + u)‖ ≤ Mξ)
    (hchart : ∀ k, ∃ j : Fin 3, ∀ z : ℂ, ‖z‖ ≤ ρ₁ →
      Real.exp (-cr) ≤ ‖ellV (Ls k) (t.2.2 k + z) j‖)
    (hsmall : ∀ s : ℂ, ‖s‖ ≤ ρ₁ / (1 + ‖v‖) → ‖Psi Ls μs p (t + s • v)‖ ≤ Real.exp (-U))
    (hQ : ∀ k < T, (C'l * HX' ^ 2 * Mξ ^ 2 * Real.exp cr) ^ (m * D) * Real.exp (-U) /
      (ρ₁ / (1 + ‖v‖)) ^ k * ((((∏ f, efac (d0 := d0) (d1 := d1) (m := m) d dM l dX' f ^
        Nfac A₀ A₁ D f) * (d ^ 2) ^ k * k.factorial : ℕ) : ℝ) *
        (((L : ℝ) + 1) * Real.exp B * (2 ^ (∑ f : Fct d0 d1 m, Nfac A₀ A₁ D f) *
          ∏ f, Afac (d0 := d0) (d1 := d1) (m := m) aT hM Cl HX' H f ^ Nfac A₀ A₁ D f) *
          (2 * (2 * (1 + 7 * aV * H))) ^ k)) ^ Module.finrank ℚ K < 1) :
    ∀ k < T, iteratedDeriv k (fun s : ℂ => Psi Ls μs p (t + s • v)) 0 = 0 := by
  classical
  -- the `KS` bound for `F_t`
  have hfac := ks_gfac (d0 := d0) (d1 := d1) Ls t v κ2 X' hH haT haV (zero_le_one.trans hCl)
    hlaw ht0 hv0 ht1 hv1 hv2 hX's he₁ hg₂
  have hn : ∀ l f, (μs l).expo f ≤ Nfac A₀ A₁ D f := by
    intro l f
    rcases f with i | i | ⟨k, c⟩
    · exact hα l i
    · exact hβ l i
    · show (μs l).γ k c ≤ D
      calc (μs l).γ k c ≤ ∑ c', (μs l).γ k c' :=
            single_le_sum (f := fun c => (μs l).γ k c) (fun _ _ => Nat.zero_le _) (mem_univ c)
        _ = D := (μs l).hγ k
  have hAE : 1 ≤ AE Cl HX' H := by
    unfold AE
    have h1 : 1 ≤ Cl * HX' ^ 2 := one_le_mul_of_one_le_of_one_le hCl (one_le_pow₀ hHX')
    have h2 : 1 ≤ H ^ 2 := one_le_pow₀ hH
    nlinarith
  have hAf1 : ∀ f, 1 ≤ Afac (d0 := d0) (d1 := d1) (m := m) aT hM Cl HX' H f := by
    intro f; rcases f with i | i | ⟨k, c⟩
    · exact haT
    · exact hhM
    · exact hAE
  have hB₁ : 0 ≤ 2 * (1 + 7 * aV * H) := by positivity
  have hKS := KS.poly hB₁ hfac hAf1 p (fun l => (μs l).expo) (Nfac A₀ A₁ D) hn
  set Aprod : ℝ := 2 ^ (∑ f : Fct d0 d1 m, Nfac A₀ A₁ D f) *
    ∏ f, Afac (d0 := d0) (d1 := d1) (m := m) aT hM Cl HX' H f ^ Nfac A₀ A₁ D f with hAprod
  have hAprod1 : 1 ≤ Aprod :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
      (one_le_prod₀ fun f _ => one_le_pow₀ (hAf1 f))
  have hsum : ∑ l, |(p l : ℝ)| ≤ ((L : ℝ) + 1) * Real.exp B := by
    calc ∑ l, |(p l : ℝ)| ≤ ∑ _l : Fin L, Real.exp B := sum_le_sum fun l _ => hp l
      _ = L * Real.exp B := by simp
      _ ≤ ((L : ℝ) + 1) * Real.exp B := by gcongr; linarith
  set A' : ℝ := ((L : ℝ) + 1) * Real.exp B * Aprod with hA'
  have hA'1 : 1 ≤ A' := by
    rw [hA']
    have h1 : 1 ≤ ((L : ℝ) + 1) * Real.exp B :=
      one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
        (Real.one_le_exp hB)
    exact one_le_mul_of_one_le_of_one_le h1 hAprod1
  have hKS' : KS ι A' (2 * (2 * (1 + 7 * aV * H)))
      (∏ f, efac (d0 := d0) (d1 := d1) (m := m) d dM l dX' f ^ Nfac A₀ A₁ D f) (d ^ 2)
      (Fpoly Ls t v κ2 X' μs p) := by
    refine hKS.mono ?_ (by positivity) le_rfl dvd_rfl dvd_rfl
    rw [hA']; exact mul_le_mul_of_nonneg_right hsum (by positivity)
  -- the disc
  set ρ : ℝ := ρ₁ / (1 + ‖v‖) with hρdef
  have hρ : 0 < ρ := by positivity
  have hvs : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, ‖v.2.2 k * s‖ ≤ ρ₁ := by
    intro s hs k
    have hvk : ‖v.2.2 k‖ ≤ ‖v‖ :=
      (norm_le_pi_norm _ k).trans ((norm_snd_le _).trans (norm_snd_le _))
    rw [norm_mul]
    calc ‖v.2.2 k‖ * ‖s‖ ≤ ‖v‖ * ρ := mul_le_mul hvk hs (norm_nonneg _) (norm_nonneg _)
      _ ≤ ρ₁ := by
          rw [hρdef, mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg v]
  choose jk hjk using hchart
  have hjne : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, ellV (Ls k) (t.2.2 k + v.2.2 k * s) (jk k) ≠ 0 :=
    fun s hs k => norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) (hjk k _ (hvs s hs k)))
  set R : Fin m → ℂ → ℂ := fun k s => lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k)
      (xiV (Ls k) (v.2.2 k) s) (jk k) / ellV (Ls k) (t.2.2 k + v.2.2 k * s) (jk k) with hRdef
  have hFeq : ∀ s : ℂ, ‖s‖ ≤ ρ → Fpoly Ls t v κ2 X' μs p s =
      (∏ k, R k s ^ D) * Psi Ls μs p (t + s • v) := fun s hs =>
    Fpoly_eq Ls t v κ2 X' hX'rep μs p jk (fun k => (hxi k _ (hvs s hs k)).1) (hjne s hs)
  -- bounds
  set MR : ℝ := C'l * HX' ^ 2 * Mξ ^ 2 * Real.exp cr with hMRdef
  have hMR0 : 0 ≤ MR := by positivity
  have hR : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, ‖R k s‖ ≤ MR := by
    intro s hs k
    obtain ⟨-, hP, hQ'⟩ := hxi k _ (hvs s hs k)
    have hden := hjk k _ (hvs s hs k)
    have hX'n : ‖X' k‖ ≤ HX' :=
      (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => (hX's k i).norm_le
    have hξn : ‖xiV (Ls k) (v.2.2 k) s‖ ≤ Mξ := by
      refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
      fin_cases i
      · exact hP
      · exact hQ'
      · simpa [xiV] using hMξ
    have hnum := hlawB k (κ2 k) (X' k) (xiV (Ls k) (v.2.2 k) s) (jk k)
    have hpos : 0 < ‖ellV (Ls k) (t.2.2 k + v.2.2 k * s) (jk k)‖ :=
      lt_of_lt_of_le (Real.exp_pos _) hden
    simp only [hRdef]
    rw [norm_div, div_le_iff₀ hpos]
    calc ‖lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k) (xiV (Ls k) (v.2.2 k) s) (jk k)‖
        ≤ C'l * ‖X' k‖ ^ 2 * ‖xiV (Ls k) (v.2.2 k) s‖ ^ 2 := hnum
      _ ≤ C'l * HX' ^ 2 * Mξ ^ 2 := by gcongr
      _ = MR * Real.exp (-cr) := by
          rw [hMRdef, mul_assoc _ (Real.exp cr), ← Real.exp_add]; simp
      _ ≤ MR * ‖ellV (Ls k) (t.2.2 k + v.2.2 k * s) (jk k)‖ := by gcongr
  have hFb : ∀ s : ℂ, ‖s‖ ≤ ρ → ‖Fpoly Ls t v κ2 X' μs p s‖ ≤ MR ^ (m * D) * Real.exp (-U) := by
    intro s hs
    rw [hFeq s hs, norm_mul, norm_prod]
    refine mul_le_mul ?_ (hsmall s hs) (norm_nonneg _) (by positivity)
    calc ∏ k, ‖R k s ^ D‖ ≤ ∏ _k : Fin m, MR ^ D :=
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => by
            rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hR s hs k) D
      _ = MR ^ (m * D) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  have hdc : DiffContOnCl ℂ (Fpoly Ls t v κ2 X' μs p) (Metric.ball 0 ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball 0 hρ.ne']
    intro s hs
    exact (differentiableAt_Fpoly Ls t v κ2 X' μs p
      (fun k => (hxi k _ (hvs s (by simpa using hs) k)).1)).differentiableWithinAt
  -- the Taylor coefficients vanish
  have he1 : 1 ≤ ∏ f, efac (d0 := d0) (d1 := d1) (m := m) d dM l dX' f ^ Nfac A₀ A₁ D f := by
    refine Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun f _ => pow_ne_zero _ ?_)
    rcases f with i | i | ⟨k, c⟩
    · exact Nat.one_le_iff_ne_zero.mp hd
    · exact Nat.one_le_iff_ne_zero.mp hdM
    · simp only [efac, eE]; positivity
  have htco : ∀ k < T, tco k (Fpoly Ls t v κ2 X' μs p) = 0 := by
    intro k hk
    refine tco_eq_zero_of_small hKS' hA'1 (by nlinarith) he1 (one_le_pow₀ hd) hρ hdc
      (fun z hz => hFb z (by rw [mem_sphere_zero_iff_norm] at hz; exact hz.le)) ?_
    have := hQ k hk
    simpa only [hA', hAprod, hMRdef] using this
  -- the unit `u = Π R_k^D`
  have hRan : ∀ k, AnalyticAt ℂ (R k) 0 := by
    intro k
    have hnum : AnalyticAt ℂ (fun s => lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k)
        (xiV (Ls k) (v.2.2 k) s) (jk k)) 0 := by
      refine DifferentiableOn.analyticAt (s := Metric.ball 0 ρ) (fun s hs => ?_)
        (Metric.ball_mem_nhds 0 hρ)
      exact (differentiableAt_lawk_xi (Ls k) (κ2 k) (X' k) (v.2.2 k) (jk k)
        (hxi k _ (hvs s (le_of_lt (by simpa using hs)) k)).1).differentiableWithinAt
    have hden : AnalyticAt ℂ (fun s => ellV (Ls k) (t.2.2 k + v.2.2 k * s) (jk k)) 0 := by
      have hd' : Differentiable ℂ (fun s => ellV (Ls k) (t.2.2 k + v.2.2 k * s) (jk k)) :=
        (differentiable_ellV_apply (Ls k) (jk k)).comp (by fun_prop)
      exact hd'.analyticAt 0
    exact hnum.div hden (hjne 0 (by simp [hρ.le]) k)
  have hR0 : ∀ k, R k 0 ≠ 0 := by
    intro k h0
    have hxi0 : xiV (Ls k) (v.2.2 k) 0 = ![℘[Ls k] (zh (Ls k)), 0, 1] := by
      funext i; fin_cases i <;> simp [xiV, wpP, wpQ, derivWp_zh]
    have heq := lawk_eq_smul_ellV (Ls k) (hX'rep k) (c := v.2.2 k) (s := 0)
      (hxi k _ (hvs 0 (by simp [hρ.le]) k)).1 (κ2 k) (hjne 0 (by simp [hρ.le]) k)
    have h0' : lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k) (xiV (Ls k) (v.2.2 k) 0) (jk k) /
        ellV (Ls k) (t.2.2 k + v.2.2 k * 0) (jk k) = 0 := h0
    rw [h0', zero_smul, hxi0] at heq
    exact hκ2 k heq
  set u : ℂ → ℂ := fun s => ∏ k, R k s ^ D with hudef
  have hu : AnalyticAt ℂ u 0 := Finset.analyticAt_fun_prod _ fun k _ => (hRan k).pow D
  have hu0 : u 0 ≠ 0 := prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hR0 k)
  have hev : Fpoly Ls t v κ2 X' μs p =ᶠ[𝓝 0] u * fun s => Psi Ls μs p (t + s • v) := by
    filter_upwards [Metric.closedBall_mem_nhds 0 hρ] with s hs
    rw [hFeq s (by simpa using hs)]
    rfl
  intro k hk
  refine iteratedDeriv_eq_zero_of_mul hu hu0 (analyticAt_Psi_line Ls μs p t v) (T := T) ?_ k hk
  intro j hj
  rw [← (hev.iteratedDeriv j).eq_of_nhds]
  have := htco j hj
  unfold tco at this
  rcases div_eq_zero_iff.mp this with h | h
  · exact h
  · exact absurd h (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))

end LSG.Aux
