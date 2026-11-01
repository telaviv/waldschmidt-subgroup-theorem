/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.KSFib
import LSG.AuxFun.LemmaUDir

/-!
# Lemma U for the class `𝒞` along one direction (Stage 5, phase 2)

**`lemmaU_dirV`**: as `LSG.Aux.lemmaU_dir`, for `Ψ = Σ p_l M_l` with monomials `MonoV` of
`G ∈ 𝒞`. The additional data are the constants `cᵢ = sᵢ(t) − Σ_j M_ij W_j` of the fibre factors
and a `KS` bound `(A_fib, 2B₁, e_fib, d²)` for them (`ks_fibFac`). All basic factors are used with
base `2B₁` (`B₁ = 2(1 + 7 a_V H)`), so `F_t` has base `4B₁`; the unit is the abelian `Π R_k^D`
(`FpolyV_eq`), so the analytic bound on `F_t` is the abelian one.
-/

open Complex Finset LSG.Elliptic LSG.Weierstrass LSG.W88 LSG.W88.Vec PeriodPair NumberField
open LSG.Aux (ellW ellV IsRep zh wpP wpQ xiV lawk Fct gfac Afac efac Nfac AE eE KS Sz ks_gfac
  tco tco_eq_zero_of_small lawk_eq_smul_ellV differentiableAt_lawk_xi derivWp_zh
  iteratedDeriv_eq_zero_of_mul differentiable_ellV_apply)
open scoped ContDiff Topology

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m r : ℕ}
variable {K : Type*} [Field K] [NumberField K]

/-- Constants of the basic factors of the class `𝒞`. -/
def AfacV (aT hM C HX' H Afib : ℝ) : FctV d0 d1 m r → ℝ
  | .inl f => Afac aT hM C HX' H f
  | .inr _ => Afib

/-- Denominators of the basic factors of the class `𝒞`. -/
def efacV (d dM l dX' efib : ℕ) : FctV d0 d1 m r → ℕ
  | .inl f => efac d dM l dX' f
  | .inr _ => efib

/-- Exponent bounds of the basic factors of the class `𝒞`. -/
def NfacV (A₀ A₁ D : ℕ) : FctV d0 d1 m r → ℕ
  | .inl f => Nfac A₀ A₁ D f
  | .inr _ => D

/-- **Lemma U for the class `𝒞` along one direction.** -/
theorem lemmaU_dirV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (ι : K →+* ℂ)
    {L D : ℕ} (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) {A₀ A₁ T : ℕ} {B U : ℝ}
    (hα : ∀ l i, (μs l).α i ≤ A₀) (hβ : ∀ l i, (μs l).β i ≤ A₁)
    (hp : ∀ l, |(p l : ℝ)| ≤ Real.exp B) (hB : 0 ≤ B)
    (t v : TanV d0 d1 m r) (κ2 : Fin m → Fin 2) (X' : Fin m → Fin 3 → ℂ)
    (hX'rep : ∀ k, IsRep (Ls k) (t.2.2.1 k + zh (Ls k)) (X' k))
    (hκ2 : ∀ k, lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k) ![℘[Ls k] (zh (Ls k)), 0, 1] ≠ 0)
    (cst : Fin r → ℂ) (hcst : ∀ i, cst i = t.2.2.2 i - ∑ j, M i j * Wpar (Ls j) (t.2.2.1 j))
    {H aT aV hM HX' Cl Afib : ℝ} {d dM dX' l efib : ℕ} (hH : 1 ≤ H) (hd : 1 ≤ d)
    (haT : 1 ≤ aT) (haV : 0 ≤ aV) (hhM : 1 ≤ hM) (hdM : 1 ≤ dM) (hHX' : 1 ≤ HX') (hdX' : 1 ≤ dX')
    (hl : 1 ≤ l) (hCl : 1 ≤ Cl) (hAfib : 1 ≤ Afib) (hefib : 1 ≤ efib)
    (hlaw : ∀ k (κ' : Fin 2) (P Q : Fin 3 → ℂ) (Hp Hq : ℝ) (dp dq : ℕ),
      (∀ i, Sz ι Hp dp (P i)) → (∀ i, Sz ι Hq dq (Q i)) → ∀ i,
        Sz ι (Cl * Hp ^ 2 * Hq ^ 2) (l ^ 12 * dp ^ 2 * dq ^ 2) (lawk κ' (Ls k).g₂ (Ls k).g₃ P Q i))
    (ht0 : ∀ i, Sz ι aT d ((piT t).1 i)) (hv0 : ∀ i, Sz ι aV d ((piT v).1 i))
    (ht1 : ∀ i, Sz ι hM dM (exp ((piT t).2.1 i))) (hv1 : ∀ i, Sz ι aV d ((piT v).2.1 i))
    (hv2 : ∀ k, Sz ι aV d ((piT v).2.2 k)) (hX's : ∀ k i, Sz ι HX' dX' (X' k i))
    (he₁ : ∀ k, Sz ι H d (℘[Ls k] (zh (Ls k)))) (hg₂ : ∀ k, Sz ι H d ((Ls k).g₂ / 2))
    (hfib : ∀ i, KS ι Afib (2 * (2 * (1 + 7 * aV * H))) efib (d ^ 2) (fibFac Ls M κ2 X' cst v i))
    {ρ₁ C'l Mξ cr : ℝ} (hρ₁ : 0 < ρ₁) (hC'l : 0 ≤ C'l) (hMξ : 1 ≤ Mξ)
    (hlawB : ∀ k (κ' : Fin 2) (P Q : Fin 3 → ℂ) i,
      ‖lawk κ' (Ls k).g₂ (Ls k).g₃ P Q i‖ ≤ C'l * ‖P‖ ^ 2 * ‖Q‖ ^ 2)
    (hxi : ∀ k (u : ℂ), ‖u‖ ≤ ρ₁ → zh (Ls k) + u ∉ (Ls k).lattice ∧
      ‖℘[Ls k] (zh (Ls k) + u)‖ ≤ Mξ ∧ ‖℘'[Ls k] (zh (Ls k) + u)‖ ≤ Mξ)
    (hchart : ∀ k, ∃ j : Fin 3, ∀ z : ℂ, ‖z‖ ≤ ρ₁ →
      Real.exp (-cr) ≤ ‖ellV (Ls k) (t.2.2.1 k + z) j‖)
    (hsmall : ∀ s : ℂ, ‖s‖ ≤ ρ₁ / (1 + ‖v‖) → ‖PsiV Ls M μs p (t + s • v)‖ ≤ Real.exp (-U))
    (hQ : ∀ k < T, (C'l * HX' ^ 2 * Mξ ^ 2 * Real.exp cr) ^ (m * D) * Real.exp (-U) /
      (ρ₁ / (1 + ‖v‖)) ^ k * ((((∏ f, efacV (d0 := d0) (d1 := d1) (m := m) (r := r) d dM l dX'
        efib f ^ NfacV A₀ A₁ D f) * (d ^ 2) ^ k * k.factorial : ℕ) : ℝ) *
        (((L : ℝ) + 1) * Real.exp B * (2 ^ (∑ f : FctV d0 d1 m r, NfacV A₀ A₁ D f) *
          ∏ f, AfacV (d0 := d0) (d1 := d1) (m := m) (r := r) aT hM Cl HX' H Afib f ^
            NfacV A₀ A₁ D f) *
          (2 * (2 * (2 * (1 + 7 * aV * H)))) ^ k)) ^ Module.finrank ℚ K < 1) :
    ∀ k < T, iteratedDeriv k (fun s : ℂ => PsiV Ls M μs p (t + s • v)) 0 = 0 := by
  classical
  set B₁ : ℝ := 2 * (1 + 7 * aV * H) with hB₁def
  have hB₁ : 0 ≤ B₁ := by positivity
  -- the `KS` bound for `F_t`
  have hfacA := ks_gfac (d0 := d0) (d1 := d1) Ls (piT t) (piT v) κ2 X' hH haT haV
    (zero_le_one.trans hCl) hlaw ht0 hv0 ht1 hv1 hv2 hX's he₁ hg₂
  have hfac : ∀ f : FctV d0 d1 m r, KS ι (AfacV aT hM Cl HX' H Afib f) (2 * B₁)
      (efacV d dM l dX' efib f) (d ^ 2) (gfacV Ls M t v κ2 X' cst f) := by
    intro f
    rcases f with f | i
    · exact (hfacA f).mono le_rfl hB₁ (by linarith) dvd_rfl dvd_rfl
    · exact hfib i
  have hn : ∀ l f, (μs l).expo f ≤ NfacV A₀ A₁ D f := by
    intro l f
    rcases f with (i | i | ⟨k, c⟩) | i
    · exact hα l i
    · exact hβ l i
    · change (μs l).γ k c ≤ D
      calc (μs l).γ k c ≤ ∑ c', (μs l).γ k c' :=
            single_le_sum (f := fun c => (μs l).γ k c) (fun _ _ => Nat.zero_le _) (mem_univ c)
        _ ≤ ∑ c', (μs l).γ k c' + ∑ i, (μs l).φ i := Nat.le_add_right _ _
        _ = D := (μs l).hγ k
    · change (μs l).φ i ≤ D
      exact (single_le_sum (f := fun i => (μs l).φ i) (fun _ _ => Nat.zero_le _)
        (mem_univ i)).trans (μs l).hφ
  have hAE : 1 ≤ AE Cl HX' H := by
    unfold AE
    have h1 : 1 ≤ Cl * HX' ^ 2 := one_le_mul_of_one_le_of_one_le hCl (one_le_pow₀ hHX')
    have h2 : 1 ≤ H ^ 2 := one_le_pow₀ hH
    nlinarith
  have hAf1 : ∀ f, 1 ≤ AfacV (d0 := d0) (d1 := d1) (m := m) (r := r) aT hM Cl HX' H Afib f := by
    intro f; rcases f with (i | i | ⟨k, c⟩) | i
    · exact haT
    · exact hhM
    · exact hAE
    · exact hAfib
  have hKS := KS.poly (by positivity : (0 : ℝ) ≤ 2 * B₁) hfac hAf1 p (fun l => (μs l).expo)
    (NfacV A₀ A₁ D) hn
  set Aprod : ℝ := 2 ^ (∑ f : FctV d0 d1 m r, NfacV A₀ A₁ D f) *
    ∏ f, AfacV (d0 := d0) (d1 := d1) (m := m) (r := r) aT hM Cl HX' H Afib f ^ NfacV A₀ A₁ D f
    with hAprod
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
  have hKS' : KS ι A' (2 * (2 * B₁))
      (∏ f, efacV (d0 := d0) (d1 := d1) (m := m) (r := r) d dM l dX' efib f ^ NfacV A₀ A₁ D f)
      (d ^ 2) (FpolyV Ls M t v κ2 X' cst μs p) := by
    refine hKS.mono ?_ (by positivity) le_rfl dvd_rfl dvd_rfl
    rw [hA']; exact mul_le_mul_of_nonneg_right hsum (by positivity)
  -- the disc
  set ρ : ℝ := ρ₁ / (1 + ‖v‖) with hρdef
  have hρ : 0 < ρ := by positivity
  have hvs : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, ‖v.2.2.1 k * s‖ ≤ ρ₁ := by
    intro s hs k
    have hvk : ‖v.2.2.1 k‖ ≤ ‖v‖ :=
      (norm_le_pi_norm _ k).trans ((norm_fst_le _).trans ((norm_snd_le _).trans (norm_snd_le _)))
    rw [norm_mul]
    calc ‖v.2.2.1 k‖ * ‖s‖ ≤ ‖v‖ * ρ := mul_le_mul hvk hs (norm_nonneg _) (norm_nonneg _)
      _ ≤ ρ₁ := by
          rw [hρdef, mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg v]
  choose jk hjk using hchart
  have hjne : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (jk k) ≠ 0 :=
    fun s hs k => norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) (hjk k _ (hvs s hs k)))
  set R : Fin m → ℂ → ℂ := fun k s => lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k)
      (xiV (Ls k) (v.2.2.1 k) s) (jk k) / ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (jk k)
    with hRdef
  have hFeq : ∀ s : ℂ, ‖s‖ ≤ ρ → FpolyV Ls M t v κ2 X' cst μs p s =
      (∏ k, R k s ^ D) * PsiV Ls M μs p (t + s • v) := fun s hs =>
    FpolyV_eq Ls M t v κ2 X' hX'rep cst hcst μs p jk (fun k => (hxi k _ (hvs s hs k)).1)
      (hjne s hs)
  -- bounds
  set MR : ℝ := C'l * HX' ^ 2 * Mξ ^ 2 * Real.exp cr with hMRdef
  have hMR0 : 0 ≤ MR := by positivity
  have hR : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, ‖R k s‖ ≤ MR := by
    intro s hs k
    obtain ⟨-, hP, hQ'⟩ := hxi k _ (hvs s hs k)
    have hden := hjk k _ (hvs s hs k)
    have hX'n : ‖X' k‖ ≤ HX' :=
      (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => (hX's k i).norm_le
    have hξn : ‖xiV (Ls k) (v.2.2.1 k) s‖ ≤ Mξ := by
      refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
      fin_cases i
      · exact hP
      · exact hQ'
      · simpa [xiV] using hMξ
    have hnum := hlawB k (κ2 k) (X' k) (xiV (Ls k) (v.2.2.1 k) s) (jk k)
    have hpos : 0 < ‖ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (jk k)‖ :=
      lt_of_lt_of_le (Real.exp_pos _) hden
    simp only [hRdef]
    rw [norm_div, div_le_iff₀ hpos]
    calc ‖lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k) (xiV (Ls k) (v.2.2.1 k) s) (jk k)‖
        ≤ C'l * ‖X' k‖ ^ 2 * ‖xiV (Ls k) (v.2.2.1 k) s‖ ^ 2 := hnum
      _ ≤ C'l * HX' ^ 2 * Mξ ^ 2 := by gcongr
      _ = MR * Real.exp (-cr) := by
          rw [hMRdef, mul_assoc _ (Real.exp cr), ← Real.exp_add]; simp
      _ ≤ MR * ‖ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (jk k)‖ := by gcongr
  have hFb : ∀ s : ℂ, ‖s‖ ≤ ρ →
      ‖FpolyV Ls M t v κ2 X' cst μs p s‖ ≤ MR ^ (m * D) * Real.exp (-U) := by
    intro s hs
    rw [hFeq s hs, norm_mul, norm_prod]
    refine mul_le_mul ?_ (hsmall s hs) (norm_nonneg _) (by positivity)
    calc ∏ k, ‖R k s ^ D‖ ≤ ∏ _k : Fin m, MR ^ D :=
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => by
            rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hR s hs k) D
      _ = MR ^ (m * D) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  have hdiff : ∀ s : ℂ, ‖s‖ ≤ ρ → DifferentiableAt ℂ (FpolyV Ls M t v κ2 X' cst μs p) s := by
    intro s hs
    have hs' : ∀ k, zh (Ls k) + v.2.2.1 k * s ∉ (Ls k).lattice :=
      fun k => (hxi k _ (hvs s hs k)).1
    have hg : ∀ f, DifferentiableAt ℂ (gfacV Ls M t v κ2 X' cst f) s := by
      intro f
      rcases f with (i | i | ⟨k, c⟩) | i
      · exact (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)
      · exact (differentiableAt_const _).mul ((differentiableAt_const _).mul
          differentiableAt_id).cexp
      · exact differentiableAt_lawk_xi (Ls k) (κ2 k) (X' k) (v.2.2.1 k) (LSG.Aux.cidx c) (hs' k)
      · exact differentiableAt_fibFac Ls M κ2 X' cst v i hs'
    unfold FpolyV
    exact DifferentiableAt.fun_sum fun l _ => (differentiableAt_const _).mul
      (DifferentiableAt.fun_finsetProd fun f _ => (hg f).pow _)
  have hdc : DiffContOnCl ℂ (FpolyV Ls M t v κ2 X' cst μs p) (Metric.ball 0 ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball 0 hρ.ne']
    intro s hs
    exact (hdiff s (by simpa using hs)).differentiableWithinAt
  -- the Taylor coefficients vanish
  have he1 : 1 ≤ ∏ f, efacV (d0 := d0) (d1 := d1) (m := m) (r := r) d dM l dX' efib f ^
      NfacV A₀ A₁ D f := by
    refine Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun f _ => pow_ne_zero _ ?_)
    rcases f with (i | i | ⟨k, c⟩) | i
    · exact Nat.one_le_iff_ne_zero.mp hd
    · exact Nat.one_le_iff_ne_zero.mp hdM
    · simp only [efacV, efac, eE]; positivity
    · exact Nat.one_le_iff_ne_zero.mp hefib
  have htco : ∀ k < T, tco k (FpolyV Ls M t v κ2 X' cst μs p) = 0 := by
    intro k hk
    refine tco_eq_zero_of_small hKS' hA'1 (by nlinarith) he1 (one_le_pow₀ hd) hρ hdc
      (fun z hz => hFb z (by rw [mem_sphere_zero_iff_norm] at hz; exact hz.le)) ?_
    have := hQ k hk
    simpa only [hA', hAprod, hMRdef, hB₁def] using this
  -- the unit `u = Π R_k^D`
  have hRan : ∀ k, AnalyticAt ℂ (R k) 0 := by
    intro k
    have hnum : AnalyticAt ℂ (fun s => lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k)
        (xiV (Ls k) (v.2.2.1 k) s) (jk k)) 0 := by
      refine DifferentiableOn.analyticAt (s := Metric.ball 0 ρ) (fun s hs => ?_)
        (Metric.ball_mem_nhds 0 hρ)
      exact (differentiableAt_lawk_xi (Ls k) (κ2 k) (X' k) (v.2.2.1 k) (jk k)
        (hxi k _ (hvs s (le_of_lt (by simpa using hs)) k)).1).differentiableWithinAt
    have hden : AnalyticAt ℂ (fun s => ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (jk k)) 0 := by
      have hd' : Differentiable ℂ (fun s => ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (jk k)) :=
        (differentiable_ellV_apply (Ls k) (jk k)).comp (by fun_prop)
      exact hd'.analyticAt 0
    exact hnum.div hden (hjne 0 (by simp [hρ.le]) k)
  have hR0 : ∀ k, R k 0 ≠ 0 := by
    intro k h0
    have hxi0 : xiV (Ls k) (v.2.2.1 k) 0 = ![℘[Ls k] (zh (Ls k)), 0, 1] := by
      funext i; fin_cases i <;> simp [xiV, wpP, wpQ, derivWp_zh]
    have heq := lawk_eq_smul_ellV (Ls k) (hX'rep k) (c := v.2.2.1 k) (s := 0)
      (hxi k _ (hvs 0 (by simp [hρ.le]) k)).1 (κ2 k) (hjne 0 (by simp [hρ.le]) k)
    have h0' : lawk (κ2 k) (Ls k).g₂ (Ls k).g₃ (X' k) (xiV (Ls k) (v.2.2.1 k) 0) (jk k) /
        ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * 0) (jk k) = 0 := h0
    rw [h0', zero_smul, hxi0] at heq
    exact hκ2 k heq
  set u : ℂ → ℂ := fun s => ∏ k, R k s ^ D with hudef
  have hu : AnalyticAt ℂ u 0 := Finset.analyticAt_fun_prod _ fun k _ => (hRan k).pow D
  have hu0 : u 0 ≠ 0 := prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hR0 k)
  have hev : FpolyV Ls M t v κ2 X' cst μs p =ᶠ[𝓝 0] u * fun s => PsiV Ls M μs p (t + s • v) := by
    filter_upwards [Metric.closedBall_mem_nhds 0 hρ] with s hs
    rw [hFeq s (by simpa using hs)]
    rfl
  intro k hk
  refine iteratedDeriv_eq_zero_of_mul hu hu0 (analyticAt_PsiV_line Ls M μs p t v) (T := T) ?_ k hk
  intro j hj
  rw [← (hev.iteratedDeriv j).eq_of_nhds]
  have := htco j hj
  unfold tco at this
  rcases div_eq_zero_iff.mp this with h | h
  · exact h
  · exact absurd h (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))

end LSG.AuxV
