/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunA.LemmaUFac
import LSG.AuxFunA.LemmaUBud

/-!
# A5.5c: Lemma U along one line (`STAGE_A5.md` D2)

**`lemmaU_line`.** Let `t` have block parts in the period lattices and coordinates of size `(S(μ+1)H, d)`,
`(H^{μS}, d^{μS})`, and let `v` have coordinates of size `((T+1)(τ+1)H, d)`, `‖t‖ ≤ S Y`, `‖v‖ ≤ T W`. If
`|Ψ(t + s v)| ≤ e^{−U}` for `|s| ≤ ρ₀/(1 + T W)` and `U ≥ K · Bud` (`kLU`, constants independent of
`B, L, A₀, A₁, D, S, T`), then all derivatives of order `< T` of `s ↦ Ψ(t + s v)` vanish at `0`.

Proof: the factorisation `Ψ(t + s v) = u(s) F(s)` (`PsiA_line_eq`), the sizes of the Taylor coefficients of `F`
(`ks_FA`), Cauchy on `|s| = ρ` with the lower bound of the unit (quasi-periodicity bounds and
`|θ_{i₀}| ≥ θ_m` on `B(0, ρ₀)`), Liouville (`LSG.Aux.tco_eq_zero_of_small`) with the bookkeeping of
`LemmaUBud.lean`, and Leibniz.
-/

open Complex Finset Module Metric LSG.W88
open scoped ContDiff Topology

noncomputable section

namespace LSG.AuxA

open LSG.MEB LSG.Aux

variable {K : Type*} [Field K] [NumberField K]
variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock} {D : ℕ}

lemma prod_RVarA {M : Type*} [CommMonoid M] (F : RVarA d₀ d₁ B → M) :
    ∏ f, F f = (∏ i, F (.inl i)) * (∏ j, F (.inr (.inl j))) * ∏ k, ∏ j, F (.inr (.inr ⟨k, j⟩)) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sigma, mul_assoc]

lemma sum_RVarA {M : Type*} [AddCommMonoid M] (F : RVarA d₀ d₁ B → M) :
    ∑ f, F f = (∑ i, F (.inl i)) + (∑ j, F (.inr (.inl j))) + ∑ k, ∑ j, F (.inr (.inr ⟨k, j⟩)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma, add_assoc]

/-- The constant of Lemma U along a line. -/
def kLU {ι : K →+* ℂ} (An : ∀ k, AbBlockAn (B k)) (Tay : ∀ k, AbBlockTay (B k) ι) (μ τ : ℕ) (H : ℝ) (d : ℕ)
    (Ys Wn ρ₀ θm : ℝ) : ℝ :=
  m * (cQU An * Ys ^ 2 + cQU An * Ys + Real.log (1 / θm)) +
    (1 + Real.log ((1 + Wn) / ρ₀) / Real.log 2) +
    finrank ℚ K * ((d₀ * (2 * Real.log d / Real.log 2) + d₁ * μ * Real.log d +
        Real.log ((∏ k, (Tay k).E ^ (B k).g : ℕ) : ℝ) + Real.log ((d * δm Tay : ℕ) : ℝ) / Real.log 2 + 1) +
      (1 + d₀ + d₁ + (∑ k, (B k).g : ℕ) + d₀ * (1 + Real.log ((μ + 1) * H) / Real.log 2) +
        d₁ * μ * Real.log H + Real.log (∏ k, (Tay k).A ^ (B k).g) +
        (1 + Real.log (2 * cBm Tay * ((τ + 1) * H)) / Real.log 2))) + 1

lemma differentiableAt_ratio (b : AbBlock) (v : Fin b.g → ℂ) (j : Fin b.g) {s : ℂ}
    (hs : b.θ (s • v) b.i₀ ≠ 0) : DifferentiableAt ℂ (fun s : ℂ => ratioMap b (s • v) j) s := by
  have hc : ∀ c, DifferentiableAt ℂ (fun s : ℂ => b.θ (s • v) c) s := fun c =>
    ((differentiable_pi.mp (differentiable_θ b) c) _).comp s (differentiableAt_id.smul_const v)
  exact (hc (b.is j)).div (hc b.i₀) hs

lemma differentiableAt_FA {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) (t v : Tan d₀ d₁ B) {s : ℂ}
    (hs : ∀ k, (B k).θ (s • v.2.2 k) (B k).i₀ ≠ 0) : DifferentiableAt ℂ (FA μs p t v) s := by
  have hg : ∀ f, DifferentiableAt ℂ (gA t v f) s := by
    intro f
    rcases f with i | j | ⟨k, j⟩
    · change DifferentiableAt ℂ (fun s => t.1 i + v.1 i * s) s; fun_prop
    · change DifferentiableAt ℂ (fun s => Complex.exp (t.2.1 j) * Complex.exp (v.2.1 j * s)) s; fun_prop
    · exact differentiableAt_ratio (B k) (v.2.2 k) j (hs k)
  unfold FA
  refine DifferentiableAt.fun_sum fun l _ => (differentiableAt_const _).mul ?_
  exact DifferentiableAt.fun_finsetProd fun f _ => (hg f).pow _

lemma analyticAt_uA (κ lam : Fin m → ℂ) (v : Tan d₀ d₁ B) : AnalyticAt ℂ (uA D κ lam v) 0 := by
  unfold uA
  have hθ : ∀ k, AnalyticAt ℂ (fun s : ℂ => (B k).θ (s • v.2.2 k) (B k).i₀) 0 := fun k =>
    ((analyticAt_pi_iff.mp ((B k).θ_analytic _)) (B k).i₀).comp
      (analyticAt_id.smul analyticAt_const)
  have hk : ∀ k ∈ Finset.univ, AnalyticAt ℂ
      (fun s : ℂ => (κ k * Complex.exp (lam k * s) * (B k).θ (s • v.2.2 k) (B k).i₀) ^ D) 0 := by
    intro k _
    have h1 : AnalyticAt ℂ (fun s : ℂ => Complex.exp (lam k * s)) 0 := by fun_prop
    exact ((analyticAt_const.mul h1).mul (hθ k)).pow D
  have := Finset.analyticAt_prod Finset.univ hk
  convert this using 1
  funext s; simp [Finset.prod_apply]

set_option maxHeartbeats 2000000 in
-- one long proof with many size bounds
/-- **Lemma U along one line.** -/
theorem lemmaU_line {ι : K →+* ℂ} (An : ∀ k, AbBlockAn (B k)) (Tay : ∀ k, AbBlockTay (B k) ι) {L : ℕ}
    (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) {A₀ A₁ S T μ τ : ℕ} {Bp U : ℝ}
    (hα : ∀ l i, (μs l).α i ≤ A₀) (hβ : ∀ l j, (μs l).β j ≤ A₁) (hp : ∀ l, |(p l : ℝ)| ≤ Real.exp Bp)
    (hBp : 0 ≤ Bp) (hS : 1 ≤ S) (t v : Tan d₀ d₁ B) (ht2 : ∀ k, t.2.2 k ∈ (An k).lat)
    {H : ℝ} {d : ℕ} (hH : 1 ≤ H) (hd : 1 ≤ d)
    (ht : ∀ i, Sz ι (S * (μ + 1) * H) d (t.1 i))
    (he : ∀ j, Sz ι (H ^ (μ * S)) (d ^ (μ * S)) (Complex.exp (t.2.1 j)))
    (hv0 : ∀ i, Sz ι ((T + 1) * (τ + 1) * H) d (v.1 i))
    (hv1 : ∀ j, Sz ι ((T + 1) * (τ + 1) * H) d (v.2.1 j))
    (hv2 : ∀ k j, Sz ι ((T + 1) * (τ + 1) * H) d (v.2.2 k j))
    {Ys Wn ρ₀ θm : ℝ} (htn : ‖t‖ ≤ S * Ys) (hvn : ‖v‖ ≤ T * Wn) (hYs : 0 ≤ Ys) (hWn : 0 ≤ Wn)
    (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ ≤ 1) (hθm : 0 < θm) (hθm1 : θm ≤ 1)
    (hθ : ∀ k (z : Fin (B k).g → ℂ), ‖z‖ ≤ ρ₀ → θm ≤ ‖(B k).θ z (B k).i₀‖)
    (hsmall : ∀ s : ℂ, ‖s‖ ≤ ρ₀ / (1 + T * Wn) → ‖PsiA μs p (t + s • v)‖ ≤ Real.exp (-U))
    (hU : kLU (d₀ := d₀) (d₁ := d₁) An Tay μ τ H d Ys Wn ρ₀ θm * budU Bp L A₀ A₁ D S T ≤ U) :
    ∀ j < T, iteratedDeriv j (fun s : ℂ => PsiA μs p (t + s • v)) 0 = 0 := by
  classical
  set Bud := budU Bp L A₀ A₁ D S T with hBud
  have hBud0 : 0 < Bud := bud_pos hS hBp
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hcQ0 := cQU_nonneg An
  -- quasi-periodicity at `t`
  choose κ Lk hκ0 hκ hκi hLk hθq using fun k => (An k).qp (t.2.2 k) (ht2 k)
  set lam : Fin m → ℂ := fun k => Lk k (v.2.2 k) with hlam
  have hθline : ∀ k (s : ℂ), (B k).θ (t.2.2 k + s • v.2.2 k) =
      (κ k * Complex.exp (lam k * s)) • (B k).θ (s • v.2.2 k) := by
    intro k s
    rw [add_comm, hθq k, map_smul, smul_eq_mul, mul_comm s]
  -- the radius
  set ρ : ℝ := ρ₀ / (1 + T * Wn) with hρdef
  have h1TW : 0 < 1 + T * Wn := by positivity
  have hρ : 0 < ρ := div_pos hρ₀ h1TW
  have hsv : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, ‖s • v.2.2 k‖ ≤ ρ₀ := by
    intro s hs k
    rw [norm_smul]
    calc ‖s‖ * ‖v.2.2 k‖ ≤ ρ * (T * Wn) :=
          mul_le_mul hs ((norm_z_le v k).trans hvn) (norm_nonneg _) hρ.le
      _ ≤ ρ * (1 + T * Wn) := by gcongr; linarith
      _ = ρ₀ := by rw [hρdef]; field_simp
  have hne : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, (B k).θ (s • v.2.2 k) (B k).i₀ ≠ 0 := fun s hs k h0 => by
    have := hθ k _ (hsv s hs k); rw [h0, norm_zero] at this; linarith
  -- the normalised function and its Taylor coefficients
  set F := FA μs p t v with hFdef
  set Hv : ℝ := (T + 1) * (τ + 1) * H with hHv
  have hHv1 : 1 ≤ Hv := by
    have : (1 : ℝ) ≤ (T + 1) * (τ + 1) := one_le_mul_of_one_le_of_one_le (by linarith) (by
      linarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)])
    exact one_le_mul_of_one_le_of_one_le this hH
  have hKS := ks_FA Tay μs p hα hβ t v hHv1 ht he hv0 hv1 hv2
  set NN := NfA (d₀ := d₀) (d₁ := d₁) (B := B) A₀ A₁ D
  set A' : ℝ := ((L : ℝ) + 1) * Real.exp Bp * (2 ^ (∑ f, NN f) *
    ∏ f, AfA (d₀ := d₀) (d₁ := d₁) (S * (μ + 1) * H) (H ^ (μ * S)) Tay f ^ NN f)
  have hP0 : 0 ≤ 2 ^ (∑ f, NN f) *
      ∏ f, AfA (d₀ := d₀) (d₁ := d₁) (S * (μ + 1) * H) (H ^ (μ * S)) Tay f ^ NN f := by
    refine mul_nonneg (by positivity) (prod_nonneg fun f _ => pow_nonneg ?_ _)
    rcases f with i | j | ⟨k, j⟩
    · exact zero_le_one.trans (le_max_left _ _)
    · exact zero_le_one.trans (le_max_left _ _)
    · exact zero_le_one.trans (Tay k).one_le_A
  have hP1 : 1 ≤ 2 ^ (∑ f, NN f) *
      ∏ f, AfA (d₀ := d₀) (d₁ := d₁) (S * (μ + 1) * H) (H ^ (μ * S)) Tay f ^ NN f := by
    refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) ?_
    have hf : ∀ f, 1 ≤ AfA (d₀ := d₀) (d₁ := d₁) (S * (μ + 1) * H) (H ^ (μ * S)) Tay f := by
      intro f
      rcases f with i | j | ⟨k, j⟩
      · exact le_max_left _ _
      · exact le_max_left _ _
      · exact (Tay k).one_le_A
    calc (1 : ℝ) = ∏ _f : RVarA d₀ d₁ B, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) fun f _ => one_le_pow₀ (hf f)
  have hsump : ∑ l, |(p l : ℝ)| ≤ ((L : ℝ) + 1) * Real.exp Bp := by
    calc ∑ l, |(p l : ℝ)| ≤ ∑ _l : Fin L, Real.exp Bp := sum_le_sum fun l _ => hp l
      _ = L * Real.exp Bp := by simp
      _ ≤ ((L : ℝ) + 1) * Real.exp Bp := by gcongr; linarith
  have hKS' : KS ι A' (2 * (cBm Tay * Hv))
      (∏ f, efA (d₀ := d₀) (d₁ := d₁) d d (d ^ (μ * S)) Tay f ^ NN f) (d * δm Tay) F := by
    refine hKS.mono ?_ (by have := one_le_cBm Tay; positivity) le_rfl dvd_rfl dvd_rfl
    exact mul_le_mul_of_nonneg_right hsump hP0
  have hA'1 : 1 ≤ A' := by
    have h1 : (1 : ℝ) ≤ ((L : ℝ) + 1) * Real.exp Bp :=
      one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
        (Real.one_le_exp hBp)
    exact one_le_mul_of_one_le_of_one_le h1 hP1
  have hB1 : 1 ≤ 2 * (cBm Tay * Hv) := by
    have := one_le_cBm Tay; nlinarith
  have he1 : 1 ≤ ∏ f, efA (d₀ := d₀) (d₁ := d₁) d d (d ^ (μ * S)) Tay f ^ NN f := by
    refine Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun f _ => pow_ne_zero _ ?_)
    rcases f with i | j | ⟨k, j⟩
    · change d * d ≠ 0; positivity
    · change d ^ (μ * S) ≠ 0; positivity
    · change (Tay k).E ≠ 0; have := (Tay k).one_le_E; omega
  have hδ1 : 1 ≤ d * δm Tay := Nat.one_le_iff_ne_zero.mpr (by have := one_le_δm Tay; positivity)
  -- the factorisation on the closed disc
  have hfac : ∀ s : ℂ, ‖s‖ ≤ ρ → PsiA μs p (t + s • v) = uA D κ lam v s * F s := fun s hs =>
    PsiA_line_eq μs p t v κ lam hθline s (hne s hs)
  -- differentiability of `F` on the closed disc
  have hdc : DiffContOnCl ℂ F (ball 0 ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball 0 hρ.ne']
    intro s hs
    exact (differentiableAt_FA μs p t v (hne s (mem_closedBall_zero_iff.mp hs))).differentiableWithinAt
  -- the bound on the sphere
  set a₁ : ℝ := cQU An * Ys ^ 2
  set a₂ : ℝ := cQU An * Ys
  set a₃ : ℝ := Real.log (1 / θm)
  have ha₃ : 0 ≤ a₃ := Real.log_nonneg (by rw [le_div_iff₀ hθm]; linarith)
  have hunit : ∀ s : ℂ, ‖s‖ ≤ ρ → ‖uA D κ lam v s‖⁻¹ ≤
      Real.exp (m * D * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) := by
    intro s hs
    unfold uA
    rw [norm_prod, ← prod_inv_distrib]
    have hk : ∀ k ∈ univ, ‖(κ k * Complex.exp (lam k * s) * (B k).θ (s • v.2.2 k) (B k).i₀) ^ D‖⁻¹ ≤
        Real.exp (D * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) := by
      intro k _
      have hωk : ‖t.2.2 k‖ ≤ S * Ys := (norm_z_le t k).trans htn
      have hcq : (An k).cQ ≤ cQU An := cQ_le An k
      have hcq0 := (An k).cQ_nonneg
      have i1 : ‖κ k‖⁻¹ ≤ Real.exp (a₁ * (S : ℝ) ^ 2) := (hκi k).trans (Real.exp_le_exp.mpr (by
        calc (An k).cQ * ‖t.2.2 k‖ ^ 2 ≤ cQU An * (S * Ys) ^ 2 :=
              mul_le_mul hcq (pow_le_pow_left₀ (norm_nonneg _) hωk 2) (by positivity) hcQ0
          _ = a₁ * (S : ℝ) ^ 2 := by ring))
      have i2 : ‖Complex.exp (lam k * s)‖⁻¹ ≤ Real.exp (a₂ * S) := by
        rw [Complex.norm_exp, ← Real.exp_neg]
        apply Real.exp_le_exp.mpr
        have hl : ‖lam k‖ ≤ (An k).cQ * ‖t.2.2 k‖ * ‖v.2.2 k‖ := hLk k _
        have hsvk : ‖s‖ * ‖v.2.2 k‖ ≤ ρ₀ := by rw [← norm_smul]; exact hsv s hs k
        calc -(lam k * s).re ≤ ‖lam k * s‖ := by
              have := Complex.abs_re_le_norm (lam k * s); rw [abs_le] at this; linarith
          _ = ‖lam k‖ * ‖s‖ := norm_mul _ _
          _ ≤ (An k).cQ * ‖t.2.2 k‖ * ‖v.2.2 k‖ * ‖s‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg _)
          _ = (An k).cQ * ‖t.2.2 k‖ * (‖s‖ * ‖v.2.2 k‖) := by ring
          _ ≤ cQU An * (S * Ys) * 1 := by
              refine mul_le_mul (mul_le_mul hcq hωk (norm_nonneg _) hcQ0) (hsvk.trans hρ₀1) (by positivity)
                (by positivity)
          _ = a₂ * S := by ring
      have i3 : ‖(B k).θ (s • v.2.2 k) (B k).i₀‖⁻¹ ≤ Real.exp a₃ := by
        rw [Real.exp_log (by positivity)]
        rw [one_div]
        exact inv_anti₀ hθm (hθ k _ (hsv s hs k))
      rw [norm_pow, norm_mul, norm_mul, ← inv_pow, mul_inv, mul_inv]
      have := exp_mul_exp_le (by positivity) (by positivity) (exp_mul_exp_le (by positivity) (by positivity) i1 i2) i3
      refine (pow_le_pow_left₀ (by positivity) this D).trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul]
    calc ∏ k, ‖(κ k * Complex.exp (lam k * s) * (B k).θ (s • v.2.2 k) (B k).i₀) ^ D‖⁻¹
        ≤ ∏ _k : Fin m, Real.exp (D * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) :=
          prod_le_prod₀ (fun k _ => by positivity) hk
      _ = Real.exp (m * D * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) := by
          rw [prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; ring_nf
  have hM : ∀ z ∈ sphere (0 : ℂ) ρ, ‖F z‖ ≤
      Real.exp (-U) * Real.exp (m * D * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) := by
    intro s hs
    have hs' : ‖s‖ ≤ ρ := (mem_sphere_zero_iff_norm.mp hs).le
    have hu0 : uA D κ lam v s ≠ 0 := by
      unfold uA
      exact prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (mul_ne_zero (mul_ne_zero (hκ0 k)
        (Complex.exp_ne_zero _)) (hne s hs' k))
    have hF : F s = PsiA μs p (t + s • v) / uA D κ lam v s := by
      rw [hfac s hs']; field_simp
    rw [hF, norm_div, div_eq_mul_inv]
    exact mul_le_mul (hsmall s hs') (hunit s hs') (by positivity) (Real.exp_pos _).le
  -- the vanishing of the Taylor coefficients
  -- closed forms of the size data
  have ha₁ : 0 ≤ a₁ := by positivity
  have ha₂ : 0 ≤ a₂ := by positivity
  have hHt : (1 : ℝ) ≤ S * (μ + 1) * H := by
    have : (1 : ℝ) ≤ (μ : ℝ) + 1 := by linarith [(Nat.cast_nonneg μ : (0 : ℝ) ≤ μ)]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hSR this) hH
  have hHe : (1 : ℝ) ≤ H ^ (μ * S) := one_le_pow₀ hH
  have hsum : ∑ f, NN f = d₀ * A₀ + d₁ * A₁ + (∑ k, (B k).g) * D := by
    rw [sum_RVarA]
    simp only [NN, NfA, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum_mul]
  have hprodA : ∏ f, AfA (d₀ := d₀) (d₁ := d₁) (S * (μ + 1) * H) (H ^ (μ * S)) Tay f ^ NN f =
      ((S : ℝ) * ((μ + 1) * H)) ^ (d₀ * A₀) * (H ^ (μ * S)) ^ (d₁ * A₁) * (∏ k, (Tay k).A ^ (B k).g) ^ D := by
    rw [prod_RVarA]
    simp only [NN, AfA, NfA, max_eq_right hHt, max_eq_right hHe]
    have p1 : ∏ _i : Fin d₀, ((S : ℝ) * (μ + 1) * H) ^ A₀ = ((S : ℝ) * ((μ + 1) * H)) ^ (d₀ * A₀) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm A₀, mul_assoc]
    have p2 : ∏ _j : Fin d₁, (H ^ (μ * S)) ^ A₁ = (H ^ (μ * S)) ^ (d₁ * A₁) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm A₁]
    have p3 : ∏ k, ∏ _j : Fin (B k).g, (Tay k).A ^ D = (∏ k, (Tay k).A ^ (B k).g) ^ D := by
      rw [← Finset.prod_pow]
      refine prod_congr rfl fun k _ => ?_
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, ← pow_mul, mul_comm]
    rw [p1, p2, p3]
  have hprodE : ∏ f, efA (d₀ := d₀) (d₁ := d₁) d d (d ^ (μ * S)) Tay f ^ NN f =
      (d * d) ^ (d₀ * A₀) * (d ^ (μ * S)) ^ (d₁ * A₁) * (∏ k, (Tay k).E ^ (B k).g) ^ D := by
    rw [prod_RVarA]
    simp only [NN, efA, NfA]
    have p1 : ∏ _i : Fin d₀, (d * d) ^ A₀ = (d * d) ^ (d₀ * A₀) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm A₀]
    have p2 : ∏ _j : Fin d₁, (d ^ (μ * S)) ^ A₁ = (d ^ (μ * S)) ^ (d₁ * A₁) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm A₁]
    have p3 : ∏ k, ∏ _j : Fin (B k).g, (Tay k).E ^ D = (∏ k, (Tay k).E ^ (B k).g) ^ D := by
      rw [← Finset.prod_pow]
      refine prod_congr rfl fun k _ => ?_
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, ← pow_mul, mul_comm]
    rw [p1, p2, p3]
  have hQ1 : 1 ≤ ∏ k, (Tay k).E ^ (B k).g :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (by
      have := (Tay k).one_le_E; omega))
  have hPA : (1 : ℝ) ≤ ∏ k, (Tay k).A ^ (B k).g := by
    calc (1 : ℝ) = ∏ _k : Fin m, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) fun k _ => one_le_pow₀ (Tay k).one_le_A
  have hc1 : (1 : ℝ) ≤ 2 * cBm Tay * ((τ + 1) * H) := by
    have h1 := one_le_cBm Tay
    have h2 : (1 : ℝ) ≤ (τ : ℝ) + 1 := by linarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)]
    have h3 : (1 : ℝ) ≤ ((τ : ℝ) + 1) * H := one_le_mul_of_one_le_of_one_le h2 hH
    nlinarith
  have hμH : (1 : ℝ) ≤ ((μ : ℝ) + 1) * H :=
    one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg μ : (0 : ℝ) ≤ μ)]) hH
  -- the vanishing of the Taylor coefficients
  have htco : ∀ j < T, tco j F = 0 := by
    intro j hj
    have hjT : j ≤ T := hj.le
    refine tco_eq_zero_of_small hKS' hA'1 hB1 he1 hδ1 hρ hdc hM ?_
    refine small_of_bud (U := U) (KU := m * (a₁ + a₂ + a₃)) (Kρ := 1 + Real.log ((1 + Wn) / ρ₀) / Real.log 2)
      (KX := d₀ * (2 * Real.log d / Real.log 2) + d₁ * μ * Real.log d +
        Real.log ((∏ k, (Tay k).E ^ (B k).g : ℕ) : ℝ) + Real.log ((d * δm Tay : ℕ) : ℝ) / Real.log 2 + 1)
      (KY := 1 + d₀ + d₁ + (∑ k, (B k).g : ℕ) + d₀ * (1 + Real.log ((μ + 1) * H) / Real.log 2) +
        d₁ * μ * Real.log H + Real.log (∏ k, (Tay k).A ^ (B k).g) +
        (1 + Real.log (2 * cBm Tay * ((τ + 1) * H)) / Real.log 2))
      hρ hBud0 (Nat.cast_nonneg _) (by positivity) ?_ ?_ ?_ ?_ ?_
    · rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_left (le_bud_unit hS hBp ha₁ ha₂ ha₃) (Real.exp_pos _).le
    · rw [hρdef, one_div_div]
      exact le_bud_cauchy hS hBp hjT hWn hρ₀ hρ₀1
    · rw [hprodE]
      have e1 := le_bud_e (L := L) (A₀ := A₀) (A₁ := A₁) (D := D) hS hBp (d₀ := d₀) (d₁ := d₁) (μ := μ)
        hjT hd hQ1 hδ1
      refine le_trans (le_of_eq ?_) e1
      push_cast; ring
    · simp only [A']; rw [hsum, hprodA]
      have e2 := le_bud_A (L := L) (A₀ := A₀) (A₁ := A₁) (D := D) hS hBp (d₀ := d₀) (d₁ := d₁)
        (G := ∑ k, (B k).g) (μ := μ) hjT hμH hH hPA hc1
      refine le_trans (le_of_eq ?_) e2
      have : 2 * (cBm Tay * Hv) = 2 * cBm Tay * ((τ + 1) * H) * (T + 1) := by rw [hHv]; ring
      rw [this]
      push_cast; ring
    · refine le_trans (le_of_eq ?_) hU
      unfold kLU; ring
  -- Leibniz
  intro j hj
  have hF0 : ∀ i < T, iteratedDeriv i F 0 = 0 := fun i hi => by
    have h := htco i hi
    unfold tco at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h (by exact_mod_cast i.factorial_ne_zero)
  have hev : (fun s : ℂ => PsiA μs p (t + s • v)) =ᶠ[𝓝 0] (uA D κ lam v) * F := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with s hs
    exact hfac s (mem_ball_zero_iff.mp hs).le
  rw [(hev.iteratedDeriv j).eq_of_nhds,
    iteratedDeriv_mul (analyticAt_uA κ lam v).contDiffAt hKS'.1.contDiffAt]
  refine sum_eq_zero fun i hi => ?_
  rw [hF0 (j - i) (lt_of_le_of_lt (Nat.sub_le j i) hj), mul_zero]

end LSG.AuxA
