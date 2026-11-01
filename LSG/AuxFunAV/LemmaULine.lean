/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunAV.LemmaUFac
import LSG.AuxFunA.LemmaULine

/-!
# M2.6.5b: Lemma U for `MonoAV` along one line

**`lemmaU_lineV`**, the analogue of `LSG.AuxA.lemmaU_line`. Let `t` have block parts in `lat` and coordinates (incl. the
fibre part `s′ = sPart M t`) of size `(S(μ+1)H, d)`, `(H^{μS}, d^{μS})`, let `v` have coordinates of size
`((T+1)(τ+1)H, d)`, `M` entries of size `(H, d)`, `‖t‖ ≤ S Y`, `‖v‖ ≤ T W`. If `|Ψ(t + s v)| ≤ e^{−U}` for
`|s| ≤ ρ₀/(1 + T W)` and `U ≥ K · Bud(D + F)` (`kLUV`), then all derivatives of order `< T` of `s ↦ Ψ(t + s v)` vanish
at `0`.

The proof is `lemmaU_line`'s, with the factorisation `PsiAV_line_eq` (unit of exponent `D + F`), the sizes `ks_FAV`
(`G + r` block-type factors of degree `≤ D + F`), and one extra budget term `le_bud_S` for the fibre factors, whose
size grows like `S` (the fibre part `s′` of `t` is a natural combination of the generators).
-/

open Complex Finset Module Metric
open scoped ContDiff Topology

noncomputable section

namespace LSG.AuxAV

open LSG.MEBV LSG.AuxA LSG.Aux
open LSG.MEB (AbBlock)

variable {K : Type*} [Field K] [NumberField K]
variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {D F : ℕ}

/-- **The fibre budget term**: `(S h)^{r D} ≤ exp (r (1 + log h) Bud)`. -/
lemma le_bud_S {Bp : ℝ} {L A₀ A₁ D' S T : ℕ} (hS : 1 ≤ S) (hBp : 0 ≤ Bp) {r : ℕ} {h : ℝ} (hh : 1 ≤ h) :
    ((S : ℝ) * h) ^ (r * D') ≤ Real.exp (r * (1 + Real.log h) * budU Bp L A₀ A₁ D' S T) := by
  obtain ⟨-, -, -, -, -, hDS, hD, -, -, -⟩ :=
    le_bud (L := L) (A₀ := A₀) (A₁ := A₁) (D := D') (T := T) hS hBp
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hlS : Real.log S ≤ (S : ℝ) ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < S by linarith); nlinarith
  have hlS0 := Real.log_nonneg hSR
  have hlh := Real.log_nonneg hh
  have hD0 : (0 : ℝ) ≤ D' := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  rw [← Real.exp_log (by positivity : (0 : ℝ) < ((S : ℝ) * h) ^ (r * D')), Real.log_pow,
    Real.log_mul (by positivity) (by positivity)]
  apply Real.exp_le_exp.mpr
  have h1 : (D' : ℝ) * Real.log S ≤ budU Bp L A₀ A₁ D' S T :=
    (mul_le_mul_of_nonneg_left hlS hD0).trans hDS
  have h2 : (D' : ℝ) * Real.log h ≤ Real.log h * budU Bp L A₀ A₁ D' S T := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hD hlh
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h1 hr0, mul_le_mul_of_nonneg_left h2 hr0]

lemma prod_RVarAV {M : Type*} [CommMonoid M] (Fn : RVarAV d₀ d₁ r B → M) :
    ∏ f, Fn f = (∏ i, Fn (.inl (.inl i))) * (∏ j, Fn (.inl (.inr (.inl j)))) *
      (∏ k, ∏ j, Fn (.inl (.inr (.inr ⟨k, j⟩)))) * ∏ i, Fn (.inr i) := by
  rw [Fintype.prod_sum_type, prod_RVarA]

lemma sum_RVarAV {M : Type*} [AddCommMonoid M] (Fn : RVarAV d₀ d₁ r B → M) :
    ∑ f, Fn f = (∑ i, Fn (.inl (.inl i))) + (∑ j, Fn (.inl (.inr (.inl j)))) +
      (∑ k, ∑ j, Fn (.inl (.inr (.inr ⟨k, j⟩)))) + ∑ i, Fn (.inr i) := by
  rw [Fintype.sum_sum_type, sum_RVarA]

/-- The helper size of the fibre factors: `(μ + 1) H + m H A_m`. -/
def hFib {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) (μ : ℕ) (H : ℝ) : ℝ :=
  (μ + 1) * H + m * (H * Am Tay)

/-- The constant of Lemma U along a line. -/
def kLUV {ι : K →+* ℂ} (An : ∀ k, VBlockAn (B k)) (Tay : ∀ k, VBlockTay (B k) ι) (μ τ : ℕ) (H : ℝ) (d : ℕ)
    (Ys Wn ρ₀ θm : ℝ) : ℝ :=
  m * (cQU (fun k => (An k).an) * Ys ^ 2 + cQU (fun k => (An k).an) * Ys + Real.log (1 / θm)) +
    (1 + Real.log ((1 + Wn) / ρ₀) / Real.log 2) +
    finrank ℚ K * ((d₀ * (2 * Real.log d / Real.log 2) + d₁ * μ * Real.log d +
        Real.log (((∏ k, (Tay k).E ^ (B k).g) * ((d * d) * (d * Em Tay)) ^ r : ℕ) : ℝ) +
        Real.log ((d * δm (tayB Tay) : ℕ) : ℝ) / Real.log 2 + 1) +
      ((1 + d₀ + d₁ + ((∑ k, (B k).g) + r : ℕ) + d₀ * (1 + Real.log ((μ + 1) * H) / Real.log 2) +
        d₁ * μ * Real.log H + Real.log (∏ k, (Tay k).A ^ (B k).g) +
        (1 + Real.log (2 * cBm (tayB Tay) * ((τ + 1) * H)) / Real.log 2)) +
        r * (1 + Real.log (hFib Tay μ H)))) + 1

lemma differentiableAt_tauV (b : VBlock) (v : Fin b.g → ℂ) {s : ℂ} (hs : b.base.θ (s • v) b.base.i₀ ≠ 0) :
    DifferentiableAt ℂ (fun s : ℂ => tauV b (s • v)) s := by
  have hc : DifferentiableAt ℂ (fun s : ℂ => b.base.θ (s • v) b.base.i₀) s :=
    ((differentiable_pi.mp (differentiable_θ b.base) _) _).comp s (differentiableAt_id.smul_const v)
  have hT : DifferentiableAt ℂ (fun s : ℂ => b.T (s • v) 0 b.t₀) s :=
    ((differentiable_T b 0 b.t₀) _).comp s (differentiableAt_id.smul_const v)
  exact hT.div hc hs

lemma differentiableAt_FAV (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) (t v : TanAV d₀ d₁ r B) {s : ℂ}
    (hs : ∀ k, (B k).base.θ (s • v.2.2.1 k) (B k).base.i₀ ≠ 0) : DifferentiableAt ℂ (FAV M νs p t v) s := by
  have hg : ∀ f, DifferentiableAt ℂ (gAV M t v f) s := by
    intro f
    rcases f with (i | j | ⟨k, j⟩) | i
    · change DifferentiableAt ℂ (fun s => t.1 i + v.1 i * s) s; fun_prop
    · change DifferentiableAt ℂ (fun s => Complex.exp (t.2.1 j) * Complex.exp (v.2.1 j * s)) s; fun_prop
    · exact differentiableAt_ratio (B k).base (v.2.2.1 k) j (hs k)
    · change DifferentiableAt ℂ (fun s : ℂ => (sPart M t + s • v.2.2.2) i +
        ∑ j, M i j * tauV (B j) ((s • v.2.2.1) j)) s
      refine DifferentiableAt.add (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; fun_prop) ?_
      exact DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul
        (differentiableAt_tauV (B j) (v.2.2.1 j) (hs j))
  unfold FAV
  refine DifferentiableAt.fun_sum fun l _ => (differentiableAt_const _).mul ?_
  exact DifferentiableAt.fun_finsetProd fun f _ => (hg f).pow _

set_option maxHeartbeats 4000000 in
-- one long proof with many size bounds
/-- **Lemma U along one line.** -/
theorem lemmaU_lineV {ι : K →+* ℂ} (An : ∀ k, VBlockAn (B k)) (Tay : ∀ k, VBlockTay (B k) ι)
    (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ}
    (νs : Fin L → MonoAV d₀ d₁ r B D F) (p : Fin L → ℤ) {A₀ A₁ S T μ τ : ℕ} {Bp U : ℝ}
    (hα : ∀ l i, (νs l).μ.α i ≤ A₀) (hβ : ∀ l j, (νs l).μ.β j ≤ A₁) (hp : ∀ l, |(p l : ℝ)| ≤ Real.exp Bp)
    (hBp : 0 ≤ Bp) (hS : 1 ≤ S) (t v : TanAV d₀ d₁ r B) (ht2 : ∀ k, t.2.2.1 k ∈ (An k).an.lat)
    {H : ℝ} {d : ℕ} (hH : 1 ≤ H) (hd : 1 ≤ d)
    (ht : ∀ i, Sz ι (S * (μ + 1) * H) d (t.1 i))
    (he : ∀ j, Sz ι (H ^ (μ * S)) (d ^ (μ * S)) (Complex.exp (t.2.1 j)))
    (hts : ∀ i, Sz ι (S * (μ + 1) * H) d (sPart M t i))
    (hv0 : ∀ i, Sz ι ((T + 1) * (τ + 1) * H) d (v.1 i))
    (hv1 : ∀ j, Sz ι ((T + 1) * (τ + 1) * H) d (v.2.1 j))
    (hv2 : ∀ k j, Sz ι ((T + 1) * (τ + 1) * H) d (v.2.2.1 k j))
    (hv3 : ∀ i, Sz ι ((T + 1) * (τ + 1) * H) d (v.2.2.2 i))
    (hM : ∀ i j, Sz ι H d (M i j))
    {Ys Wn ρ₀ θm : ℝ} (htn : ‖t‖ ≤ S * Ys) (hvn : ‖v‖ ≤ T * Wn) (hYs : 0 ≤ Ys) (hWn : 0 ≤ Wn)
    (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ ≤ 1) (hθm : 0 < θm) (hθm1 : θm ≤ 1)
    (hθ : ∀ k (z : Fin (B k).g → ℂ), ‖z‖ ≤ ρ₀ → θm ≤ ‖(B k).base.θ z (B k).base.i₀‖)
    (hsmall : ∀ s : ℂ, ‖s‖ ≤ ρ₀ / (1 + T * Wn) → ‖PsiAV M νs p (t + s • v)‖ ≤ Real.exp (-U))
    (hU : kLUV (d₀ := d₀) (d₁ := d₁) (r := r) An Tay μ τ H d Ys Wn ρ₀ θm *
      budU Bp L A₀ A₁ (D + F) S T ≤ U) :
    ∀ j < T, iteratedDeriv j (fun s : ℂ => PsiAV M νs p (t + s • v)) 0 = 0 := by
  classical
  set D₂ := D + F with hD₂
  set Bud := budU Bp L A₀ A₁ D₂ S T with hBud
  have hBud0 : 0 < Bud := bud_pos hS hBp
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  set An' : ∀ k, AbBlockAn (Bb B k) := fun k => (An k).an
  have hcQ0 := cQU_nonneg An'
  -- quasi-periodicity at `t`
  choose κ Lk hκ0 hκ hκi hLk hθq using fun k => (An k).an.qp (t.2.2.1 k) (ht2 k)
  set lam : Fin m → ℂ := fun k => Lk k (v.2.2.1 k) with hlam
  have hθline : ∀ k (s : ℂ), (B k).base.θ (t.2.2.1 k + s • v.2.2.1 k) =
      (κ k * Complex.exp (lam k * s)) • (B k).base.θ (s • v.2.2.1 k) := by
    intro k s
    rw [add_comm, hθq k, map_smul, smul_eq_mul, mul_comm s]
  have hTline : ∀ k (s : ℂ), (B k).T (s • v.2.2.1 k + t.2.2.1 k) ((B k).η (t.2.2.1 k)) =
      (κ k * Complex.exp (lam k * s)) • (B k).T (s • v.2.2.1 k) 0 := by
    intro k s
    have h := VBlockAn.T_qp (b := B k) ((An k).an.lat_le (ht2 k)) (hθq k) (s • v.2.2.1 k) 0
    rw [zero_add] at h
    rw [h, map_smul, smul_eq_mul, mul_comm s]
  -- the radius
  set ρ : ℝ := ρ₀ / (1 + T * Wn) with hρdef
  have h1TW : 0 < 1 + T * Wn := by positivity
  have hρ : 0 < ρ := div_pos hρ₀ h1TW
  have hsv : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, ‖s • v.2.2.1 k‖ ≤ ρ₀ := by
    intro s hs k
    rw [norm_smul]
    calc ‖s‖ * ‖v.2.2.1 k‖ ≤ ρ * (T * Wn) :=
          mul_le_mul hs ((norm_zV_le v k).trans hvn) (norm_nonneg _) hρ.le
      _ ≤ ρ * (1 + T * Wn) := by gcongr; linarith
      _ = ρ₀ := by rw [hρdef]; field_simp
  have hne : ∀ s : ℂ, ‖s‖ ≤ ρ → ∀ k, (B k).base.θ (s • v.2.2.1 k) (B k).base.i₀ ≠ 0 := fun s hs k h0 => by
    have := hθ k _ (hsv s hs k); rw [h0, norm_zero] at this; linarith
  -- the normalised function and its Taylor coefficients
  set Fn := FAV M νs p t v with hFdef
  set Hv : ℝ := (T + 1) * (τ + 1) * H with hHv
  have hHv1 : 1 ≤ Hv := by
    have : (1 : ℝ) ≤ (T + 1) * (τ + 1) := one_le_mul_of_one_le_of_one_le (by linarith) (by
      linarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)])
    exact one_le_mul_of_one_le_of_one_le this hH
  set Ht : ℝ := S * (μ + 1) * H with hHtdef
  set Hf : ℝ := max 1 Ht + m * (H * Am Tay) with hHf
  set ef : ℕ := (d * d) * (d * Em Tay) with hef
  have hKS := ks_FAV Tay M νs p hα hβ t v hHv1 (by linarith) ht he hts hv0 hv1 hv2 hv3 hM
  set NN := NfAV (d₀ := d₀) (d₁ := d₁) (r := r) (B := B) A₀ A₁ D₂
  set A' : ℝ := ((L : ℝ) + 1) * Real.exp Bp * (2 ^ (∑ f, NN f) *
    ∏ f, AfAV (d₀ := d₀) (d₁ := d₁) (r := r) Ht (H ^ (μ * S)) Hf Tay f ^ NN f)
  have hAf1 : ∀ f, 1 ≤ AfAV (d₀ := d₀) (d₁ := d₁) (r := r) Ht (H ^ (μ * S)) Hf Tay f := by
    intro f
    rcases f with (i | j | ⟨k, j⟩) | i
    · exact le_max_left _ _
    · exact le_max_left _ _
    · exact (Tay k).one_le_A
    · have := Am_nonneg Tay
      have : (1 : ℝ) ≤ max 1 Ht := le_max_left _ _
      change 1 ≤ max 1 Ht + m * (H * Am Tay)
      have : 0 ≤ (m : ℝ) * (H * Am Tay) := by positivity
      linarith
  have hP0 : 0 ≤ 2 ^ (∑ f, NN f) *
      ∏ f, AfAV (d₀ := d₀) (d₁ := d₁) (r := r) Ht (H ^ (μ * S)) Hf Tay f ^ NN f :=
    mul_nonneg (by positivity) (prod_nonneg fun f _ => pow_nonneg (zero_le_one.trans (hAf1 f)) _)
  have hP1 : 1 ≤ 2 ^ (∑ f, NN f) *
      ∏ f, AfAV (d₀ := d₀) (d₁ := d₁) (r := r) Ht (H ^ (μ * S)) Hf Tay f ^ NN f := by
    refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) ?_
    calc (1 : ℝ) = ∏ _f : RVarAV d₀ d₁ r B, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) fun f _ => one_le_pow₀ (hAf1 f)
  have hsump : ∑ l, |(p l : ℝ)| ≤ ((L : ℝ) + 1) * Real.exp Bp := by
    calc ∑ l, |(p l : ℝ)| ≤ ∑ _l : Fin L, Real.exp Bp := sum_le_sum fun l _ => hp l
      _ = L * Real.exp Bp := by simp
      _ ≤ ((L : ℝ) + 1) * Real.exp Bp := by gcongr; linarith
  have hKS' : KS ι A' (2 * (cBm (tayB Tay) * Hv))
      (∏ f, efAV (d₀ := d₀) (d₁ := d₁) (r := r) d d (d ^ (μ * S)) ef Tay f ^ NN f)
      (d * δm (tayB Tay)) Fn := by
    refine hKS.mono ?_ (by have := one_le_cBm (tayB Tay); positivity) le_rfl dvd_rfl dvd_rfl
    exact mul_le_mul_of_nonneg_right hsump hP0
  have hA'1 : 1 ≤ A' := by
    have h1 : (1 : ℝ) ≤ ((L : ℝ) + 1) * Real.exp Bp :=
      one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
        (Real.one_le_exp hBp)
    exact one_le_mul_of_one_le_of_one_le h1 hP1
  have hB1 : 1 ≤ 2 * (cBm (tayB Tay) * Hv) := by
    have := one_le_cBm (tayB Tay); nlinarith
  have hEm := one_le_Em Tay
  have he1 : 1 ≤ ∏ f, efAV (d₀ := d₀) (d₁ := d₁) (r := r) d d (d ^ (μ * S)) ef Tay f ^ NN f := by
    refine Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun f _ => pow_ne_zero _ ?_)
    rcases f with (i | j | ⟨k, j⟩) | i
    · change d * d ≠ 0; positivity
    · change d ^ (μ * S) ≠ 0; positivity
    · change (Tay k).E ≠ 0; have := (Tay k).one_le_E; omega
    · change (d * d) * (d * Em Tay) ≠ 0; have : Em Tay ≠ 0 := by omega
      positivity
  have hδ1 : 1 ≤ d * δm (tayB Tay) := Nat.one_le_iff_ne_zero.mpr (by have := one_le_δm (tayB Tay); positivity)
  -- the factorisation on the closed disc
  have hfac : ∀ s : ℂ, ‖s‖ ≤ ρ → PsiAV M νs p (t + s • v) = uA D₂ κ lam (piA v) s * Fn s := fun s hs =>
    PsiAV_line_eq M νs p t v κ lam hθline hTline s (hne s hs)
  have hdc : DiffContOnCl ℂ Fn (ball 0 ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball 0 hρ.ne']
    intro s hs
    exact (differentiableAt_FAV M νs p t v (hne s (mem_closedBall_zero_iff.mp hs))).differentiableWithinAt
  -- the bound on the sphere
  set a₁ : ℝ := cQU An' * Ys ^ 2
  set a₂ : ℝ := cQU An' * Ys
  set a₃ : ℝ := Real.log (1 / θm)
  have ha₃ : 0 ≤ a₃ := Real.log_nonneg (by rw [le_div_iff₀ hθm]; linarith)
  have hunit : ∀ s : ℂ, ‖s‖ ≤ ρ → ‖uA D₂ κ lam (piA v) s‖⁻¹ ≤
      Real.exp (m * D₂ * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) := by
    intro s hs
    change ‖∏ k, (κ k * Complex.exp (lam k * s) * (B k).base.θ (s • v.2.2.1 k) (B k).base.i₀) ^ D₂‖⁻¹ ≤ _
    rw [norm_prod, ← prod_inv_distrib]
    have hk : ∀ k ∈ univ, ‖(κ k * Complex.exp (lam k * s) * (B k).base.θ (s • v.2.2.1 k) (B k).base.i₀) ^ D₂‖⁻¹ ≤
        Real.exp (D₂ * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) := by
      intro k _
      have hωk : ‖t.2.2.1 k‖ ≤ S * Ys := (norm_zV_le t k).trans htn
      have hcq : (An k).an.cQ ≤ cQU An' := cQ_le An' k
      have hcq0 := (An k).an.cQ_nonneg
      have i1 : ‖κ k‖⁻¹ ≤ Real.exp (a₁ * (S : ℝ) ^ 2) := (hκi k).trans (Real.exp_le_exp.mpr (by
        calc (An k).an.cQ * ‖t.2.2.1 k‖ ^ 2 ≤ cQU An' * (S * Ys) ^ 2 :=
              mul_le_mul hcq (pow_le_pow_left₀ (norm_nonneg _) hωk 2) (by positivity) hcQ0
          _ = a₁ * (S : ℝ) ^ 2 := by ring))
      have i2 : ‖Complex.exp (lam k * s)‖⁻¹ ≤ Real.exp (a₂ * S) := by
        rw [Complex.norm_exp, ← Real.exp_neg]
        apply Real.exp_le_exp.mpr
        have hl : ‖lam k‖ ≤ (An k).an.cQ * ‖t.2.2.1 k‖ * ‖v.2.2.1 k‖ := hLk k _
        have hsvk : ‖s‖ * ‖v.2.2.1 k‖ ≤ ρ₀ := by rw [← norm_smul]; exact hsv s hs k
        calc -(lam k * s).re ≤ ‖lam k * s‖ := by
              have := Complex.abs_re_le_norm (lam k * s); rw [abs_le] at this; linarith
          _ = ‖lam k‖ * ‖s‖ := norm_mul _ _
          _ ≤ (An k).an.cQ * ‖t.2.2.1 k‖ * ‖v.2.2.1 k‖ * ‖s‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg _)
          _ = (An k).an.cQ * ‖t.2.2.1 k‖ * (‖s‖ * ‖v.2.2.1 k‖) := by ring
          _ ≤ cQU An' * (S * Ys) * 1 := by
              refine mul_le_mul (mul_le_mul hcq hωk (norm_nonneg _) hcQ0) (hsvk.trans hρ₀1) (by positivity)
                (by positivity)
          _ = a₂ * S := by ring
      have i3 : ‖(B k).base.θ (s • v.2.2.1 k) (B k).base.i₀‖⁻¹ ≤ Real.exp a₃ := by
        rw [Real.exp_log (by positivity)]
        rw [one_div]
        exact inv_anti₀ hθm (hθ k _ (hsv s hs k))
      rw [norm_pow, norm_mul, norm_mul, ← inv_pow, mul_inv, mul_inv]
      have := exp_mul_exp_le (by positivity) (by positivity)
        (exp_mul_exp_le (by positivity) (by positivity) i1 i2) i3
      refine (pow_le_pow_left₀ (by positivity) this D₂).trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul]
    calc ∏ k, ‖(κ k * Complex.exp (lam k * s) * (B k).base.θ (s • v.2.2.1 k) (B k).base.i₀) ^ D₂‖⁻¹
        ≤ ∏ _k : Fin m, Real.exp (D₂ * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) :=
          prod_le_prod₀ (fun k _ => by positivity) hk
      _ = Real.exp (m * D₂ * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) := by
          rw [prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; ring_nf
  have hMb : ∀ z ∈ sphere (0 : ℂ) ρ, ‖Fn z‖ ≤
      Real.exp (-U) * Real.exp (m * D₂ * (a₁ * (S : ℝ) ^ 2 + a₂ * S + a₃)) := by
    intro s hs
    have hs' : ‖s‖ ≤ ρ := (mem_sphere_zero_iff_norm.mp hs).le
    have hu0 : uA D₂ κ lam (piA v) s ≠ 0 := by
      change ∏ k, (κ k * Complex.exp (lam k * s) * (B k).base.θ (s • v.2.2.1 k) (B k).base.i₀) ^ D₂ ≠ 0
      exact prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (mul_ne_zero (mul_ne_zero (hκ0 k)
        (Complex.exp_ne_zero _)) (hne s hs' k))
    have hF : Fn s = PsiAV M νs p (t + s • v) / uA D₂ κ lam (piA v) s := by
      rw [hfac s hs']; field_simp
    rw [hF, norm_div, div_eq_mul_inv]
    exact mul_le_mul (hsmall s hs') (hunit s hs') (by positivity) (Real.exp_pos _).le
  -- closed forms of the size data
  have ha₁ : 0 ≤ a₁ := by positivity
  have ha₂ : 0 ≤ a₂ := by positivity
  have hμ1 : (1 : ℝ) ≤ (μ : ℝ) + 1 := by linarith [(Nat.cast_nonneg μ : (0 : ℝ) ≤ μ)]
  have hHt : (1 : ℝ) ≤ Ht := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hSR hμ1) hH
  have hHe : (1 : ℝ) ≤ H ^ (μ * S) := one_le_pow₀ hH
  have hG : ∑ k, (B k).g = ∑ k, (Bb B k).g := rfl
  have hsum : ∑ f, NN f = d₀ * A₀ + d₁ * A₁ + ((∑ k, (B k).g) + r) * D₂ := by
    rw [sum_RVarAV]
    simp only [NN, NfAV, NfA, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← sum_mul]
    simp only [Bb]; ring
  have hH0 : 0 ≤ H := by linarith
  have hhF1 : 1 ≤ hFib Tay μ H := by
    have h1 : 0 ≤ (m : ℝ) * (H * Am Tay) := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hH0 (Am_nonneg Tay))
    have : 1 ≤ ((μ : ℝ) + 1) * H := one_le_mul_of_one_le_of_one_le hμ1 hH
    unfold hFib; linarith
  have hHfS : Hf ≤ S * hFib Tay μ H := by
    have hAm := Am_nonneg Tay
    rw [hHf, max_eq_right hHt, hHtdef, hFib]
    have : (m : ℝ) * (H * Am Tay) ≤ S * (m * (H * Am Tay)) :=
      le_mul_of_one_le_left (by positivity) hSR
    nlinarith
  have hprodA : ∏ f, AfAV (d₀ := d₀) (d₁ := d₁) (r := r) Ht (H ^ (μ * S)) Hf Tay f ^ NN f ≤
      ((S : ℝ) * ((μ + 1) * H)) ^ (d₀ * A₀) * (H ^ (μ * S)) ^ (d₁ * A₁) * (∏ k, (Tay k).A ^ (B k).g) ^ D₂ *
        ((S : ℝ) * hFib Tay μ H) ^ (r * D₂) := by
    rw [prod_RVarAV]
    simp only [NN, AfAV, AfA, NfAV, NfA, max_eq_right hHt, max_eq_right hHe]
    have p1 : ∏ _i : Fin d₀, Ht ^ A₀ = ((S : ℝ) * ((μ + 1) * H)) ^ (d₀ * A₀) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm A₀, hHtdef, mul_assoc]
    have p2 : ∏ _j : Fin d₁, (H ^ (μ * S)) ^ A₁ = (H ^ (μ * S)) ^ (d₁ * A₁) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm A₁]
    have p3 : ∏ k, ∏ _j : Fin (Bb B k).g, (tayB Tay k).A ^ D₂ = (∏ k, (Tay k).A ^ (B k).g) ^ D₂ := by
      rw [← Finset.prod_pow]
      refine prod_congr rfl fun k _ => ?_
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, ← pow_mul, mul_comm]; rfl
    have p4 : ∏ _i : Fin r, Hf ^ D₂ ≤ ((S : ℝ) * hFib Tay μ H) ^ (r * D₂) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm D₂]
      have hHf0 : 0 ≤ Hf := by
        have h1 := le_max_left 1 Ht
        have h2 : 0 ≤ (m : ℝ) * (H * Am Tay) := by have := Am_nonneg Tay; positivity
        rw [hHf]; linarith
      exact pow_le_pow_left₀ hHf0 hHfS _
    rw [p1, p2, p3]
    have hA0 : (0 : ℝ) ≤ ∏ k, (Tay k).A ^ (B k).g :=
      prod_nonneg fun k _ => pow_nonneg (zero_le_one.trans (Tay k).one_le_A) _
    exact mul_le_mul_of_nonneg_left p4 (mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) hH0)) _) (pow_nonneg (pow_nonneg hH0 _) _)) (pow_nonneg hA0 _))
  have hprodE : ∏ f, efAV (d₀ := d₀) (d₁ := d₁) (r := r) d d (d ^ (μ * S)) ef Tay f ^ NN f =
      (d * d) ^ (d₀ * A₀) * (d ^ (μ * S)) ^ (d₁ * A₁) * ((∏ k, (Tay k).E ^ (B k).g) * ef ^ r) ^ D₂ := by
    rw [prod_RVarAV]
    simp only [NN, efAV, efA, NfAV, NfA]
    have p1 : ∏ _i : Fin d₀, (d * d) ^ A₀ = (d * d) ^ (d₀ * A₀) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm A₀]
    have p2 : ∏ _j : Fin d₁, (d ^ (μ * S)) ^ A₁ = (d ^ (μ * S)) ^ (d₁ * A₁) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm A₁]
    have p3 : ∏ k, ∏ _j : Fin (Bb B k).g, (tayB Tay k).E ^ D₂ = (∏ k, (Tay k).E ^ (B k).g) ^ D₂ := by
      rw [← Finset.prod_pow]
      refine prod_congr rfl fun k _ => ?_
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, ← pow_mul, mul_comm]; rfl
    have p4 : ∏ _i : Fin r, ef ^ D₂ = (ef ^ r) ^ D₂ := by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, ← pow_mul, mul_comm]
    rw [p1, p2, p3, p4, mul_pow]; ring
  have hQ1 : 1 ≤ (∏ k, (Tay k).E ^ (B k).g) * ef ^ r := by
    refine Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (by
      have := (Tay k).one_le_E; omega)) (pow_ne_zero _ ?_))
    change (d * d) * (d * Em Tay) ≠ 0; have : Em Tay ≠ 0 := by omega
    positivity
  have hPA : (1 : ℝ) ≤ ∏ k, (Tay k).A ^ (B k).g := by
    calc (1 : ℝ) = ∏ _k : Fin m, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) fun k _ => one_le_pow₀ (Tay k).one_le_A
  have hc1 : (1 : ℝ) ≤ 2 * cBm (tayB Tay) * ((τ + 1) * H) := by
    have h1 := one_le_cBm (tayB Tay)
    have h2 : (1 : ℝ) ≤ (τ : ℝ) + 1 := by linarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)]
    have h3 : (1 : ℝ) ≤ ((τ : ℝ) + 1) * H := one_le_mul_of_one_le_of_one_le h2 hH
    nlinarith
  have hμH : (1 : ℝ) ≤ ((μ : ℝ) + 1) * H := one_le_mul_of_one_le_of_one_le hμ1 hH
  -- the vanishing of the Taylor coefficients
  have htco : ∀ j < T, tco j Fn = 0 := by
    intro j hj
    have hjT : j ≤ T := hj.le
    refine tco_eq_zero_of_small hKS' hA'1 hB1 he1 hδ1 hρ hdc hMb ?_
    refine small_of_bud (U := U) (KU := m * (a₁ + a₂ + a₃)) (Kρ := 1 + Real.log ((1 + Wn) / ρ₀) / Real.log 2)
      (KX := d₀ * (2 * Real.log d / Real.log 2) + d₁ * μ * Real.log d +
        Real.log (((∏ k, (Tay k).E ^ (B k).g) * ef ^ r : ℕ) : ℝ) +
        Real.log ((d * δm (tayB Tay) : ℕ) : ℝ) / Real.log 2 + 1)
      (KY := (1 + d₀ + d₁ + ((∑ k, (B k).g) + r : ℕ) + d₀ * (1 + Real.log ((μ + 1) * H) / Real.log 2) +
        d₁ * μ * Real.log H + Real.log (∏ k, (Tay k).A ^ (B k).g) +
        (1 + Real.log (2 * cBm (tayB Tay) * ((τ + 1) * H)) / Real.log 2)) + r * (1 + Real.log (hFib Tay μ H)))
      hρ hBud0 (Nat.cast_nonneg _) (by positivity) ?_ ?_ ?_ ?_ ?_
    · rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_left (le_bud_unit hS hBp ha₁ ha₂ ha₃) (Real.exp_pos _).le
    · rw [hρdef, one_div_div]
      exact le_bud_cauchy hS hBp hjT hWn hρ₀ hρ₀1
    · rw [hprodE]
      have e1 := le_bud_e (L := L) (A₀ := A₀) (A₁ := A₁) (D := D₂) hS hBp (d₀ := d₀) (d₁ := d₁) (μ := μ)
        hjT hd hQ1 hδ1
      refine le_trans (le_of_eq ?_) e1
      push_cast; ring
    · have e2 := le_bud_A (L := L) (A₀ := A₀) (A₁ := A₁) (D := D₂) hS hBp (d₀ := d₀) (d₁ := d₁)
        (G := (∑ k, (B k).g) + r) (μ := μ) hjT hμH hH hPA hc1
      have e3 := le_bud_S (L := L) (A₀ := A₀) (A₁ := A₁) (D' := D₂) (T := T) hS hBp (r := r) hhF1
      have hBv : 2 * (cBm (tayB Tay) * Hv) = 2 * cBm (tayB Tay) * ((τ + 1) * H) * (T + 1) := by
        rw [hHv]; ring
      have hle : A' * (2 * (cBm (tayB Tay) * Hv)) ^ j ≤
          (((L : ℝ) + 1) * Real.exp Bp * (2 : ℝ) ^ (d₀ * A₀ + d₁ * A₁ + ((∑ k, (B k).g) + r) * D₂) *
            ((S : ℝ) * ((μ + 1) * H)) ^ (d₀ * A₀) * (H ^ (μ * S)) ^ (d₁ * A₁) *
            (∏ k, (Tay k).A ^ (B k).g) ^ D₂ * (2 * cBm (tayB Tay) * ((τ + 1) * H) * (T + 1)) ^ j) *
          ((S : ℝ) * hFib Tay μ H) ^ (r * D₂) := by
        simp only [A']
        rw [hsum, hBv]
        have h0 : 0 ≤ ((L : ℝ) + 1) * Real.exp Bp * (2 : ℝ) ^ (d₀ * A₀ + d₁ * A₁ + ((∑ k, (B k).g) + r) * D₂) *
            (2 * cBm (tayB Tay) * ((τ + 1) * H) * (T + 1)) ^ j := by
          have := one_le_cBm (tayB Tay); positivity
        calc ((L : ℝ) + 1) * Real.exp Bp * (2 ^ (d₀ * A₀ + d₁ * A₁ + ((∑ k, (B k).g) + r) * D₂) *
              ∏ f, AfAV (d₀ := d₀) (d₁ := d₁) (r := r) Ht (H ^ (μ * S)) Hf Tay f ^ NN f) *
              (2 * cBm (tayB Tay) * ((τ + 1) * H) * (T + 1)) ^ j
            = (((L : ℝ) + 1) * Real.exp Bp * (2 : ℝ) ^ (d₀ * A₀ + d₁ * A₁ + ((∑ k, (B k).g) + r) * D₂) *
              (2 * cBm (tayB Tay) * ((τ + 1) * H) * (T + 1)) ^ j) *
              ∏ f, AfAV (d₀ := d₀) (d₁ := d₁) (r := r) Ht (H ^ (μ * S)) Hf Tay f ^ NN f := by ring
          _ ≤ (((L : ℝ) + 1) * Real.exp Bp * (2 : ℝ) ^ (d₀ * A₀ + d₁ * A₁ + ((∑ k, (B k).g) + r) * D₂) *
              (2 * cBm (tayB Tay) * ((τ + 1) * H) * (T + 1)) ^ j) *
              (((S : ℝ) * ((μ + 1) * H)) ^ (d₀ * A₀) * (H ^ (μ * S)) ^ (d₁ * A₁) *
                (∏ k, (Tay k).A ^ (B k).g) ^ D₂ * ((S : ℝ) * hFib Tay μ H) ^ (r * D₂)) :=
              mul_le_mul_of_nonneg_left hprodA h0
          _ = _ := by ring
      refine hle.trans ((mul_le_mul e2 e3 (by positivity) (by positivity)).trans (le_of_eq ?_))
      rw [← Real.exp_add]; congr 1; push_cast; ring
    · refine le_trans (le_of_eq ?_) hU
      unfold kLUV; rw [hef]
  -- Leibniz
  intro j hj
  have hF0 : ∀ i < T, iteratedDeriv i Fn 0 = 0 := fun i hi => by
    have h := htco i hi
    unfold tco at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h (by exact_mod_cast i.factorial_ne_zero)
  have hev : (fun s : ℂ => PsiAV M νs p (t + s • v)) =ᶠ[𝓝 0] (uA D₂ κ lam (piA v)) * Fn := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with s hs
    exact hfac s (mem_ball_zero_iff.mp hs).le
  rw [(hev.iteratedDeriv j).eq_of_nhds,
    iteratedDeriv_mul (analyticAt_uA κ lam (piA v)).contDiffAt hKS'.1.contDiffAt]
  refine sum_eq_zero fun i hi => ?_
  rw [hF0 (j - i) (lt_of_le_of_lt (Nat.sub_le j i) hj), mul_zero]

end LSG.AuxAV
