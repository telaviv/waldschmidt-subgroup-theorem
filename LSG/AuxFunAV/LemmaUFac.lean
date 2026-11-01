/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunAV.Growth
import LSG.AuxFunA.LemmaUFac

/-!
# M2.6.5a: Lemma U for `MonoAV`, the factorisation on a line through a point of `Y(S)`

At a point `t` whose block parts `t_z` are periods in `per` (every point of `Y(S)`: block parts in `lat`, fibre part
`t_s = M η(t_z) + s′` with `s′ = sPart M t` algebraic), quasi-periodicity of `θ` and of `T` (same multiplier,
`VBlockAn.T_qp`) gives, on `θ_{i₀}(s v_k) ≠ 0`,

  `Ψ(t + s v) = u(s) · F(s)`, `u = uA (D + F) κ λ (piA v)` (MEB's unit with exponent `D + F`),
  `F(s) = Σ_l p_l Π_f g_f(s)^{n_{l,f}}`   (`PsiAV_line_eq`)

with the basic factors `g_f` (`gAV`): those of the abelian consumer (`gA` on `piA t`, `piA v`) and the **fibre factors**
`s′_i + v_{s,i} s + Σ_j M_ij τ_j(s v_{z,j})` (`fibR` on the line). Only Taylor data at the origin enter: the fibre
factors have `KS`-controlled Taylor coefficients from `VBlockTay.ksT` and the algebraicity of `M` (`ks_fibAV`), and
`F` from `LSG.Aux.KS.poly` (`ks_FAV`).
-/

open Complex Finset Module

noncomputable section

namespace LSG.AuxAV

open LSG.MEBV LSG.AuxA LSG.Aux
open LSG.MEB (AbBlock)

variable {K : Type*} [Field K] [NumberField K]
variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {D F : ℕ}

/-- The base Taylor packages. -/
def tayB {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) : ∀ k, AbBlockTay (Bb B k) ι :=
  fun k => (Tay k).toAbBlockTay

/-- `Σ_k A_k`. -/
def Am {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) : ℝ := ∑ k, (Tay k).A

/-- `Π_k E_k`. -/
def Em {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) : ℕ := ∏ k, (Tay k).E

lemma A_le_Am {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) (k : Fin m) : (Tay k).A ≤ Am Tay :=
  single_le_sum (f := fun k => (Tay k).A) (fun k _ => zero_le_one.trans (Tay k).one_le_A) (mem_univ k)

lemma Am_nonneg {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) : 0 ≤ Am Tay :=
  sum_nonneg fun k _ => zero_le_one.trans (Tay k).one_le_A

lemma one_le_Em {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) : 1 ≤ Em Tay :=
  Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun k _ => by have := (Tay k).one_le_E; omega)

/-- The algebraic fibre part `s − M η(z)` of a point. -/
def sPart (M : Matrix (Fin r) (Fin m) ℂ) (t : TanAV d₀ d₁ r B) : Fin r → ℂ :=
  t.2.2.2 - M.mulVec (etaB B t.2.2.1)

/-- **The basic factors** on the line `s ↦ t + s v`. -/
def gAV (M : Matrix (Fin r) (Fin m) ℂ) (t v : TanAV d₀ d₁ r B) : RVarAV d₀ d₁ r B → ℂ → ℂ
  | .inl f => gA (piA t) (piA v) f
  | .inr i => fun s => fibR M i (s • v.2.2.1) (sPart M t + s • v.2.2.2)

/-- **The normalised function** `F(s) = Σ_l p_l Π_f g_f(s)^{n_{l,f}}`. -/
def FAV (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F) (p : Fin L → ℤ)
    (t v : TanAV d₀ d₁ r B) (s : ℂ) : ℂ :=
  ∑ l, (p l : ℂ) * ∏ f, gAV M t v f s ^ (νs l).rexp f

/-- **The factorisation** `Ψ(t + s v) = u(s) F(s)`. -/
theorem PsiAV_line_eq (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) (t v : TanAV d₀ d₁ r B) (κ lam : Fin m → ℂ)
    (hθ : ∀ k s, (B k).base.θ (t.2.2.1 k + s • v.2.2.1 k) =
      (κ k * Complex.exp (lam k * s)) • (B k).base.θ (s • v.2.2.1 k))
    (hT : ∀ k s, (B k).T (s • v.2.2.1 k + t.2.2.1 k) ((B k).η (t.2.2.1 k)) =
      (κ k * Complex.exp (lam k * s)) • (B k).T (s • v.2.2.1 k) 0)
    (s : ℂ) (hs : ∀ k, (B k).base.θ (s • v.2.2.1 k) (B k).base.i₀ ≠ 0) :
    PsiAV M νs p (t + s • v) = uA (D + F) κ lam (piA v) s * FAV M νs p t v s := by
  set f : Fin m → ℂ := fun k => κ k * Complex.exp (lam k * s) with hf
  set P : ℂ := ∏ k, (κ k * Complex.exp (lam k * s) * (B k).base.θ (s • v.2.2.1 k) (B k).base.i₀) with hP
  have huA : ∀ n, uA n κ lam (piA v) s = P ^ n := fun n => by
    rw [hP, ← prod_pow]; rfl
  have hPfθ : (∏ k, f k) * ∏ k, thI B (s • v.2.2.1) k = P := by
    rw [hP, ← prod_mul_distrib]; rfl
  have hz : ∀ k, thI B (s • v.2.2.1) k ≠ 0 := hs
  unfold PsiAV FAV
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  -- the abelian part
  have hA : (νs l).μ.eval (piA (t + s • v)) =
      P ^ D * ∏ f : RVarA d₀ d₁ (Bb B), gAV M t v (.inl f) s ^ (νs l).rexp (.inl f) := by
    have h := PsiA_line_eq (fun _ : Fin 1 => (νs l).μ) (fun _ => 1) (piA t) (piA v) κ lam hθ s hs
    simp only [PsiA, FA, univ_unique, sum_singleton, Int.cast_one, one_mul] at h
    rw [map_add, map_smul, h, huA]
    rfl
  -- the padding
  have hW : ∏ k, thI B (t + s • v).2.2.1 k = P := by
    rw [← hPfθ, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ => ?_
    change (B k).base.θ (t.2.2.1 k + s • v.2.2.1 k) _ = _
    rw [hθ k s]; rfl
  -- the fibre forms
  have hS : ∀ i, fibF M i (t + s • v).2.2.1 (t + s • v).2.2.2 = P * gAV M t v (.inr i) s := by
    intro i
    have e1 : (t + s • v).2.2.1 = s • v.2.2.1 + t.2.2.1 := by
      change t.2.2.1 + s • v.2.2.1 = _; rw [add_comm]
    have e2 : (t + s • v).2.2.2 = (sPart M t + s • v.2.2.2) + M.mulVec (etaB B t.2.2.1) := by
      change t.2.2.2 + s • v.2.2.2 = _; simp only [sPart]; abel
    rw [e1, e2, fibF_add_per (z := s • v.2.2.1) (lam := t.2.2.1) M i _ f
      (fun k => by rw [add_comm]; exact hθ k s) (fun k => hT k s),
      fibF_eq M i _ _ hz, ← mul_assoc, hPfθ]
    rfl
  have hφ := (νs l).hφ
  have key : ∏ i, fibF M i (t + s • v).2.2.1 (t + s • v).2.2.2 ^ (νs l).φ i =
      P ^ (∑ i, (νs l).φ i) * ∏ i, gAV M t v (.inr i) s ^ (νs l).rexp (.inr i) := by
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by rw [hS i, mul_pow]; rfl
  unfold MonoAV.eval
  rw [hA, hW, key, huA, Fintype.prod_sum_type (fun x => gAV M t v x s ^ (νs l).rexp x)]
  have e : P ^ (D + F) = P ^ D * P ^ (F - ∑ i, (νs l).φ i) * P ^ (∑ i, (νs l).φ i) := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hφ, ← pow_add]
  rw [e]; ring

/-! ### Sizes of the Taylor coefficients -/

/-- **Taylor coefficients of a fibre factor.** -/
theorem ks_fibAV {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r)
    (t v : TanAV d₀ d₁ r B) {Ht Hv H : ℝ} {dt dv d : ℕ} (hHv : 1 ≤ Hv) (hH : 0 ≤ H)
    (ht : Sz ι Ht dt (sPart M t i)) (hv : Sz ι Hv dv (v.2.2.2 i)) (hvz : ∀ k j, Sz ι Hv dv (v.2.2.1 k j))
    (hM : ∀ j, Sz ι H d (M i j)) :
    KS ι (max 1 Ht + m * (H * Am Tay)) (cBm (tayB Tay) * Hv) ((dt * dv) * (d * Em Tay)) (dv * δm (tayB Tay))
      (gAV M t v (.inr i)) := by
  have hB0 : 0 ≤ cBm (tayB Tay) * Hv := by have := one_le_cBm (tayB Tay); positivity
  have hHvB : Hv ≤ cBm (tayB Tay) * Hv := le_mul_of_one_le_left (by linarith) (one_le_cBm (tayB Tay))
  have hlin : KS ι (max 1 Ht) (cBm (tayB Tay) * Hv) ((dt * dv) * (d * Em Tay)) (dv * δm (tayB Tay))
      (fun s => sPart M t i + v.2.2.2 i * s) := by
    refine (ks_lin ((ht.mono (le_max_right _ _) (Dvd.intro dv rfl))) ?_ hB0).mono le_rfl hB0 le_rfl
      (Dvd.intro _ rfl) dvd_rfl
    refine hv.mono ?_ (Dvd.intro_left dt rfl)
    exact hHvB.trans (le_mul_of_one_le_left hB0 (le_max_left _ _))
  have hj : ∀ j ∈ univ, KS ι (H * Am Tay) (cBm (tayB Tay) * Hv) ((dt * dv) * (d * Em Tay)) (dv * δm (tayB Tay))
      (fun s => M i j * tauV (B j) (s • v.2.2.1 j)) := by
    intro j _
    have h := KS.const_mul (hM j) ((Tay j).ksT (v.2.2.1 j) Hv dv hHv (hvz j))
    refine h.mono (mul_le_mul_of_nonneg_left (A_le_Am Tay j) hH)
      (by have := (Tay j).one_le_cB; positivity)
      (mul_le_mul_of_nonneg_right (cB_le_cBm (tayB Tay) j) (zero_le_one.trans hHv)) ?_
      (mul_dvd_mul_left dv (δ_dvd_δm (tayB Tay) j))
    exact Dvd.dvd.mul_left (mul_dvd_mul_left d (dvd_prod_of_mem _ (mem_univ j))) _
  have hsum := KS.sum univ hB0 hj
  have hadd := hlin.add hsum
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hadd
  convert hadd using 1
  funext s
  simp only [gAV, fibR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The size of the basic factors (`Hf`: the fibre factors). -/
def AfAV (Ht He Hf : ℝ) {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) : RVarAV d₀ d₁ r B → ℝ
  | .inl f => AfA Ht He (tayB Tay) f
  | .inr _ => Hf

/-- The denominators of the basic factors (`ef`: the fibre factors). -/
def efAV (dt dv de ef : ℕ) {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) : RVarAV d₀ d₁ r B → ℕ
  | .inl f => efA dt dv de (tayB Tay) f
  | .inr _ => ef

/-- The degree bounds of the basic factors. -/
def NfAV (A₀ A₁ D₂ : ℕ) : RVarAV d₀ d₁ r B → ℕ
  | .inl f => NfA (B := Bb B) A₀ A₁ D₂ f
  | .inr _ => D₂

/-- **Sizes of the Taylor coefficients of `F`.** -/
theorem ks_FAV {ι : K →+* ℂ} (Tay : ∀ k, VBlockTay (B k) ι) (M : Matrix (Fin r) (Fin m) ℂ) {L A₀ A₁ : ℕ}
    (νs : Fin L → MonoAV d₀ d₁ r B D F) (p : Fin L → ℤ) (hα : ∀ l i, (νs l).μ.α i ≤ A₀)
    (hβ : ∀ l j, (νs l).μ.β j ≤ A₁) (t v : TanAV d₀ d₁ r B) {Ht He Hv H : ℝ} {dt de dv d : ℕ}
    (hHv : 1 ≤ Hv) (hH : 0 ≤ H)
    (ht : ∀ i, Sz ι Ht dt (t.1 i)) (he : ∀ j, Sz ι He de (Complex.exp (t.2.1 j)))
    (hs : ∀ i, Sz ι Ht dt (sPart M t i))
    (hv0 : ∀ i, Sz ι Hv dv (v.1 i)) (hv1 : ∀ j, Sz ι Hv dv (v.2.1 j))
    (hv2 : ∀ k j, Sz ι Hv dv (v.2.2.1 k j)) (hv3 : ∀ i, Sz ι Hv dv (v.2.2.2 i))
    (hM : ∀ i j, Sz ι H d (M i j)) :
    KS ι ((∑ l, |(p l : ℝ)|) * (2 ^ (∑ f, NfAV (d₀ := d₀) (d₁ := d₁) (r := r) (B := B) A₀ A₁ (D + F) f) *
        ∏ f, AfAV (d₀ := d₀) (d₁ := d₁) (r := r) Ht He (max 1 Ht + m * (H * Am Tay)) Tay f ^
          NfAV (d₀ := d₀) (d₁ := d₁) (r := r) (B := B) A₀ A₁ (D + F) f))
      (2 * (cBm (tayB Tay) * Hv))
      (∏ f, efAV (d₀ := d₀) (d₁ := d₁) (r := r) dt dv de ((dt * dv) * (d * Em Tay)) Tay f ^
        NfAV (d₀ := d₀) (d₁ := d₁) (r := r) (B := B) A₀ A₁ (D + F) f)
      (dv * δm (tayB Tay)) (FAV M νs p t v) := by
  have hB0 : 0 ≤ cBm (tayB Tay) * Hv := by have := one_le_cBm (tayB Tay); positivity
  have hHvB : Hv ≤ cBm (tayB Tay) * Hv := le_mul_of_one_le_left (by linarith) (one_le_cBm (tayB Tay))
  have hg : ∀ f, KS ι (AfAV Ht He (max 1 Ht + m * (H * Am Tay)) Tay f) (cBm (tayB Tay) * Hv)
      (efAV dt dv de ((dt * dv) * (d * Em Tay)) Tay f) (dv * δm (tayB Tay)) (gAV M t v f) := by
    intro f
    rcases f with (i | j | ⟨k, j⟩) | i
    · refine ks_lin ((ht i).mono (le_max_right _ _) (Dvd.intro dv rfl)) ?_ hB0
      refine (hv0 i).mono ?_ (Dvd.intro_left dt rfl)
      exact hHvB.trans (le_mul_of_one_le_left hB0 (le_max_left _ _))
    · refine (ks_expm ((he j).mono_le (le_max_right _ _)) (hv1 j)).mono le_rfl
        (zero_le_one.trans hHv) hHvB dvd_rfl (Dvd.intro _ rfl)
    · have h := (Tay k).ks (v.2.2.1 k) Hv dv hHv (hv2 k) j
      refine h.mono le_rfl (by have := (Tay k).one_le_cB; positivity)
        (mul_le_mul_of_nonneg_right (cB_le_cBm (tayB Tay) k) (zero_le_one.trans hHv)) dvd_rfl
        (mul_dvd_mul_left dv (δ_dvd_δm (tayB Tay) k))
    · exact ks_fibAV Tay M i t v hHv hH (hs i) (hv3 i) hv2 (hM i)
  have hA : ∀ f, 1 ≤ AfAV (d₀ := d₀) (d₁ := d₁) (r := r) Ht He (max 1 Ht + m * (H * Am Tay)) Tay f := by
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
  exact KS.poly hB0 hg hA p (fun l => (νs l).rexp) (NfAV A₀ A₁ (D + F)) fun l f => by
    rcases f with (i | j | ⟨k, j⟩) | i
    · exact hα l i
    · exact hβ l j
    · have := (νs l).μ.hγ k
      rw [Fin.sum_univ_succ] at this
      have hle := single_le_sum (f := fun j : Fin (Bb B k).g => (νs l).μ.γ k j.succ) (fun _ _ => Nat.zero_le _)
        (mem_univ j)
      simp only [MonoAV.rexp, MonoA.rexp, NfAV, NfA]; omega
    · have := (νs l).hφ
      have hle := single_le_sum (f := fun i => (νs l).φ i) (fun _ _ => Nat.zero_le _) (mem_univ i)
      simp only [MonoAV.rexp, NfAV]; omega

end LSG.AuxAV
