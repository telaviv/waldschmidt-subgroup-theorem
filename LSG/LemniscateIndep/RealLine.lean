/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.LemniscateIndep.Integral
import LSG.LemniscateIndep.Symm

/-!
# `℘` on the real segment `(0, a/2]` of a square lattice `a ℤ[i]`

For `ω₁ = a > 0`, `ω₂ = i a`, write `P t = ℘(t)`, `Q t = ℘'(t)` (real on `ℝ`) and `e = P (a/2)`.
* `g₂ = 4 e²` (from `℘'(a/2) = 0`, `g₃ = 0` and `e ≠ 0`, the latter by `℘(i z) = -℘(z)` and the
  degree-two property of `℘`);
* `Q² = 4 P³ - 4 e² P` and `Q ≠ 0` on `(0, a/2)`; `P → +∞` at `0⁺`; hence `P > e > 0` on `(0, a/2)`.
* `τ = √(e / P)` maps `(0, a/2)` into `(0, 1)`, extends continuously to `[0, a/2]` with
  `τ 0 = 0`, `τ (a/2) = 1`, and `(τ' / √(1 - τ⁴))² = e`.
* Mean value theorem for `F ∘ τ`, `F x = ∫₀ˣ dt/√(1-t⁴)`: `varpi / 2 = √e · a / 2`, i.e.
  `e = (varpi / a)²` (`rP_half_eq`).
-/

noncomputable section

open Complex PeriodPair Filter Topology Set LSG.Weierstrass

namespace LSG.LemniscateIndep

/-- Hypotheses: `L` is the square lattice `a ℤ[i]` with `a > 0`. -/
structure Sq (L : PeriodPair) (a : ℝ) : Prop where
  pos : 0 < a
  h₁ : L.ω₁ = a
  h₂ : L.ω₂ = I * a

/-- `℘` on the real line (real part). -/
def rP (L : PeriodPair) (t : ℝ) : ℝ := (℘[L] (t : ℂ)).re

/-- `℘'` on the real line (real part). -/
def rQ (L : PeriodPair) (t : ℝ) : ℝ := (℘'[L] (t : ℂ)).re

/-- `t² ℘(t)`, extended continuously to `t = 0`. -/
def rPhi (L : PeriodPair) (t : ℝ) : ℝ := t ^ 2 * (L.weierstrassPExcept 0 (t : ℂ)).re + 1

/-- `τ(t) = √(e / ℘(t))`, written so that it is continuous at `0`. -/
def tau (L : PeriodPair) (a t : ℝ) : ℝ := Real.sqrt (rP L (a / 2)) * t / Real.sqrt (rPhi L t)

variable {L : PeriodPair} {a : ℝ}

namespace Sq

variable (S : Sq L a)
include S

lemma notMem {t : ℝ} (ht0 : 0 < t) (hta : t < a) : (t : ℂ) ∉ L.lattice :=
  ofReal_notMem S.pos S.h₁ S.h₂ ht0 hta

lemma P_ofReal (t : ℝ) : ℘[L] (t : ℂ) = (rP L t : ℂ) := weierstrassP_ofReal S.h₁ S.h₂ t

lemma Q_ofReal (t : ℝ) : ℘'[L] (t : ℂ) = (rQ L t : ℂ) := derivWeierstrassP_ofReal S.h₁ S.h₂ t

lemma hasDerivAt_rP {t : ℝ} (ht0 : 0 < t) (hta : t < a) : HasDerivAt (rP L) (rQ L t) t :=
  (hasDerivAt_weierstrassP L (S.notMem ht0 hta)).real_of_complex

lemma half_eq : L.ω₁ / 2 = ((a / 2 : ℝ) : ℂ) := by rw [S.h₁]; push_cast; ring

lemma rP_half_ne_zero : rP L (a / 2) ≠ 0 := by
  intro he
  have hP : ℘[L] (L.ω₁ / 2) = 0 := by rw [S.half_eq, S.P_ofReal, he, ofReal_zero]
  have hI : ℘[L] (L.ω₂ / 2) = 0 := by
    rw [show L.ω₂ / 2 = I * (L.ω₁ / 2) by rw [S.h₁, S.h₂]; ring, weierstrassP_I_mul S.h₁ S.h₂,
      hP, neg_zero]
  rcases (weierstrassP_eq_iff L L.ω₁_div_two_notMem_lattice L.ω₂_div_two_notMem_lattice).1
    (hI.trans hP.symm) with h | h
  · have := (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := -1 / 2) (β := 1 / 2)).1
      (by convert h using 1; push_cast; ring)
    exact absurd this.1 (by norm_num)
  · have := (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 1 / 2)).1
      (by convert h using 1; push_cast; ring)
    exact absurd this.1 (by norm_num)

/-- `g₂ = 4 e²`. -/
lemma g₂_eq : L.g₂ = 4 * (rP L (a / 2) : ℂ) ^ 2 := by
  have hc := weierstrassP_half_cubic L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice
  rw [g₃_eq_zero_of_square S.h₁ S.h₂, S.half_eq, S.P_ofReal] at hc
  have h0 : (rP L (a / 2) : ℂ) ≠ 0 := ofReal_ne_zero.2 S.rP_half_ne_zero
  have : (rP L (a / 2) : ℂ) * (4 * (rP L (a / 2) : ℂ) ^ 2 - L.g₂) = 0 := by
    linear_combination hc
  exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0)).symm

lemma relation {t : ℝ} (ht0 : 0 < t) (hta : t < a) :
    rQ L t ^ 2 = 4 * rP L t ^ 3 - 4 * rP L (a / 2) ^ 2 * rP L t := by
  have h := L.derivWeierstrassP_sq (t : ℂ) (S.notMem ht0 hta)
  rw [S.P_ofReal, S.Q_ofReal, S.g₂_eq, g₃_eq_zero_of_square S.h₁ S.h₂, sub_zero] at h
  exact_mod_cast h

lemma rQ_ne_zero {t : ℝ} (ht0 : 0 < t) (hta : t < a / 2) : rQ L t ≠ 0 := by
  have h := derivWeierstrassP_ne_zero L (z := (t : ℂ)) (by
    rw [show (2 : ℂ) * t = ((2 * t : ℝ) : ℂ) by push_cast; ring]
    exact S.notMem (by linarith) (by linarith))
  rw [S.Q_ofReal] at h
  exact_mod_cast h

end Sq

lemma rPhi_eq {t : ℝ} (ht : t ≠ 0) : rPhi L t = t ^ 2 * rP L t := by
  have h := congrArg Complex.re (weierstrassP_eq_except_zero L (t : ℂ))
  rw [show (1 : ℂ) / (t : ℂ) ^ 2 = ((1 / t ^ 2 : ℝ) : ℂ) by push_cast; ring, add_re,
    ofReal_re] at h
  rw [rPhi, rP, h]
  field_simp

lemma continuousAt_rPhi {t : ℝ} (h : (t : ℂ) ∉ (L.lattice : Set ℂ) \ {0}) :
    ContinuousAt (rPhi L) t := by
  have hw : ContinuousAt (fun s : ℝ => L.weierstrassPExcept 0 (s : ℂ)) t :=
    (L.analyticOnNhd_weierstrassPExcept 0 _ h).continuousAt.comp continuous_ofReal.continuousAt
  exact ((continuousAt_id.pow 2).mul (continuous_re.continuousAt.comp hw)).add continuousAt_const

namespace Sq

variable (S : Sq L a)
include S

lemma exists_large : ∃ t₀ ∈ Ioo 0 (a / 2), |rP L (a / 2)| < rP L t₀ := by
  have h0 : rPhi L 0 = 1 := by simp [rPhi]
  have hφ : Tendsto (rPhi L) (𝓝[>] 0) (𝓝 1) := by
    have := (continuousAt_rPhi (L := L) (t := 0) (by simp)).tendsto
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun t : ℝ => (t⁻¹) ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero
  have hprod := hφ.pos_mul_atTop one_pos hinv
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (a / 2) := Ioo_mem_nhdsGT (half_pos S.pos)
  obtain ⟨t, ht, hgt⟩ := (hev1.and (hprod.eventually_gt_atTop |rP L (a / 2)|)).exists
  refine ⟨t, ht, ?_⟩
  rw [rPhi_eq ht.1.ne'] at hgt
  have : t ^ 2 * rP L t * (t⁻¹) ^ 2 = rP L t := by
    have := ht.1.ne'; field_simp
  linarith

lemma abs_lt_rP {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) : |rP L (a / 2)| < rP L t := by
  obtain ⟨t₀, ht₀, hgt⟩ := S.exists_large
  by_contra hle
  rw [not_lt] at hle
  have hsub : uIcc t t₀ ⊆ Ioo 0 (a / 2) := ordConnected_Ioo.uIcc_subset ht ht₀
  have hcont : ContinuousOn (rP L) (uIcc t t₀) := fun x hx =>
    (S.hasDerivAt_rP (hsub hx).1 (by linarith [(hsub hx).2, S.pos])).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hPc⟩ := intermediate_value_uIcc hcont (mem_uIcc.2 (Or.inl ⟨hle, hgt.le⟩))
  have hrel := S.relation (hsub hc).1 (by linarith [(hsub hc).2, S.pos])
  rw [hPc] at hrel
  have h3 : |rP L (a / 2)| ^ 3 = |rP L (a / 2)| ^ 2 * |rP L (a / 2)| := pow_succ _ 2
  have : rQ L c ^ 2 = 0 := by rw [hrel, h3, sq_abs]; ring
  exact S.rQ_ne_zero (hsub hc).1 (hsub hc).2 (pow_eq_zero_iff two_ne_zero |>.1 this)

lemma rP_half_pos : 0 < rP L (a / 2) := by
  have hcont : ContinuousAt (rP L) (a / 2) :=
    (S.hasDerivAt_rP (half_pos S.pos) (half_lt_self S.pos)).continuousAt
  have hle : |rP L (a / 2)| ≤ rP L (a / 2) := by
    refine ge_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (a / 2)))) ?_
    filter_upwards [Ioo_mem_nhdsLT (half_pos S.pos)] with t ht using (S.abs_lt_rP ht).le
  exact lt_of_le_of_ne ((abs_nonneg _).trans hle) (Ne.symm S.rP_half_ne_zero)

lemma lt_rP {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) : rP L (a / 2) < rP L t :=
  (le_abs_self _).trans_lt (S.abs_lt_rP ht)

lemma le_rP {t : ℝ} (ht : t ∈ Ioc 0 (a / 2)) : rP L (a / 2) ≤ rP L t := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h]
  · exact (S.lt_rP ⟨ht.1, h⟩).le

lemma rPhi_pos {t : ℝ} (ht : t ∈ Icc 0 (a / 2)) : 0 < rPhi L t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simp [rPhi]
  · rw [rPhi_eq h.ne']
    exact mul_pos (pow_pos h 2) (S.rP_half_pos.trans_le (S.le_rP ⟨h, ht.2⟩))

lemma tau_eq {t : ℝ} (ht : t ∈ Ioc 0 (a / 2)) :
    tau L a t = Real.sqrt (rP L (a / 2)) / Real.sqrt (rP L t) := by
  have hP : 0 < rP L t := S.rP_half_pos.trans_le (S.le_rP ht)
  rw [tau, rPhi_eq ht.1.ne', Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.1.le]
  have := Real.sqrt_pos.2 hP
  have := ht.1.ne'
  field_simp

omit S in
lemma tau_zero : tau L a 0 = 0 := by simp [tau]

lemma tau_half : tau L a (a / 2) = 1 := by
  rw [S.tau_eq ⟨half_pos S.pos, le_rfl⟩]
  exact div_self (Real.sqrt_pos.2 S.rP_half_pos).ne'

lemma tau_mem_Icc {t : ℝ} (ht : t ∈ Icc 0 (a / 2)) : tau L a t ∈ Icc 0 1 := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; rw [tau_zero]; exact ⟨le_rfl, zero_le_one⟩
  · rw [S.tau_eq ⟨h, ht.2⟩]
    have hP : 0 < rP L t := S.rP_half_pos.trans_le (S.le_rP ⟨h, ht.2⟩)
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (Real.sqrt_pos.2 hP)]
    exact Real.sqrt_le_sqrt (S.le_rP ⟨h, ht.2⟩)

lemma tau_mem_Ioo {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) : tau L a t ∈ Ioo 0 1 := by
  rw [S.tau_eq ⟨ht.1, ht.2.le⟩]
  have hP : 0 < rP L t := S.rP_half_pos.trans (S.lt_rP ht)
  refine ⟨div_pos (Real.sqrt_pos.2 S.rP_half_pos) (Real.sqrt_pos.2 hP), ?_⟩
  rw [div_lt_one (Real.sqrt_pos.2 hP)]
  exact Real.sqrt_lt_sqrt S.rP_half_pos.le (S.lt_rP ht)

lemma continuousOn_tau : ContinuousOn (tau L a) (Icc 0 (a / 2)) := by
  have hφ : ContinuousOn (rPhi L) (Icc 0 (a / 2)) := by
    intro t ht
    refine (continuousAt_rPhi ?_).continuousWithinAt
    rintro ⟨hm, hne⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; exact hne (by simp)
    · exact S.notMem h (by linarith [ht.2, S.pos]) hm
  exact (continuousOn_const.mul continuousOn_id).div hφ.sqrt
    (fun t ht => (Real.sqrt_pos.2 (S.rPhi_pos ht)).ne')

/-- The derivative of `τ` on `(0, a/2)`. -/
def dtau (L : PeriodPair) (a t : ℝ) : ℝ :=
  (0 * Real.sqrt (rP L t) - Real.sqrt (rP L (a / 2)) * (rQ L t / (2 * Real.sqrt (rP L t)))) /
    Real.sqrt (rP L t) ^ 2

lemma hasDerivAt_tau {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) : HasDerivAt (tau L a) (dtau L a t) t := by
  have hP : 0 < rP L t := S.rP_half_pos.trans (S.lt_rP ht)
  have hs := (S.hasDerivAt_rP ht.1 (by linarith [ht.2, S.pos])).sqrt hP.ne'
  have hd := (hasDerivAt_const t (Real.sqrt (rP L (a / 2)))).div hs (Real.sqrt_pos.2 hP).ne'
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using S.tau_eq ⟨hs.1, hs.2.le⟩

lemma deriv_sq {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) :
    (lemInt (tau L a t) * dtau L a t) ^ 2 = rP L (a / 2) := by
  have hP : 0 < rP L t := S.rP_half_pos.trans (S.lt_rP ht)
  have hτ := S.tau_mem_Ioo ht
  have hrel := S.relation ht.1 (by linarith [ht.2, S.pos])
  rw [S.tau_eq ⟨ht.1, ht.2.le⟩] at hτ ⊢
  set r := Real.sqrt (rP L (a / 2)) with hr
  set s := Real.sqrt (rP L t) with hs
  have hr0 : 0 < r := Real.sqrt_pos.2 S.rP_half_pos
  have hs0 : 0 < s := Real.sqrt_pos.2 hP
  have hr2 : r ^ 2 = rP L (a / 2) := Real.sq_sqrt S.rP_half_pos.le
  have hs2 : s ^ 2 = rP L t := Real.sq_sqrt hP.le
  have h4 : (r / s) ^ 4 < 1 := pow_lt_one₀ hτ.1.le hτ.2 (by norm_num)
  set u := Real.sqrt (1 - (r / s) ^ 4) with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 (by linarith)
  have hu2 : u ^ 2 = 1 - (r / s) ^ 4 := Real.sq_sqrt (by linarith)
  have hQ : rQ L t ^ 2 = 4 * s ^ 6 - 4 * r ^ 4 * s ^ 2 := by
    rw [hrel, ← hs2, ← hr2]; ring
  have hX : (dtau L a t) ^ 2 = r ^ 2 * u ^ 2 := by
    rw [dtau, ← hr, ← hs, hu2, div_pow]
    field_simp
    linear_combination r ^ 2 * hQ
  rw [lemInt, ← hu, mul_pow, hX, ← hr2]
  field_simp

/-- **`e = (varpi / a)²`.** -/
theorem rP_half_eq : rP L (a / 2) = (varpi / a) ^ 2 := by
  have ha := S.pos
  have hGc : ContinuousOn (fun t => lemF (tau L a t)) (Icc 0 (a / 2)) :=
    continuousOn_lemF.comp S.continuousOn_tau (fun t ht => S.tau_mem_Icc ht)
  have hGd : ∀ x ∈ Ioo 0 (a / 2),
      HasDerivAt (fun t => lemF (tau L a t)) (lemInt (tau L a x) * dtau L a x) x :=
    fun x hx => (hasDerivAt_lemF (S.tau_mem_Ioo hx)).comp x (S.hasDerivAt_tau hx)
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope _ _ (half_pos ha) hGc hGd
  rw [S.tau_half, tau_zero, lemF_one, lemF_zero] at hcd
  have hsl : (varpi / 2 - 0) / (a / 2 - 0) = varpi / a := by
    rw [sub_zero, sub_zero]; field_simp
  rw [← S.deriv_sq hc, hcd, hsl]

/-- `g₂ = 4 (varpi / a)⁴` for the square lattice `a ℤ[i]`. -/
theorem g₂_eq_of_square : L.g₂ = 4 * ((varpi / a : ℝ) : ℂ) ^ 4 := by
  rw [S.g₂_eq, S.rP_half_eq]; push_cast; ring

end Sq

end LSG.LemniscateIndep
