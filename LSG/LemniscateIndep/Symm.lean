/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.Addition

/-!
# Symmetries of a square lattice `a ℤ[i]` (`a > 0` real)

For a period pair with `ω₁ = a`, `ω₂ = i a`:
* the lattice is stable under `z ↦ i z` and under complex conjugation;
* `G₆ = 0`, hence `g₃ = 0` (`g₃_eq_zero_of_square`);
* `℘(i z) = -℘(z)`, `℘(z̄) = conj ℘(z)`, `℘'(z̄) = conj ℘'(z)`;
* real points of `(0, a)` are not lattice points.
-/

noncomputable section

open Complex PeriodPair

namespace LSG.LemniscateIndep

variable {L : PeriodPair} {a : ℝ}

lemma mem_lattice_sq (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) {z : ℂ} :
    z ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) * a + n * (I * a) = z := by
  rw [PeriodPair.mem_lattice, h₁, h₂]

lemma I_mul_mem (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) {z : ℂ} (hz : z ∈ L.lattice) :
    I * z ∈ L.lattice := by
  obtain ⟨m, n, rfl⟩ := (mem_lattice_sq h₁ h₂).1 hz
  refine (mem_lattice_sq h₁ h₂).2 ⟨-n, m, ?_⟩
  push_cast
  linear_combination (-(n : ℂ) * a) * I_sq

lemma conj_mem (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) {z : ℂ} (hz : z ∈ L.lattice) :
    (starRingEnd ℂ) z ∈ L.lattice := by
  obtain ⟨m, n, rfl⟩ := (mem_lattice_sq h₁ h₂).1 hz
  refine (mem_lattice_sq h₁ h₂).2 ⟨m, -n, ?_⟩
  simp only [map_add, map_mul, map_intCast, conj_ofReal, conj_I]
  push_cast
  ring

/-- Multiplication by `i` as a permutation of the lattice. -/
def mulIEquiv (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) : L.lattice ≃ L.lattice where
  toFun l := ⟨I * l, I_mul_mem h₁ h₂ l.2⟩
  invFun l := ⟨I * (I * (I * l)), I_mul_mem h₁ h₂ (I_mul_mem h₁ h₂ (I_mul_mem h₁ h₂ l.2))⟩
  left_inv l := by
    ext; simp only
    linear_combination (I ^ 2 - 1) * (l : ℂ) * I_sq
  right_inv l := by
    ext; simp only
    linear_combination (I ^ 2 - 1) * (l : ℂ) * I_sq

/-- Complex conjugation as a permutation of the lattice. -/
def conjEquiv (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) : L.lattice ≃ L.lattice where
  toFun l := ⟨(starRingEnd ℂ) l, conj_mem h₁ h₂ l.2⟩
  invFun l := ⟨(starRingEnd ℂ) l, conj_mem h₁ h₂ l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

lemma tsum_mulI (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (f : ℂ → ℂ) :
    ∑' l : L.lattice, f (I * l) = ∑' l : L.lattice, f l :=
  (mulIEquiv h₁ h₂).tsum_eq (fun l => f l)

lemma tsum_conj (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (f : ℂ → ℂ) :
    ∑' l : L.lattice, f ((starRingEnd ℂ) l) = ∑' l : L.lattice, f l :=
  (conjEquiv h₁ h₂).tsum_eq (fun l => f l)

/-- `G₆ = 0` for a square lattice. -/
lemma G_six_eq_zero (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) : L.G 6 = 0 := by
  have h := tsum_mulI h₁ h₂ (fun z => (z ^ 6)⁻¹)
  have hI6 : I ^ 6 = -1 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, I_sq]; norm_num
  simp only [mul_pow, hI6, neg_one_mul, inv_neg, tsum_neg] at h
  have : L.G 6 = -L.G 6 := by rw [PeriodPair.G]; exact h.symm
  linear_combination this / 2

theorem g₃_eq_zero_of_square (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) : L.g₃ = 0 := by
  rw [PeriodPair.g₃, G_six_eq_zero h₁ h₂, mul_zero]

/-- `℘(i z) = -℘(z)`. -/
lemma weierstrassP_I_mul (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (z : ℂ) :
    ℘[L] (I * z) = -℘[L] z := by
  have h := tsum_mulI h₁ h₂ (fun w => 1 / (I * z - w) ^ 2 - 1 / w ^ 2)
  have hpt : ∀ w : ℂ, 1 / (I * z - I * w) ^ 2 - 1 / (I * w) ^ 2 =
      -(1 / (z - w) ^ 2 - 1 / w ^ 2) := by
    intro w
    rw [← mul_sub, mul_pow, mul_pow, I_sq]
    simp only [neg_one_mul, one_div, inv_neg]
    ring
  simp only [hpt, tsum_neg] at h
  change ℘[L] (I * z) = -(∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
  rw [h]
  rfl

/-- `℘(z̄) = conj ℘(z)`. -/
lemma weierstrassP_conj (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (z : ℂ) :
    ℘[L] ((starRingEnd ℂ) z) = (starRingEnd ℂ) (℘[L] z) := by
  have h := tsum_conj h₁ h₂ (fun w => 1 / ((starRingEnd ℂ) z - w) ^ 2 - 1 / w ^ 2)
  change _ = (starRingEnd ℂ) (∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
  rw [Complex.conj_tsum]
  simp only [map_sub, map_div₀, map_one, map_pow] at h ⊢
  rw [h]
  rfl

/-- `℘'(z̄) = conj ℘'(z)`. -/
lemma derivWeierstrassP_conj (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (z : ℂ) :
    ℘'[L] ((starRingEnd ℂ) z) = (starRingEnd ℂ) (℘'[L] z) := by
  have h := tsum_conj h₁ h₂ (fun w => 2 / ((starRingEnd ℂ) z - w) ^ 3)
  change _ = (starRingEnd ℂ) (-∑' l : L.lattice, 2 / (z - l) ^ 3)
  rw [map_neg, Complex.conj_tsum]
  simp only [map_sub, map_div₀, map_ofNat, map_pow] at h ⊢
  rw [h]
  rfl

/-- `℘` is real on the real line. -/
lemma weierstrassP_ofReal (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (t : ℝ) :
    ℘[L] (t : ℂ) = ((℘[L] (t : ℂ)).re : ℂ) := by
  have h := weierstrassP_conj h₁ h₂ (t : ℂ)
  rw [conj_ofReal] at h
  exact (Complex.conj_eq_iff_re.1 h.symm).symm

/-- `℘'` is real on the real line. -/
lemma derivWeierstrassP_ofReal (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (t : ℝ) :
    ℘'[L] (t : ℂ) = ((℘'[L] (t : ℂ)).re : ℂ) := by
  have h := derivWeierstrassP_conj h₁ h₂ (t : ℂ)
  rw [conj_ofReal] at h
  exact (Complex.conj_eq_iff_re.1 h.symm).symm

/-- Real points of `(0, a)` are not lattice points. -/
lemma ofReal_notMem (ha : 0 < a) (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) {t : ℝ} (ht0 : 0 < t)
    (hta : t < a) : (t : ℂ) ∉ L.lattice := by
  intro hm
  obtain ⟨m, n, h⟩ := (mem_lattice_sq h₁ h₂).1 hm
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [add_re, mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im, mul_zero, sub_zero,
    I_re, zero_mul, I_im, sub_self, mul_im, one_mul, zero_add, add_zero, add_im, mul_eq_zero,
    Int.cast_eq_zero] at hre him
  rcases him with hn | hn
  · subst hn
    have h1 : (0 : ℝ) < m := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    have h2 : (m : ℝ) < 1 := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    have h1' : (0 : ℤ) < m := by exact_mod_cast h1
    have h2' : m < (1 : ℤ) := by exact_mod_cast h2
    omega
  · exact absurd hn ha.ne'

end LSG.LemniscateIndep
