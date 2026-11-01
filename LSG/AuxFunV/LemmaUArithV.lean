/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.LemmaUDirV
import LSG.AuxFunV.SzInv
import LSG.AuxFun.LemmaUArith

/-!
# Lemma U for the class `𝒞`: bookkeeping (Stage 5, phase 2)

* `SzS ι c S z`: `z` has house and a denominator `≤ e^{c S²}`. Closure under `+`, `·`, inverses
  (`SzS.add`, `SzS.mul`, `SzS.inv` via `sz_inv`), finite sums, common denominators
  (`SzS.common`).
* `prod_efacV`, `sum_NfacV`, `prod_AfacV`: the products over `FctV = Fct ⊕ Fin r` split into the
  abelian part and `r` fibre factors of exponent `D`.
* **`dominate`**: the Liouville quantity of `lemmaU_dirV` is at most that of the abelian
  `lemmaU_dir` with `U` replaced by `U − E`, as soon as the extra fibre factor
  `(e_fib^{rD} 2^{rD} A_fib^{rD} 2^k)^{deg}` is `≤ e^E`. So `lemmaU_arith` (applied with `U − E`)
  gives the hypothesis of `lemmaU_dirV`.
-/

open Finset

noncomputable section

namespace LSG.AuxV

open LSG.Aux

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

/-! ### Sizes `e^{c S²}` -/

/-- `z` has house and a denominator `≤ e^{c S²}`. -/
def SzS (ι : K →+* ℂ) (c S : ℝ) (z : ℂ) : Prop :=
  ∃ d : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ Real.exp (c * S ^ 2) ∧ Sz ι (Real.exp (c * S ^ 2)) d z

namespace SzS

variable {c c' S : ℝ} {z w : ℂ}

lemma mono (h : SzS ι c S z) (hc : c ≤ c') (hS : 1 ≤ S) : SzS ι c' S z := by
  obtain ⟨d, hd, hdle, hz⟩ := h
  have hle : Real.exp (c * S ^ 2) ≤ Real.exp (c' * S ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (by positivity))
  exact ⟨d, hd, hdle.trans hle, hz.mono_le hle⟩

lemma of_sz {A : ℝ} {d : ℕ} (h : Sz ι A d z) (hd : 1 ≤ d)
    (hA : A ≤ Real.exp (c * S ^ 2)) (hdc : (d : ℝ) ≤ Real.exp (c * S ^ 2)) : SzS ι c S z :=
  ⟨d, hd, hdc, h.mono_le hA⟩

lemma mul (h : SzS ι c S z) (h' : SzS ι c' S w) : SzS ι (c + c') S (z * w) := by
  obtain ⟨d, hd, hdle, hz⟩ := h
  obtain ⟨d', hd', hdle', hw⟩ := h'
  have he : Real.exp ((c + c') * S ^ 2) = Real.exp (c * S ^ 2) * Real.exp (c' * S ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  refine ⟨d * d', Nat.one_le_iff_ne_zero.mpr (by positivity), ?_, ?_⟩
  · rw [he]; push_cast; exact mul_le_mul hdle hdle' (by positivity) (by positivity)
  · rw [he]; exact hz.mul hw

lemma add (h : SzS ι c S z) (h' : SzS ι c' S w) (hc : 0 ≤ c) (hc' : 0 ≤ c') (hS : 1 ≤ S) :
    SzS ι (c + c' + 1) S (z + w) := by
  obtain ⟨d, hd, hdle, hz⟩ := h
  obtain ⟨d', hd', hdle', hw⟩ := h'
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have e1 : Real.exp (c * S ^ 2) ≤ Real.exp ((c + c') * S ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have e2 : Real.exp (c' * S ^ 2) ≤ Real.exp ((c + c') * S ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have h2 : (2 : ℝ) ≤ Real.exp (S ^ 2) := by
    have := Real.add_one_le_exp (S ^ 2); linarith
  have he : Real.exp ((c + c' + 1) * S ^ 2) = Real.exp ((c + c') * S ^ 2) * Real.exp (S ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have hE0 : 0 ≤ Real.exp ((c + c') * S ^ 2) := (Real.exp_pos _).le
  refine ⟨d * d', Nat.one_le_iff_ne_zero.mpr (by positivity), ?_, ?_⟩
  · have : ((d * d' : ℕ) : ℝ) ≤ Real.exp ((c + c') * S ^ 2) := by
      push_cast
      calc (d : ℝ) * d' ≤ Real.exp (c * S ^ 2) * Real.exp (c' * S ^ 2) :=
            mul_le_mul hdle hdle' (by positivity) (by positivity)
        _ = Real.exp ((c + c') * S ^ 2) := by rw [← Real.exp_add]; ring_nf
    rw [he]
    exact this.trans (le_mul_of_one_le_right hE0 (by linarith))
  · refine ((hz.mono le_rfl (Dvd.intro d' rfl)).add
      (hw.mono le_rfl (Dvd.intro_left d rfl))).mono_le ?_
    rw [he]
    calc Real.exp (c * S ^ 2) + Real.exp (c' * S ^ 2) ≤ 2 * Real.exp ((c + c') * S ^ 2) := by
          linarith
      _ ≤ Real.exp ((c + c') * S ^ 2) * Real.exp (S ^ 2) := by nlinarith

lemma neg (h : SzS ι c S z) : SzS ι c S (-z) := by
  obtain ⟨d, hd, hdle, hz⟩ := h; exact ⟨d, hd, hdle, hz.neg⟩

lemma sub (h : SzS ι c S z) (h' : SzS ι c' S w) (hc : 0 ≤ c) (hc' : 0 ≤ c') (hS : 1 ≤ S) :
    SzS ι (c + c' + 1) S (z - w) := by
  rw [sub_eq_add_neg]; exact h.add h'.neg hc hc' hS

lemma inv (h : SzS ι c S z) (hz : z ≠ 0) (hc : 0 ≤ c) :
    SzS ι ((2 * Module.finrank ℚ K + 1) * c) S z⁻¹ := by
  obtain ⟨d, hd, hdle, hzs⟩ := h
  have hE1 : 1 ≤ Real.exp (c * S ^ 2) := Real.one_le_exp (by positivity)
  obtain ⟨d', hd', hd'le, hinv⟩ := sz_inv hzs hz hE1 hd
  set n := Module.finrank ℚ K
  have hdA : (d : ℝ) * Real.exp (c * S ^ 2) ≤ Real.exp (2 * c * S ^ 2) := by
    calc (d : ℝ) * Real.exp (c * S ^ 2) ≤ Real.exp (c * S ^ 2) * Real.exp (c * S ^ 2) :=
          mul_le_mul_of_nonneg_right hdle (by positivity)
      _ = Real.exp (2 * c * S ^ 2) := by rw [← Real.exp_add]; ring_nf
  have hpow : ((d : ℝ) * Real.exp (c * S ^ 2)) ^ n ≤ Real.exp (2 * n * c * S ^ 2) := by
    calc ((d : ℝ) * Real.exp (c * S ^ 2)) ^ n ≤ Real.exp (2 * c * S ^ 2) ^ n :=
          pow_le_pow_left₀ (by positivity) hdA n
      _ = Real.exp (2 * n * c * S ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf
  have hfin : Real.exp (2 * n * c * S ^ 2) ≤ Real.exp ((2 * n + 1) * c * S ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg S])
  refine ⟨d', hd', hd'le.trans (hpow.trans hfin), hinv.mono_le ?_⟩
  calc (d : ℝ) * ((d : ℝ) * Real.exp (c * S ^ 2)) ^ n
      ≤ Real.exp (c * S ^ 2) * Real.exp (2 * n * c * S ^ 2) :=
        mul_le_mul hdle hpow (by positivity) (by positivity)
    _ = Real.exp ((2 * n + 1) * c * S ^ 2) := by rw [← Real.exp_add]; ring_nf

lemma sum {α : Type*} (s : Finset α) {z : α → ℂ} (hc : 0 ≤ c) (hS : 1 ≤ S)
    (h : ∀ a ∈ s, SzS ι c S (z a)) : SzS ι (s.card * (c + 1)) S (∑ a ∈ s, z a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, le_rfl, by simp, ?_⟩
    simpa using (Sz.zero (ι := ι) 1).mono_le (by positivity)
  | insert a s ha ih =>
    rw [sum_insert ha, card_insert_of_notMem ha]
    have h1 := h a (mem_insert_self a s)
    have h2 := ih fun b hb => h b (mem_insert_of_mem hb)
    refine (h1.add h2 hc (by positivity) hS).mono ?_ hS
    push_cast; nlinarith

/-- A common denominator for a finite family. -/
lemma common {α : Type*} [Fintype α] {z : α → ℂ} (h : ∀ a, SzS ι c S (z a)) :
    ∃ e : ℕ, 1 ≤ e ∧ (e : ℝ) ≤ Real.exp (Fintype.card α * c * S ^ 2) ∧
      ∀ a, Sz ι (Real.exp (c * S ^ 2)) e (z a) := by
  classical
  choose d hd hdle hz using h
  refine ⟨∏ a, d a, Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun a _ => by
    have := hd a; omega), ?_, fun a => (hz a).mono le_rfl (dvd_prod_of_mem _ (mem_univ a))⟩
  push_cast
  calc ∏ a, (d a : ℝ) ≤ ∏ _a : α, Real.exp (c * S ^ 2) :=
        prod_le_prod₀ (fun a _ => Nat.cast_nonneg _) fun a _ => hdle a
    _ = Real.exp (Fintype.card α * c * S ^ 2) := by
        rw [prod_const, card_univ, ← Real.exp_nat_mul]; ring_nf

end SzS

/-! ### Splitting the products over `FctV` -/

variable {d0 d1 m r : ℕ}

lemma prod_efacV (d dM l dX' efib A₀ A₁ D : ℕ) :
    ∏ f, efacV (d0 := d0) (d1 := d1) (m := m) (r := r) d dM l dX' efib f ^ NfacV A₀ A₁ D f =
      (∏ f : Fct d0 d1 m, efac d dM l dX' f ^ Nfac A₀ A₁ D f) * efib ^ (r * D) := by
  rw [Fintype.prod_sum_type]
  simp only [efacV, NfacV, prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm D r]

lemma sum_NfacV (A₀ A₁ D : ℕ) :
    ∑ f : FctV d0 d1 m r, NfacV A₀ A₁ D f = ∑ f : Fct d0 d1 m, Nfac A₀ A₁ D f + r * D := by
  rw [Fintype.sum_sum_type]
  simp [NfacV]

lemma prod_AfacV (aT hM C HX' H Afib : ℝ) (A₀ A₁ D : ℕ) :
    ∏ f, AfacV (d0 := d0) (d1 := d1) (m := m) (r := r) aT hM C HX' H Afib f ^ NfacV A₀ A₁ D f =
      (∏ f : Fct d0 d1 m, Afac aT hM C HX' H f ^ Nfac A₀ A₁ D f) * Afib ^ (r * D) := by
  rw [Fintype.prod_sum_type]
  simp only [AfacV, NfacV, prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm D r]

/-- **Domination of the Liouville quantity.** -/
lemma dominate {a U E ρk Lf P Afib B2 : ℝ} {deg Eab efib dk1 dk2 N Sab k : ℕ} (ha : 0 ≤ a)
    (hρ : 0 < ρk) (hLf : 0 ≤ Lf) (hP : 0 ≤ P) (hB2 : 0 ≤ B2)
    (h : a * Real.exp (-(U - E)) / ρk *
      (((Eab * dk1 * dk2 : ℕ) : ℝ) * (Lf * (2 ^ Sab * P) * B2 ^ k)) ^ deg < 1)
    (hX : ((efib : ℝ) ^ N * 2 ^ N * Afib ^ N * 2 ^ k) ^ deg ≤ Real.exp E) :
    a * Real.exp (-U) / ρk * ((((Eab * efib ^ N) * dk1 * dk2 : ℕ) : ℝ) *
      (Lf * (2 ^ (Sab + N) * (P * Afib ^ N)) * (2 * B2) ^ k)) ^ deg < 1 := by
  set Q := a * Real.exp (-(U - E)) / ρk *
    (((Eab * dk1 * dk2 : ℕ) : ℝ) * (Lf * (2 ^ Sab * P) * B2 ^ k)) ^ deg
  have hQ0 : 0 ≤ Q := by positivity
  have heq : a * Real.exp (-U) / ρk * ((((Eab * efib ^ N) * dk1 * dk2 : ℕ) : ℝ) *
      (Lf * (2 ^ (Sab + N) * (P * Afib ^ N)) * (2 * B2) ^ k)) ^ deg =
      Q * (Real.exp (-E) * ((efib : ℝ) ^ N * 2 ^ N * Afib ^ N * 2 ^ k) ^ deg) := by
    have he : Real.exp (-U) = Real.exp (-(U - E)) * Real.exp (-E) := by
      rw [← Real.exp_add]; ring_nf
    simp only [Q, he]
    push_cast
    rw [pow_add, mul_pow]
    ring
  have hle : Real.exp (-E) * ((efib : ℝ) ^ N * 2 ^ N * Afib ^ N * 2 ^ k) ^ deg ≤ 1 := by
    calc Real.exp (-E) * ((efib : ℝ) ^ N * 2 ^ N * Afib ^ N * 2 ^ k) ^ deg
        ≤ Real.exp (-E) * Real.exp E := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [heq]
  calc Q * (Real.exp (-E) * ((efib : ℝ) ^ N * 2 ^ N * Afib ^ N * 2 ^ k) ^ deg) ≤ Q * 1 :=
        mul_le_mul_of_nonneg_left hle hQ0
    _ = Q := mul_one Q
    _ < 1 := h

end LSG.AuxV
