/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.SchneiderLang.Arith

/-!
# Sizes of algebraic numbers: house and denominator (Stage 3, D1/D3)

`K` is a number field with an embedding `ι : K →+* ℂ`. A complex number `z` has *size* `(A, d)`
(`Sz ι A d z`) if `z = ι x` with `x ∈ K`, `house x ≤ A` and `d · x` an algebraic integer.

* closure: `Sz.add`, `Sz.mul`, `Sz.pow`, `Sz.sum`, `Sz.prod`, `Sz.div_nat`, `Sz.mono`, …
* **`Sz.one_le_norm_mul`** (Liouville): `z ≠ 0`, `Sz ι A d z`, `1 ≤ A`, `1 ≤ d` give
  `1 ≤ |z| (d A)^{[K:ℚ]}`.
-/

open NumberField Finset

namespace LSG.Aux

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ)

/-- `z = ι x` with `house x ≤ A` and `d · x` integral. -/
def Sz (A : ℝ) (d : ℕ) (z : ℂ) : Prop :=
  ∃ x : K, ι x = z ∧ house x ≤ A ∧ IsIntegral ℤ ((d : K) * x)

variable {ι}

namespace Sz

lemma nonneg {A : ℝ} {d : ℕ} {z : ℂ} (h : Sz ι A d z) : 0 ≤ A := by
  obtain ⟨x, -, hx, -⟩ := h
  exact (house_nonneg x).trans hx

lemma mono {A A' : ℝ} {d d' : ℕ} {z : ℂ} (h : Sz ι A d z) (hA : A ≤ A') (hd : d ∣ d') :
    Sz ι A' d' z := by
  obtain ⟨x, rfl, hx, hi⟩ := h
  obtain ⟨e, rfl⟩ := hd
  refine ⟨x, rfl, hx.trans hA, ?_⟩
  have : ((d * e : ℕ) : K) * x = (e : K) * ((d : K) * x) := by push_cast; ring
  rw [this]
  have he : IsIntegral ℤ (e : K) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (e : ℤ))
  exact he.mul hi

lemma mono_le {A A' : ℝ} {d : ℕ} {z : ℂ} (h : Sz ι A d z) (hA : A ≤ A') : Sz ι A' d z :=
  h.mono hA dvd_rfl

lemma zero (d : ℕ) : Sz ι 0 d 0 :=
  ⟨0, by simp, by simp [house], by simpa using isIntegral_zero⟩

lemma natCast (n : ℕ) : Sz ι n 1 n := by
  refine ⟨n, by simp, ?_, by simpa using isIntegral_algebraMap (R := ℤ) (x := (n : ℤ))⟩
  have := house_nat_mul (1 : K) n
  simp only [mul_one] at this
  rw [this]
  have h1 : house (1 : K) ≤ 1 := by
    rw [house_eq_sup']
    simp
  calc (n : ℝ) * house (1 : K) ≤ n * 1 := by gcongr
    _ = n := mul_one _

lemma one : Sz ι 1 1 (1 : ℂ) := by simpa using natCast (ι := ι) 1

lemma add {A A' : ℝ} {d : ℕ} {z w : ℂ} (h : Sz ι A d z) (h' : Sz ι A' d w) :
    Sz ι (A + A') d (z + w) := by
  obtain ⟨x, rfl, hx, hi⟩ := h
  obtain ⟨y, rfl, hy, hj⟩ := h'
  refine ⟨x + y, by simp, (house_add_le x y).trans (add_le_add hx hy), ?_⟩
  rw [mul_add]; exact hi.add hj

lemma neg {A : ℝ} {d : ℕ} {z : ℂ} (h : Sz ι A d z) : Sz ι A d (-z) := by
  obtain ⟨x, rfl, hx, hi⟩ := h
  refine ⟨-x, by simp, ?_, by rw [mul_neg]; exact hi.neg⟩
  have : house (-x) = house x := by simp [house]
  rw [this]; exact hx

lemma sub {A A' : ℝ} {d : ℕ} {z w : ℂ} (h : Sz ι A d z) (h' : Sz ι A' d w) :
    Sz ι (A + A') d (z - w) := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

lemma mul {A A' : ℝ} {d d' : ℕ} {z w : ℂ} (h : Sz ι A d z) (h' : Sz ι A' d' w) :
    Sz ι (A * A') (d * d') (z * w) := by
  obtain ⟨x, rfl, hx, hi⟩ := h
  obtain ⟨y, rfl, hy, hj⟩ := h'
  refine ⟨x * y, by simp, (house_mul_le x y).trans ?_, ?_⟩
  · exact mul_le_mul hx hy (house_nonneg y) ((house_nonneg x).trans hx)
  · have : ((d * d' : ℕ) : K) * (x * y) = ((d : K) * x) * ((d' : K) * y) := by push_cast; ring
    rw [this]; exact hi.mul hj

lemma pow {A : ℝ} {d : ℕ} {z : ℂ} (h : Sz ι A d z) (k : ℕ) : Sz ι (A ^ k) (d ^ k) (z ^ k) := by
  induction k with
  | zero => simpa using one (ι := ι)
  | succ k ih => simpa [pow_succ] using ih.mul h

lemma sum {α : Type*} (s : Finset α) {A : α → ℝ} {d : ℕ} {z : α → ℂ}
    (h : ∀ i ∈ s, Sz ι (A i) d (z i)) : Sz ι (∑ i ∈ s, A i) d (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (ι := ι) d
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

lemma prod {α : Type*} (s : Finset α) {A : α → ℝ} {d : α → ℕ} {z : α → ℂ}
    (h : ∀ i ∈ s, Sz ι (A i) (d i) (z i)) :
    Sz ι (∏ i ∈ s, A i) (∏ i ∈ s, d i) (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one (ι := ι)
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

lemma intCast (k : ℤ) : Sz ι |(k : ℝ)| 1 (k : ℂ) := by
  have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  rcases Int.natAbs_eq k with h | h
  · have := natCast (ι := ι) k.natAbs
    rw [h]; simpa using this
  · have := (natCast (ι := ι) k.natAbs).neg
    rw [h]; simpa using this

lemma nat_mul {A : ℝ} {d : ℕ} {z : ℂ} (h : Sz ι A d z) (n : ℕ) : Sz ι (n * A) d (n * z) := by
  simpa using (natCast (ι := ι) n).mul h

lemma div_nat {A : ℝ} {d : ℕ} {z : ℂ} (h : Sz ι A d z) {n : ℕ} (hn : n ≠ 0) :
    Sz ι (A / n) (d * n) (z / n) := by
  obtain ⟨x, rfl, hx, hi⟩ := h
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨x / n, by simp, ?_, ?_⟩
  · have := house_nat_mul (x / n) n
    rw [mul_div_cancel₀ x hn'] at this
    have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [le_div_iff₀ hpos]
    calc house (x / n) * n = house x := by rw [this]; ring
      _ ≤ A := hx
  · have : ((d * n : ℕ) : K) * (x / n) = (d : K) * x := by
      push_cast; field_simp
    rw [this]; exact hi

/-- **Liouville's inequality** for a number of size `(A, d)`. -/
theorem one_le_norm_mul {A : ℝ} {d : ℕ} {z : ℂ} (h : Sz ι A d z) (hz : z ≠ 0) (hA : 1 ≤ A)
    (hd : 1 ≤ d) : 1 ≤ ‖z‖ * ((d : ℝ) * A) ^ Module.finrank ℚ K := by
  obtain ⟨x, rfl, hx, hi⟩ := h
  have hx0 : x ≠ 0 := by rintro rfl; simp at hz
  set β : 𝓞 K := ⟨(d : K) * x, hi⟩
  have hd0 : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hβ0 : β ≠ 0 := fun h0 => by
    have := congrArg Subtype.val h0
    simp only [β] at this
    exact mul_ne_zero hd0 hx0 this
  have key := LSG.SL.one_le_norm_mul_house_pow β hβ0 ι
  have hβ : ((β : 𝓞 K) : K) = (d : K) * x := rfl
  rw [hβ, map_mul, map_natCast, norm_mul, house_nat_mul, Complex.norm_natCast] at key
  have hn : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hdA : 1 ≤ (d : ℝ) * A := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hdx : (d : ℝ) * house x ≤ d * A := by gcongr
  have h0 : 0 ≤ (d : ℝ) * house x := mul_nonneg (Nat.cast_nonneg _) (house_nonneg x)
  calc (1 : ℝ) ≤ d * ‖ι x‖ * ((d : ℝ) * house x) ^ (Module.finrank ℚ K - 1) := key
    _ ≤ d * ‖ι x‖ * ((d : ℝ) * A) ^ (Module.finrank ℚ K - 1) := by gcongr
    _ ≤ (d * A) * ‖ι x‖ * ((d : ℝ) * A) ^ (Module.finrank ℚ K - 1) := by
        gcongr
        calc (d : ℝ) = d * 1 := (mul_one _).symm
          _ ≤ d * A := by gcongr
    _ = ‖ι x‖ * ((d : ℝ) * A) ^ Module.finrank ℚ K := by
        conv_rhs => rw [show Module.finrank ℚ K = (Module.finrank ℚ K - 1) + 1 by omega]
        ring

end Sz

end LSG.Aux
