/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LawSize
import LSG.Elliptic.AdditionLawsGroup
import LSG.Weierstrass.Dictionary

/-!
# Algebraic points `exp_E(Σ hⱼ zⱼ)` and their sizes (Stage 3, D1)

`IsRep L z X`: `X ∈ ℂ³` is a nonzero cone vector on `E_L` representing `exp_E(z)`
(`toPoint L.g₂ L.g₃ X = expE L z`).

* `isRep_lawk`: one of the two addition laws represents `exp(z + w)` (`LSG.Elliptic.exists_law`).
* `exists_den`: every element of a number field has a denominator.
* **`exists_alg_points`**: given representatives of `exp(zⱼ)` with coordinates in a number field `K`,
  for every `h ∈ ℕ^μ` with `hⱼ ≤ 2^k` there is a representative of `exp(Σ hⱼ zⱼ)` whose coordinates
  have house `≤ e^{A 4^k}` and a common denominator `≤ e^{A 4^k}` (balanced splitting
  `h = ⌈h/2⌉ + ⌊h/2⌋`; the size `s` satisfies `s(k+1) ≤ 4 s(k) + c`).
* `exists_alg_points_S`: the same with `hⱼ ≤ S` and bound `e^{A S²}` (`S ≥ 1`).
-/

open Finset NumberField LSG.Elliptic LSG.Weierstrass

noncomputable section

namespace LSG.Aux

variable (L : PeriodPair)

/-- `X` is a nonzero cone vector on `E_L` representing `exp_E(z)`. -/
def IsRep (z : ℂ) (X : Fin 3 → ℂ) : Prop :=
  X ≠ 0 ∧ Fv L.g₂ L.g₃ X = 0 ∧ toPoint L.g₂ L.g₃ X = expE L z

lemma isRep_zero : IsRep L 0 O := by
  refine ⟨fun h => by simpa [O] using congrFun h 1, Fv_O _ _, ?_⟩
  rw [toPoint_O, expE_zero]; rfl

lemma Fv_lawk {g₂ g₃ : ℂ} {P Q : Fin 3 → ℂ} (hP : Fv g₂ g₃ P = 0) (hQ : Fv g₂ g₃ Q = 0)
    (k : Fin 2) : Fv g₂ g₃ (lawk k g₂ g₃ P Q) = 0 := by
  fin_cases k
  · simp only [lawk]; simpa [hP, hQ] using Fv_law₁ g₂ g₃ P Q
  · simp only [lawk]; simpa [hP, hQ] using Fv_law₂ g₂ g₃ P Q

lemma isRep_lawk {z w : ℂ} {X Y : Fin 3 → ℂ} (hX : IsRep L z X) (hY : IsRep L w Y) :
    ∃ k : Fin 2, IsRep L (z + w) (lawk k L.g₂ L.g₃ X Y) := by
  classical
  obtain ⟨k, hne, hpt⟩ := exists_law (two_ne_zero) (discr_ne_zero L) hX.2.1 hY.2.1 hX.1 hY.1
  refine ⟨k, hne, Fv_lawk hX.2.1 hY.2.1 k, ?_⟩
  change toPoint L.g₂ L.g₃ (![law₁ L.g₂ L.g₃ X Y, law₂ L.g₂ L.g₃ X Y] k) = _
  rw [hpt, hX.2.2, hY.2.2, expE_add]; rfl

lemma exists_den {K : Type*} [Field K] [NumberField K] (x : K) :
    ∃ d : ℕ, 1 ≤ d ∧ IsIntegral ℤ ((d : K) * x) := by
  obtain ⟨y, hy, hi⟩ := exists_integral_multiples ℤ ℚ (L := K) {x}
  have hi := hi x (by simp)
  refine ⟨y.natAbs, by omega, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · rw [h] at hi; simpa [zsmul_eq_mul] using hi
  · rw [h] at hi; simpa [zsmul_eq_mul] using hi.neg

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

/-- A weighted denominator for `(g₂, g₃)`. -/
lemma exists_wden (γ₂ γ₃ : K) :
    ∃ l : ℕ, 1 ≤ l ∧ IsIntegral ℤ ((l : K) ^ 4 * γ₂) ∧ IsIntegral ℤ ((l : K) ^ 6 * γ₃) := by
  obtain ⟨a, ha, hai⟩ := exists_den γ₂
  obtain ⟨b, hb, hbi⟩ := exists_den γ₃
  have hint : ∀ n : ℕ, IsIntegral ℤ (n : K) := fun n => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (n : ℤ))
  refine ⟨a * b, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · have : ((a * b : ℕ) : K) ^ 4 * γ₂ = ((a ^ 3 * b ^ 4 : ℕ) : K) * ((a : K) * γ₂) := by
      push_cast; ring
    rw [this]; exact (hint _).mul hai
  · have : ((a * b : ℕ) : K) ^ 6 * γ₃ = ((a ^ 6 * b ^ 5 : ℕ) : K) * ((b : K) * γ₃) := by
      push_cast; ring
    rw [this]; exact (hint _).mul hbi

/-- Representatives of finite sums, with some size. -/
lemma exists_rep_finset {γ₂ γ₃ : K} (h₂ : ι γ₂ = L.g₂) (h₃ : ι γ₃ = L.g₃) {μ : ℕ}
    (z : Fin μ → ℂ) (X₀ : Fin μ → Fin 3 → ℂ) (hX₀ : ∀ j, IsRep L (z j) (X₀ j))
    (hK : ∀ j, ∃ H : ℝ, ∃ d : ℕ, 1 ≤ d ∧ ∀ i, Sz ι H d (X₀ j i)) (s : Finset (Fin μ)) :
    ∃ (X : Fin 3 → ℂ) (H : ℝ) (d : ℕ), IsRep L (∑ j ∈ s, z j) X ∧ 1 ≤ d ∧
      ∀ i, Sz ι H d (X i) := by
  classical
  obtain ⟨l, hl1, hl₂, hl₃⟩ := exists_wden γ₂ γ₃
  obtain ⟨C, -, hC⟩ := sz_lawk ι (le_max_left (house γ₂) (house γ₃))
    (le_max_right (house γ₂) (house γ₃)) hl₂ hl₃
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨O, 1, 1, by simpa using isRep_zero L, le_rfl, fun i => ?_⟩
    fin_cases i
    · simpa [O] using (Sz.zero (ι := ι) 1).mono_le zero_le_one
    · simpa [O] using Sz.one (ι := ι)
    · simpa [O] using (Sz.zero (ι := ι) 1).mono_le zero_le_one
  | insert a s ha ih =>
    obtain ⟨X, H, d, hX, hd, hXs⟩ := ih
    obtain ⟨H', d', hd', hX'⟩ := hK a
    obtain ⟨k, hk⟩ := isRep_lawk L hX (hX₀ a)
    refine ⟨lawk k L.g₂ L.g₃ X (X₀ a), C * H ^ 2 * H' ^ 2, l ^ 12 * d ^ 2 * d' ^ 2, ?_,
      Nat.one_le_iff_ne_zero.mpr (by positivity), fun i => ?_⟩
    · rw [sum_insert ha, add_comm]; exact hk
    · have := hC k X (X₀ a) H H' d d' hXs hX' i
      rw [h₂, h₃] at this
      exact this

/-- **Algebraic points of `E` along `Σ hⱼ zⱼ`, with sizes `e^{A 4^k}` for `hⱼ ≤ 2^k`.** -/
theorem exists_alg_points {γ₂ γ₃ : K} (h₂ : ι γ₂ = L.g₂) (h₃ : ι γ₃ = L.g₃) {μ : ℕ}
    (z : Fin μ → ℂ) (X₀ : Fin μ → Fin 3 → ℂ) (hX₀ : ∀ j, IsRep L (z j) (X₀ j))
    (hK : ∀ j, ∃ H : ℝ, ∃ d : ℕ, 1 ≤ d ∧ ∀ i, Sz ι H d (X₀ j i)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ, ∀ h : Fin μ → ℕ, (∀ j, h j ≤ 2 ^ k) →
      ∃ (X : Fin 3 → ℂ) (d : ℕ), IsRep L (∑ j, (h j : ℂ) * z j) X ∧ 1 ≤ d ∧
        (d : ℝ) ≤ Real.exp (A * 4 ^ k) ∧ ∀ i, Sz ι (Real.exp (A * 4 ^ k)) d (X i) := by
  classical
  obtain ⟨l, hl1, hl₂, hl₃⟩ := exists_wden γ₂ γ₃
  obtain ⟨C, hC0, hC⟩ := sz_lawk ι (le_max_left (house γ₂) (house γ₃))
    (le_max_right (house γ₂) (house γ₃)) hl₂ hl₃
  -- base data for the `0/1` vectors
  choose Xs Hs ds hXs hds hSs using fun s : Finset (Fin μ) =>
    exists_rep_finset L h₂ h₃ z X₀ hX₀ hK s
  set B : ℝ := ∑ s : Finset (Fin μ), (|Hs s| + ds s) + 1
  have hHB : ∀ s, Hs s ≤ B := fun s => by
    have := single_le_sum (f := fun s : Finset (Fin μ) => |Hs s| + (ds s : ℝ))
      (fun s _ => by positivity) (mem_univ s)
    linarith [le_abs_self (Hs s), (Nat.cast_nonneg (ds s) : (0 : ℝ) ≤ ds s)]
  have hdB : ∀ s, (ds s : ℝ) ≤ B := fun s => by
    have := single_le_sum (f := fun s : Finset (Fin μ) => |Hs s| + (ds s : ℝ))
      (fun s _ => by positivity) (mem_univ s)
    linarith [abs_nonneg (Hs s)]
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ s : Finset (Fin μ), (|Hs s| + (ds s : ℝ)) := sum_nonneg fun s _ => by positivity
    linarith
  -- constants: `c` absorbs the law constants, `A` the base case
  set c : ℝ := Real.log (C + 1) + 12 * Real.log l
  have hc0 : 0 ≤ c := by
    have : 0 ≤ Real.log (C + 1) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast hl1)
    positivity
  set A : ℝ := Real.log B + c
  have hA0 : 0 ≤ A := add_nonneg (Real.log_nonneg hB1) hc0
  refine ⟨A, hA0, ?_⟩
  -- the invariant, with the `− c` slack
  have main : ∀ k : ℕ, ∀ h : Fin μ → ℕ, (∀ j, h j ≤ 2 ^ k) →
      ∃ (X : Fin 3 → ℂ) (d : ℕ), IsRep L (∑ j, (h j : ℂ) * z j) X ∧ 1 ≤ d ∧
        (d : ℝ) ≤ Real.exp (A * 4 ^ k - c) ∧ ∀ i, Sz ι (Real.exp (A * 4 ^ k - c)) d (X i) := by
    intro k
    induction k with
    | zero =>
      intro h hh
      set s : Finset (Fin μ) := univ.filter fun j => h j = 1
      have hsum : ∑ j, (h j : ℂ) * z j = ∑ j ∈ s, z j := by
        rw [sum_filter]
        refine sum_congr rfl fun j _ => ?_
        have := hh j
        simp only [pow_zero] at this
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h0 | h1
        · simp [h0]
        · simp [h1]
      have hexp : Real.exp (A * 4 ^ 0 - c) = B := by
        simp only [pow_zero, mul_one, A, add_sub_cancel_right]
        exact Real.exp_log (by linarith)
      refine ⟨Xs s, ds s, by rw [hsum]; exact hXs s, hds s, ?_, fun i => ?_⟩
      · rw [hexp]; exact hdB s
      · rw [hexp]
        exact (hSs s i).mono_le (hHB s)
    | succ k ih =>
      intro h hh
      obtain ⟨X₁, d₁, hX₁, hd₁, hd₁le, hS₁⟩ := ih (fun j => (h j + 1) / 2) fun j => by
        have := hh j; rw [pow_succ] at this; omega
      obtain ⟨X₂, d₂, hX₂, hd₂, hd₂le, hS₂⟩ := ih (fun j => h j / 2) fun j => by
        have := hh j; rw [pow_succ] at this; omega
      obtain ⟨kk, hkk⟩ := isRep_lawk L hX₁ hX₂
      have hsplit : ∑ j, (((h j + 1) / 2 : ℕ) : ℂ) * z j + ∑ j, ((h j / 2 : ℕ) : ℂ) * z j =
          ∑ j, (h j : ℂ) * z j := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        rw [← add_mul]; congr 1; exact_mod_cast (by omega : (h j + 1) / 2 + h j / 2 = h j)
      set E := Real.exp (A * 4 ^ k - c)
      have hE : Real.exp (A * 4 ^ (k + 1) - c) = Real.exp (4 * (A * 4 ^ k - c) + 3 * c) := by
        congr 1; rw [pow_succ]; ring
      have hlaw : Real.exp (c) ≥ (C + 1) * (l : ℝ) ^ 12 := by
        simp only [c]
        rw [Real.exp_add, Real.exp_log (by linarith)]
        rw [show 12 * Real.log l = Real.log ((l : ℝ) ^ 12) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
      have hE0 : 0 < E := Real.exp_pos _
      refine ⟨lawk kk L.g₂ L.g₃ X₁ X₂, l ^ 12 * d₁ ^ 2 * d₂ ^ 2, by rw [← hsplit]; exact hkk,
        Nat.one_le_iff_ne_zero.mpr (by positivity), ?_, fun i => ?_⟩
      · rw [hE]
        push_cast
        have h4 : E ^ 2 * E ^ 2 = Real.exp (4 * (A * 4 ^ k - c)) := by
          rw [← pow_add, ← Real.exp_nat_mul]; push_cast; ring_nf
        have h1 : (d₁ : ℝ) ^ 2 * (d₂ : ℝ) ^ 2 ≤ Real.exp (4 * (A * 4 ^ k - c)) := by
          rw [← h4]; gcongr
        have h2 : (l : ℝ) ^ 12 ≤ Real.exp (3 * c) := by
          calc (l : ℝ) ^ 12 ≤ (C + 1) * (l : ℝ) ^ 12 := by
                nlinarith [pow_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l) 12]
            _ ≤ Real.exp c := hlaw
            _ ≤ Real.exp (3 * c) := Real.exp_le_exp.mpr (by linarith)
        rw [Real.exp_add]
        calc (l : ℝ) ^ 12 * (d₁ : ℝ) ^ 2 * (d₂ : ℝ) ^ 2
            = (l : ℝ) ^ 12 * ((d₁ : ℝ) ^ 2 * (d₂ : ℝ) ^ 2) := by ring
          _ ≤ Real.exp (3 * c) * Real.exp (4 * (A * 4 ^ k - c)) := by gcongr
          _ = Real.exp (4 * (A * 4 ^ k - c)) * Real.exp (3 * c) := by ring
      · have := hC kk X₁ X₂ E E d₁ d₂ hS₁ hS₂ i
        rw [h₂, h₃] at this
        refine this.mono_le ?_
        rw [hE, Real.exp_add]
        have h2 : C ≤ Real.exp (3 * c) := by
          calc C ≤ (C + 1) * 1 := by linarith
            _ ≤ (C + 1) * (l : ℝ) ^ 12 := by
                gcongr; exact one_le_pow₀ (by exact_mod_cast hl1)
            _ ≤ Real.exp c := hlaw
            _ ≤ Real.exp (3 * c) := Real.exp_le_exp.mpr (by linarith)
        have h4 : E ^ 2 * E ^ 2 = Real.exp (4 * (A * 4 ^ k - c)) := by
          rw [← pow_add, ← Real.exp_nat_mul]; push_cast; ring_nf
        calc C * E ^ 2 * E ^ 2 = C * (E ^ 2 * E ^ 2) := by ring
          _ ≤ Real.exp (3 * c) * (E ^ 2 * E ^ 2) := by gcongr
          _ = Real.exp (4 * (A * 4 ^ k - c)) * Real.exp (3 * c) := by rw [h4]; ring
  intro k h hh
  obtain ⟨X, d, hX, hd, hdle, hS⟩ := main k h hh
  have hle : Real.exp (A * 4 ^ k - c) ≤ Real.exp (A * 4 ^ k) :=
    Real.exp_le_exp.mpr (by linarith)
  exact ⟨X, d, hX, hd, hdle.trans hle, fun i => (hS i).mono_le hle⟩

/-- `exists_alg_points` with `hⱼ ≤ S` and bound `e^{A S²}`. -/
theorem exists_alg_points_S {γ₂ γ₃ : K} (h₂ : ι γ₂ = L.g₂) (h₃ : ι γ₃ = L.g₃) {μ : ℕ}
    (z : Fin μ → ℂ) (X₀ : Fin μ → Fin 3 → ℂ) (hX₀ : ∀ j, IsRep L (z j) (X₀ j))
    (hK : ∀ j, ∃ H : ℝ, ∃ d : ℕ, 1 ≤ d ∧ ∀ i, Sz ι H d (X₀ j i)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ S : ℕ, 1 ≤ S → ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
      ∃ (X : Fin 3 → ℂ) (d : ℕ), IsRep L (∑ j, (h j : ℂ) * z j) X ∧ 1 ≤ d ∧
        (d : ℝ) ≤ Real.exp (A * S ^ 2) ∧ ∀ i, Sz ι (Real.exp (A * S ^ 2)) d (X i) := by
  obtain ⟨A, hA0, hA⟩ := exists_alg_points L h₂ h₃ z X₀ hX₀ hK
  refine ⟨4 * A, by positivity, fun S hS h hh => ?_⟩
  set k := Nat.log 2 S + 1
  have hlt : S < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) S
  have hle : 2 ^ k ≤ 2 * S := by
    have := Nat.pow_log_le_self 2 (by omega : S ≠ 0)
    simp only [k, pow_succ]; omega
  obtain ⟨X, d, hX, hd, hdle, hS'⟩ := hA k h fun j => (hh j).trans hlt.le
  have h4 : A * 4 ^ k ≤ 4 * A * S ^ 2 := by
    have : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    have h2 : ((2 : ℝ) ^ k) ≤ 2 * S := by exact_mod_cast hle
    have h0 : (0 : ℝ) ≤ 2 ^ k := by positivity
    calc A * ((2 : ℝ) ^ k) ^ 2 ≤ A * (2 * S) ^ 2 := by gcongr
      _ = 4 * A * S ^ 2 := by ring
  have hE := Real.exp_le_exp.mpr h4
  exact ⟨X, d, hX, hd, hdle.trans hE, fun i => (hS' i).mono_le hE⟩

end LSG.Aux
