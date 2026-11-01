/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Progression

/-!
# Representatives of the grid modulo the periods `ℤ^κ × 0`

The grid of the Tier 1 construction (`STAGE3_D2.md`, O2) is `Zⁿ`, `Z = {(j − A)/K : 0 ≤ j ≤ 2A}`.
Modulo the period lattice `ℤ^κ × 0` every grid point is `s + ω` with `ω ∈ ℤ^κ × 0` small and `s` in
the *condition set*

  `𝕊 = {s : s_i ∈ {0, 1/K, …, (K−1)/K} (i < κ), s_i ∈ Z (i ≥ κ)}`,

which has `K^κ (2A+1)^{n−κ}` elements instead of `(2A+1)^n`: **this is the κ-saving of W83
Prop. 2.1** (conditions only on a fundamental domain of the periods).

* `LSG.Aux.condIdx`: the index set (a `Finset (Fin n → ℕ)`), `LSG.Aux.condPt`: the point.
* `LSG.Aux.card_condIdx`: `#𝕊 = K^κ N^{n−κ}`.
* `LSG.Aux.grid_decomp`: every grid point is `condPt k + ω`, `ω ∈ ℤ^κ × 0`, `‖ω‖ ≤ A/K + 1`.
-/

open Complex Finset

namespace LSG.Aux

variable {n : ℕ}

/-- Indices of the condition set: `k i < K` for `i < κ`, `k i < N` for `i ≥ κ`. -/
def condIdx (n κ K N : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun i : Fin n => if i.val < κ then range K else range N

/-- The condition point of index `k`. -/
noncomputable def condPt (κ A K : ℕ) (k : Fin n → ℕ) : Fin n → ℂ :=
  fun i => if i.val < κ then (k i : ℂ) / K else pnode A K (k i)

lemma card_condIdx {κ : ℕ} (hκ : κ ≤ n) (K N : ℕ) :
    (condIdx n κ K N).card = K ^ κ * N ^ (n - κ) := by
  rw [condIdx, Fintype.card_piFinset]
  have : ∀ i : Fin n, (if i.val < κ then range K else range N).card =
      (fun j : ℕ => if j < κ then K else N) i.val := by
    intro i; by_cases h : i.val < κ <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => this i,
    Fin.prod_univ_eq_prod_range (fun j : ℕ => if j < κ then K else N) n,
    ← prod_range_mul_prod_Ico _ hκ]
  congr 1
  · rw [prod_ite_of_true fun j hj => mem_range.mp hj, prod_const, card_range]
  · rw [prod_ite_of_false fun j hj => by simp only [mem_Ico] at hj; omega, prod_const,
      Nat.card_Ico]

lemma norm_condPt_le {κ A K : ℕ} (hK : K ≠ 0) {N : ℕ} (hN : N = 2 * A + 1) {k : Fin n → ℕ}
    (hk : k ∈ condIdx n κ K N) {ρ : ℝ} (h1 : 1 ≤ ρ) (hA : (A : ℝ) / K ≤ ρ) :
    ‖condPt κ A K k‖ ≤ ρ := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
  have hki := Fintype.mem_piFinset.mp hk i
  simp only [condPt]
  split_ifs with hi
  · simp only [hi, ↓reduceIte, mem_range] at hki
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_iff₀ hKpos]
    have : (k i : ℝ) ≤ K := by exact_mod_cast hki.le
    nlinarith
  · simp only [hi, ↓reduceIte, mem_range] at hki
    exact (norm_pnode_le (by omega)).trans hA

/-- **Decomposition of grid points modulo `ℤ^κ × 0`.** -/
theorem grid_decomp {κ A K : ℕ} (hK : K ≠ 0) {g : Fin n → ℂ} (hg : ∀ i, g i ∈ progNodes A K) :
    ∃ k ∈ condIdx n κ K (2 * A + 1), ∃ q : Fin n → ℤ, (∀ i : Fin n, κ ≤ i.val → q i = 0) ∧
      g = condPt κ A K k + (fun i => (q i : ℂ)) ∧ ‖(fun i => (q i : ℂ))‖ ≤ A / K + 1 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hKz : (0 : ℤ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  choose j hj hjg using fun i => mem_image.mp (hg i)
  -- `t i = j i − A = K q i + m i`
  set t : Fin n → ℤ := fun i => (j i : ℤ) - A with ht
  refine ⟨fun i => if i.val < κ then (t i % K).toNat else j i, ?_,
    fun i => if i.val < κ then t i / K else 0, ?_, ?_, ?_⟩
  · refine Fintype.mem_piFinset.mpr fun i => ?_
    split_ifs with hi
    · have h1 := Int.emod_nonneg (t i) hKz.ne'
      have h2 := Int.emod_lt_of_pos (t i) hKz
      rw [mem_range]; omega
    · exact hj i
  · intro i hi; simp [show ¬ i.val < κ by omega]
  · funext i
    simp only [condPt, Pi.add_apply]
    split_ifs with hi
    · have h1 := Int.emod_nonneg (t i) hKz.ne'
      have hdiv := Int.mul_ediv_add_emod (t i) K
      rw [← hjg i]
      have hcast : (((t i % K).toNat : ℕ) : ℂ) = ((t i % K : ℤ) : ℂ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
      have key : ((t i : ℤ) : ℂ) = K * ((t i / K : ℤ) : ℂ) + ((t i % K : ℤ) : ℂ) := by
        exact_mod_cast hdiv.symm
      have hK' : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK
      rw [hcast, pnode, show (j i : ℂ) - A = ((t i : ℤ) : ℂ) by simp [ht], key]
      field_simp
      ring
    · simp [hjg i]
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    simp only
    split_ifs with hi
    · rw [Complex.norm_intCast]
      have h1 := Int.emod_nonneg (t i) hKz.ne'
      have h2 := Int.emod_lt_of_pos (t i) hKz
      have hdiv := Int.mul_ediv_add_emod (t i) K
      have hji : j i ≤ 2 * A := by have := mem_range.mp (hj i); omega
      -- real versions
      set qq : ℤ := t i / K
      set mm : ℤ := t i % K
      have hd : (K : ℝ) * qq + mm = (j i : ℝ) - A := by
        have := congrArg (fun x : ℤ => (x : ℝ)) hdiv
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
        rw [this]; simp [ht]
      have hm0 : (0 : ℝ) ≤ mm := by exact_mod_cast h1
      have hmK : (mm : ℝ) < K := by exact_mod_cast h2
      have hj0 : (0 : ℝ) ≤ j i := Nat.cast_nonneg _
      have hjA : (j i : ℝ) ≤ 2 * A := by exact_mod_cast hji
      rw [abs_le]
      constructor
      · have : (K : ℝ) * (-qq) ≤ A + K := by nlinarith
        have h3 : -(qq : ℝ) ≤ A / K + 1 := by
          rw [div_add_one hKpos.ne', le_div_iff₀ hKpos]; linarith
        linarith
      · have : (K : ℝ) * qq ≤ A := by nlinarith
        have h3 : (qq : ℝ) ≤ A / K := by rw [le_div_iff₀ hKpos]; linarith
        linarith
    · simp only [Int.cast_zero, norm_zero]; positivity

end LSG.Aux
