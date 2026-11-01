/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Siegel's lemma for approximate complex linear conditions

W83 (Waldschmidt, Ann. Math. 117, 1983), proof of Prop. 2.1, uses Siegel's lemma in the form of
"Lemma 3.3 of W81": `L` integer unknowns `p_λ` with `|p_λ| ≤ B` can be chosen, not all zero, so that
finitely many complex linear forms `Σ_λ p_λ a_{iλ}` are smaller than a given `ε`, provided the
box of unknowns is larger than the number of cells of side `ε` that the values can occupy.

Mathlib's `Int.Matrix.exists_ne_zero_int_vec_norm_le` is for exact integer systems, so we prove the
approximate version directly by the pigeonhole principle (cells of side `ε` for real and imaginary
parts).

* `LSG.Aux.siegel_approx`: the statement.
-/

open Complex Finset

namespace LSG.Aux

/-- **Siegel's lemma for approximate complex conditions.** If `Σ_λ ‖a i λ‖ ≤ Y` for every
condition `i` and `(2⌈BY/ε⌉ + 2)^{2·#ι} < (B + 1)^L`, then there are integers `q_λ`, not all zero,
`|q_λ| ≤ B`, with `‖Σ_λ q_λ a i λ‖ ≤ 2ε` for every `i`. -/
theorem siegel_approx {ι : Type*} [Fintype ι] {L : ℕ} (a : ι → Fin L → ℂ) (B : ℕ) {Y ε : ℝ}
    (hε : 0 < ε) (hY : ∀ i, ∑ l, ‖a i l‖ ≤ Y)
    (hcount : (2 * ⌈(B : ℝ) * Y / ε⌉₊ + 2) ^ (2 * Fintype.card ι) < (B + 1) ^ L) :
    ∃ q : Fin L → ℤ, q ≠ 0 ∧ (∀ l, |q l| ≤ B) ∧ ∀ i, ‖∑ l, (q l : ℂ) * a i l‖ ≤ 2 * ε := by
  classical
  set M : ℕ := ⌈(B : ℝ) * Y / ε⌉₊ with hM
  -- the value of the `i`-th form at a box point
  let v : (Fin L → Fin (B + 1)) → ι → ℂ := fun p i => ∑ l, ((p l : ℕ) : ℂ) * a i l
  let f : (Fin L → Fin (B + 1)) → ι → ℤ × ℤ := fun p i =>
    (⌊(v p i).re / ε⌋, ⌊(v p i).im / ε⌋)
  let I : Finset ℤ := Icc (-(M : ℤ) - 1) M
  let t : Finset (ι → ℤ × ℤ) := Fintype.piFinset (fun _ => I ×ˢ I)
  have hcardI : I.card = 2 * M + 2 := by
    simp only [I, Int.card_Icc]
    omega
  have hcard_t : t.card = (2 * M + 2) ^ (2 * Fintype.card ι) := by
    simp only [t, Fintype.card_piFinset, card_product, hcardI, prod_const, card_univ]
    rw [pow_mul, ← sq]
  have hcard_s : (univ : Finset (Fin L → Fin (B + 1))).card = (B + 1) ^ L := by
    simp
  -- bound on the values
  have hv : ∀ p i, ‖v p i‖ ≤ B * Y := by
    intro p i
    calc ‖v p i‖ ≤ ∑ l, ‖((p l : ℕ) : ℂ) * a i l‖ := norm_sum_le _ _
      _ ≤ ∑ l, (B : ℝ) * ‖a i l‖ := by
          apply sum_le_sum
          intro l _
          rw [norm_mul, Complex.norm_natCast]
          gcongr
          exact_mod_cast Nat.lt_succ_iff.mp (p l).isLt
      _ = B * ∑ l, ‖a i l‖ := by rw [mul_sum]
      _ ≤ B * Y := by gcongr; exact hY i
  have hmem : ∀ x : ℝ, |x| ≤ B * Y → ⌊x / ε⌋ ∈ I := by
    intro x hx
    have hBY : (B : ℝ) * Y / ε ≤ M := Nat.le_ceil _
    have h1 : x / ε ≤ M := by
      calc x / ε ≤ B * Y / ε := by gcongr; exact (le_abs_self x).trans hx
        _ ≤ M := hBY
    have h2 : -(M : ℝ) ≤ x / ε := by
      have : -(B * Y / ε) ≤ x / ε := by
        rw [neg_div', div_le_div_iff_of_pos_right hε]
        linarith [neg_abs_le x]
      linarith
    simp only [I, mem_Icc]
    constructor
    · have := Int.lt_floor_add_one (x / ε)
      have h3 : ((-(M : ℤ) - 1 : ℤ) : ℝ) < ⌊x / ε⌋ := by
        push_cast; linarith
      exact_mod_cast h3.le
    · exact Int.floor_le_iff.mpr (by push_cast; linarith)
  have hmaps : ∀ p ∈ (univ : Finset (Fin L → Fin (B + 1))), f p ∈ t := by
    intro p _
    simp only [t, Fintype.mem_piFinset, mem_product]
    intro i
    exact ⟨hmem _ ((abs_re_le_norm _).trans (hv p i)), hmem _ ((abs_im_le_norm _).trans (hv p i))⟩
  have hlt : t.card < (univ : Finset (Fin L → Fin (B + 1))).card := by
    rw [hcard_t, hcard_s]; exact hcount
  obtain ⟨x, -, y, -, hxy, hfxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨fun l => ((x l : ℕ) : ℤ) - ((y l : ℕ) : ℤ), ?_, ?_, ?_⟩
  · intro h
    apply hxy
    funext l
    have := congrFun h l
    simp only [Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at this
    exact Fin.ext this
  · intro l
    have hx := Nat.lt_succ_iff.mp (x l).isLt
    have hy := Nat.lt_succ_iff.mp (y l).isLt
    change |((x l : ℕ) : ℤ) - ((y l : ℕ) : ℤ)| ≤ B
    rw [abs_le]
    constructor <;> omega
  · intro i
    have hfi := congrFun hfxy i
    simp only [f, Prod.mk.injEq] at hfi
    have hre := Int.abs_sub_lt_one_of_floor_eq_floor hfi.1
    have him := Int.abs_sub_lt_one_of_floor_eq_floor hfi.2
    have heq : ∑ l, (((((x l : ℕ) : ℤ) - ((y l : ℕ) : ℤ) : ℤ) : ℂ)) * a i l = v x i - v y i := by
      simp only [v, ← sum_sub_distrib]
      refine sum_congr rfl fun l _ => ?_
      push_cast; ring
    rw [heq]
    have hre' : |(v x i - v y i).re| < ε := by
      rw [← sub_div, abs_div, abs_of_pos hε, div_lt_one hε] at hre
      rwa [sub_re]
    have him' : |(v x i - v y i).im| < ε := by
      rw [← sub_div, abs_div, abs_of_pos hε, div_lt_one hε] at him
      rwa [sub_im]
    linarith [norm_le_abs_re_add_abs_im (v x i - v y i)]

end LSG.Aux
