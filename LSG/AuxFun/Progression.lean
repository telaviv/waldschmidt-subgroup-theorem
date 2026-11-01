/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Lagrange

/-!
# Lagrange constants for a real arithmetic progression

Nodes `x_j = (j − A)/K`, `0 ≤ j ≤ 2A` (a progression of `2A + 1` points of step `1/K` in
`[−A/K, A/K] ⊂ ℝ ⊂ ℂ`). This is the one-variable node set of the Tier 1 grid (`STAGE3_D2.md`, O2):
it is stable (up to truncation) under translation by `1`, the period in adapted coordinates.

Node products are factorials, `∏_{i ≠ k} |x_k − x_i| = k! (2A − k)! / K^{2A}`, so the Lagrange basis
satisfies `|ℓ_k(w)| ≤ (2(K|w| + A))^{2A} / (2A)!`. With `A ≤ rK < A + 1` and `R ≥ 4r` this gives the
constants used in `LSG.Aux.grid_interp`, all bounded by `100^{2A+1}`.

* `LSG.Aux.progNodes`, `LSG.Aux.card_progNodes`.
* `LSG.Aux.prog_constants`.
-/

open Complex Finset
open scoped Nat

namespace LSG.Aux

/-- The `j`-th node `(j − A)/K`. -/
noncomputable def pnode (A K j : ℕ) : ℂ := ((j : ℂ) - A) / K

/-- The progression `{(j − A)/K : 0 ≤ j ≤ 2A}`. -/
noncomputable def progNodes (A K : ℕ) : Finset ℂ := (range (2 * A + 1)).image (pnode A K)

lemma pnode_injective {A K : ℕ} (hK : K ≠ 0) : Function.Injective (pnode A K) := by
  intro i j h
  have hK' : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK
  unfold pnode at h
  rw [div_left_inj' hK', sub_left_inj] at h
  exact_mod_cast h

lemma card_progNodes {A K : ℕ} (hK : K ≠ 0) : (progNodes A K).card = 2 * A + 1 := by
  rw [progNodes, card_image_of_injective _ (pnode_injective hK), card_range]

lemma norm_pnode_sub (A K i j : ℕ) : ‖pnode A K i - pnode A K j‖ = |(i : ℝ) - j| / K := by
  unfold pnode
  rw [← sub_div, sub_sub_sub_cancel_right, norm_div, Complex.norm_natCast]
  congr 1
  rw [show ((i : ℂ) - j) = (((i : ℝ) - j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs]

lemma norm_pnode_le {A K j : ℕ} (hj : j ≤ 2 * A) : ‖pnode A K j‖ ≤ A / K := by
  have h0 : pnode A K j = pnode A K j - pnode A K A := by simp [pnode]
  rw [h0, norm_pnode_sub]
  gcongr
  rw [abs_le]
  constructor
  · have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  · have : (j : ℝ) ≤ 2 * A := by exact_mod_cast hj
    linarith

/-- `∏_{i ∈ [0, N), i ≠ k} |k − i| = k! (N − 1 − k)!`. -/
lemma prod_abs_sub_erase {N k : ℕ} (hk : k < N) :
    ∏ i ∈ (range N).erase k, |(k : ℝ) - i| = (k ! : ℝ) * ((N - 1 - k) ! : ℝ) := by
  have hsplit : (range N).erase k = range k ∪ Ico (k + 1) N := by
    ext i; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (range k) (Ico (k + 1) N) := by
    rw [disjoint_left]; intro i hi hi'; simp only [mem_range, mem_Ico] at hi hi'; omega
  rw [hsplit, prod_union hdisj]
  congr 1
  · -- the left part
    have h1 : ∀ i ∈ range k, |(k : ℝ) - i| = (((k - 1 - i : ℕ) : ℝ) + 1) := by
      intro i hi
      rw [mem_range] at hi
      rw [abs_of_nonneg (by have : (i : ℝ) ≤ k := by exact_mod_cast hi.le
                            linarith)]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    rw [prod_congr rfl h1, prod_range_reflect (fun j => ((j : ℕ) : ℝ) + 1) k]
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast; rfl
  · -- the right part
    rw [prod_Ico_eq_prod_range]
    have h2 : ∀ j ∈ range (N - (k + 1)), |(k : ℝ) - ((k + 1 + j : ℕ) : ℝ)| = (j : ℝ) + 1 := by
      intro j _
      push_cast
      rw [show (k : ℝ) - (k + 1 + j) = -((j : ℝ) + 1) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    rw [prod_congr rfl h2, show N - 1 - k = N - (k + 1) by omega,
      ← Finset.prod_range_add_one_eq_factorial]
    push_cast; rfl

lemma factorial_div_two_pow_le {m k : ℕ} (hk : k ≤ m) :
    (m ! : ℝ) / 2 ^ m ≤ (k ! : ℝ) * ((m - k) ! : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have hc := Nat.choose_le_two_pow m k
  have : (m ! : ℝ) = (m.choose k : ℝ) * k ! * (m - k) ! := by exact_mod_cast h.symm
  rw [this]
  have hc' : (m.choose k : ℝ) ≤ 2 ^ m := by exact_mod_cast hc
  have : (0 : ℝ) ≤ (k ! : ℝ) * (m - k) ! := by positivity
  nlinarith

/-- Bound for the Lagrange basis of the progression. -/
lemma norm_lagBasis_prog_le {A K k : ℕ} (hK : K ≠ 0) (hk : k ≤ 2 * A) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {w : ℂ} (hw : ‖w‖ ≤ ρ) :
    ‖lagBasis (progNodes A K) (pnode A K k) w‖ ≤ (2 * (K * ρ + A)) ^ (2 * A) / (2 * A)! := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hinj := pnode_injective (A := A) hK
  have hkN : k ∈ range (2 * A + 1) := mem_range.mpr (by omega)
  unfold lagBasis progNodes
  rw [← image_erase hinj, prod_image (fun i _ j _ h => hinj h), norm_prod]
  have hcard : ((range (2 * A + 1)).erase k).card = 2 * A := by
    rw [card_erase_of_mem hkN, card_range]; omega
  -- each factor
  have hfac : ∀ i ∈ (range (2 * A + 1)).erase k,
      ‖(w - pnode A K i) / (pnode A K k - pnode A K i)‖ ≤ (K * ρ + A) / |(k : ℝ) - i| := by
    intro i hi
    have hik : i ≠ k := ne_of_mem_erase hi
    have hi' : i ≤ 2 * A := by have := mem_range.mp (mem_of_mem_erase hi); omega
    have habs : 0 < |(k : ℝ) - i| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hik.symm))
    rw [norm_div, norm_pnode_sub, div_div_eq_mul_div, div_le_div_iff_of_pos_right habs]
    calc ‖w - pnode A K i‖ * K ≤ (ρ + A / K) * K := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add hw (norm_pnode_le hi'))
      _ = K * ρ + A := by field_simp
  calc ∏ i ∈ (range (2 * A + 1)).erase k, ‖(w - pnode A K i) / (pnode A K k - pnode A K i)‖
      ≤ ∏ i ∈ (range (2 * A + 1)).erase k, ((K * ρ + A) / |(k : ℝ) - i|) :=
        prod_le_prod₀ (fun _ _ => norm_nonneg _) hfac
    _ = (K * ρ + A) ^ (2 * A) / ((k ! : ℝ) * ((2 * A + 1 - 1 - k) ! : ℝ)) := by
        rw [prod_div_distrib, prod_const, hcard, prod_abs_sub_erase (by omega)]
    _ ≤ (K * ρ + A) ^ (2 * A) / ((2 * A)! / 2 ^ (2 * A)) := by
        gcongr
        rw [show 2 * A + 1 - 1 - k = 2 * A - k by omega]
        exact factorial_div_two_pow_le hk
    _ = (2 * (K * ρ + A)) ^ (2 * A) / (2 * A)! := by
        rw [mul_pow]; field_simp

/-- `y^m / m! ≤ (c e)^m` if `0 ≤ y ≤ c m`. -/
lemma pow_div_factorial_le_of_le {m : ℕ} {y c : ℝ} (hy : 0 ≤ y) (hyc : y ≤ c * m) :
    y ^ m / m ! ≤ (c * Real.exp 1) ^ m := by
  have hc : 0 ≤ c * m := hy.trans hyc
  have h1 : y ^ m / m ! ≤ (c * m) ^ m / m ! := by gcongr
  have h2 := Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hc0 : 0 ≤ c := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    exact nonneg_of_mul_nonneg_left hc this
  calc y ^ m / m ! ≤ (c * m) ^ m / m ! := h1
    _ = c ^ m * ((m : ℝ) ^ m / m !) := by rw [mul_pow]; ring
    _ ≤ c ^ m * Real.exp m := by gcongr
    _ = (c * Real.exp 1) ^ m := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_one]

/-- **The constants of the progression grid.** -/
theorem prog_constants {A K : ℕ} (hA : 1 ≤ A) {r R : ℝ} (hr : 0 < r) (hAr : (A : ℝ) ≤ r * K)
    (hrA : r * K < A + 1) (hR : 4 * r ≤ R) :
    K ≠ 0 ∧ (progNodes A K).card = 2 * A + 1 ∧ (∀ ζ ∈ progNodes A K, ‖ζ‖ ≤ r) ∧
    (∀ ζ ∈ progNodes A K, ∀ w : ℂ, ‖w‖ ≤ r → ‖lagBasis (progNodes A K) ζ w‖ ≤ 9 ^ (2 * A)) ∧
    (∀ ζ ∈ progNodes A K, ∀ w : ℂ, ‖w‖ = R →
      ‖lagBasis (progNodes A K) ζ w‖ ≤ (9 * R / r) ^ (2 * A)) ∧
    ((progNodes A K).card * 9 ^ (2 * A) + (progNodes A K).card * (9 * R / r) ^ (2 * A) *
      (2 * r / (R - r)) ^ (progNodes A K).card ≤ 100 ^ (2 * A + 1)) := by
  have hK : K ≠ 0 := by
    rintro rfl
    have : (1 : ℝ) ≤ A := by exact_mod_cast hA
    simp at hAr; linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have he : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hcard := card_progNodes (A := A) hK
  refine ⟨hK, hcard, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hζ
    refine (norm_pnode_le (by have := mem_range.mp hj; omega)).trans ?_
    rw [div_le_iff₀ hKpos]; linarith
  · intro ζ hζ w hw
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hζ
    refine (norm_lagBasis_prog_le hK (by have := mem_range.mp hj; omega) hr.le hw).trans ?_
    calc (2 * (K * r + A)) ^ (2 * A) / (2 * A)! ≤ (3 * Real.exp 1) ^ (2 * A) := by
          apply pow_div_factorial_le_of_le (by positivity)
          push_cast; nlinarith
      _ ≤ 9 ^ (2 * A) := by gcongr; linarith
  · intro ζ hζ w hw
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hζ
    refine (norm_lagBasis_prog_le hK (by have := mem_range.mp hj; omega) (by linarith)
      hw.le).trans ?_
    have hR0 : 0 ≤ R := by linarith
    have hRr : 1 ≤ R / r := by rw [le_div_iff₀ hr]; linarith
    calc (2 * (K * R + A)) ^ (2 * A) / (2 * A)! ≤ (3 * (R / r) * Real.exp 1) ^ (2 * A) := by
          apply pow_div_factorial_le_of_le (by positivity)
          have hKR : K * R = (R / r) * (r * K) := by field_simp
          have h1 : K * R ≤ (R / r) * (2 * A) := by
            rw [hKR]
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h2 : (A : ℝ) ≤ (R / r) * A := le_mul_of_one_le_left (by positivity) hRr
          push_cast; nlinarith
      _ ≤ (9 * R / r) ^ (2 * A) := by
          gcongr
          rw [mul_div_assoc]
          nlinarith [div_pos (by linarith : (0:ℝ) < R) hr]
  · rw [hcard]
    have hq : 2 * r / (R - r) ≤ 8 * r / (3 * R) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have hq0 : 0 ≤ 2 * r / (R - r) := div_nonneg (by linarith) (by linarith)
    have hRpos : 0 < R := by linarith
    have hq1 : 8 * r / (3 * R) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hprod : (9 * R / r) ^ (2 * A) * (2 * r / (R - r)) ^ (2 * A + 1) ≤ 24 ^ (2 * A) := by
      calc (9 * R / r) ^ (2 * A) * (2 * r / (R - r)) ^ (2 * A + 1)
          ≤ (9 * R / r) ^ (2 * A) * (8 * r / (3 * R)) ^ (2 * A) := by
            gcongr
            calc (2 * r / (R - r)) ^ (2 * A + 1) ≤ (8 * r / (3 * R)) ^ (2 * A + 1) := by gcongr
              _ ≤ (8 * r / (3 * R)) ^ (2 * A) := pow_le_pow_of_le_one (by positivity) hq1 (by omega)
        _ = 24 ^ (2 * A) := by
            rw [← mul_pow]; congr 1; field_simp; ring
    have h2A : ((2 * A + 1 : ℕ) : ℝ) ≤ 2 ^ (2 * A) := by
      have : 2 * A + 1 ≤ 2 ^ (2 * A) := Nat.lt_two_pow_self
      exact_mod_cast this
    calc ((2 * A + 1 : ℕ) : ℝ) * 9 ^ (2 * A) + ((2 * A + 1 : ℕ) : ℝ) * (9 * R / r) ^ (2 * A) *
          (2 * r / (R - r)) ^ (2 * A + 1)
        = ((2 * A + 1 : ℕ) : ℝ) * (9 ^ (2 * A) +
            (9 * R / r) ^ (2 * A) * (2 * r / (R - r)) ^ (2 * A + 1)) := by ring
      _ ≤ 2 ^ (2 * A) * (24 ^ (2 * A) + 24 ^ (2 * A)) :=
          mul_le_mul h2A (add_le_add (pow_le_pow_left₀ (by norm_num) (by norm_num) _) hprod)
            (by positivity) (by positivity)
      _ = 2 * 48 ^ (2 * A) := by rw [← two_mul, mul_left_comm, ← mul_pow]; norm_num
      _ ≤ 100 * 100 ^ (2 * A) := by
          gcongr
          · norm_num
          · norm_num
      _ = 100 ^ (2 * A + 1) := by ring

end LSG.Aux
