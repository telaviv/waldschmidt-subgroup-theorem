/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.CheckerSound
import LSG.Jac.CheckerRange

/-!
# Soundness of slot-range splitting, shifted factors and identity tables

* `zeros_of_ranges`: if for every range `[lo, hi)` of a list covering the slots `[0, N)` the check
  `(evalO2 (trX.mapRows (rowsIn lo hi)) trY ps).allZero` passes, every slot of `evalO2 trX trY ps` is zero (the
  hypothesis `hV` of `sound2V`).
* `evalSP_shiftX`, `evalSP_shiftY`; `nfValid_of_idOK` (identity tables, `δ = 1`); `nfValid_of_sameRows`.
-/

namespace LSG.Jac

open Finset

lemma T.find_mapRows (f : List (ℕ × ℕ × Bool) → List (ℕ × ℕ × Bool)) (tr : T) (c : ℕ) :
    (tr.mapRows f).find c = ⟨(tr.find c).key, (tr.find c).idx, f (tr.find c).row, (tr.find c).ky⟩ := by
  induction tr with
  | leaf v => rfl
  | node k l r ihl ihr =>
    simp only [T.mapRows, T.find_node]
    split_ifs <;> assumption

lemma T.leaves_mapRows (f : List (ℕ × ℕ × Bool) → List (ℕ × ℕ × Bool)) (tr : T) :
    (tr.mapRows f).leaves = tr.leaves.map fun l => ⟨l.key, l.idx, f l.row, l.ky⟩ := by
  induction tr with
  | leaf v => rfl
  | node k l r ihl ihr => simp [T.mapRows, T.leaves, ihl, ihr]

lemma fiber_rowsIn (lo hi : ℕ) (r : List (ℕ × ℕ × Bool)) (j : ℕ) :
    fiber (rowL (rowsIn lo hi r)) j = if lo ≤ j ∧ j < hi then fiber (rowL r) j else 0 := by
  rw [fiber_rowL_eq, fiber_rowL_eq]
  unfold rowsIn
  induction r with
  | nil => simp
  | cons t r ih =>
    by_cases hP : (Nat.ble lo t.1 && Nat.blt t.1 hi) = true
    · rw [List.filter_cons, if_pos hP, List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hP
      split_ifs <;> first | rfl | omega | simp_all
    · rw [List.filter_cons, if_neg hP, ih, List.map_cons, List.sum_cons]
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, not_and_or] at hP
      by_cases hj : t.1 = j
      · subst hj; split_ifs with h <;> simp_all <;> omega
      · simp [hj]

lemma G_ite {R : Type*} [CommRing R] (ps : List Term) (P : Prop) [Decidable P] (F : ℕ → ℕ → R) :
    G ps (fun μ ν => if P then F μ ν else 0) = if P then G ps F else 0 := by
  split_ifs <;> simp [G]

/-- The value of a range-restricted computation. -/
theorem evalO2_range (trX trY : T) (hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ 8) (lo hi : ℕ)
    (ps : List Term) (j : ℕ) (hj : j < 2 ^ 8) :
    (evalO2 (trX.mapRows (rowsIn lo hi)) trY ps).V j =
      if lo ≤ j ∧ j < hi then (evalO2 trX trY ps).V j else 0 := by
  have hrows' : ∀ μ, ∀ t ∈ ((trX.mapRows (rowsIn lo hi)).find μ).row, t.1 < 2 ^ 8 := by
    intro μ t ht
    rw [T.find_mapRows] at ht
    exact hrows μ t (List.mem_of_mem_filter ht)
  rw [(evalO2_spec trY _ hrows' ps).2 j hj, (evalO2_spec trY _ hrows ps).2 j hj]
  simp only [T.find_mapRows, fiber_rowsIn, ite_mul, zero_mul]
  exact G_ite ps _ _

/-- Slots beyond the table vanish. -/
lemma evalO2_beyond (trX trY : T) {N : ℕ} (hN : N ≤ 2 ^ 8) (hrowsN : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < N)
    (ps : List Term) (j : ℕ) (hj : j < 2 ^ 8) (hNj : N ≤ j) : (evalO2 trX trY ps).V j = 0 := by
  have hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ 8 := fun μ t ht => lt_of_lt_of_le (hrowsN μ t ht) hN
  rw [(evalO2_spec trY _ hrows ps).2 j hj]
  have : ∀ μ, fiber (rowL (trX.find μ).row) j = 0 := by
    intro μ
    rw [fiber_rowL_eq]
    refine List.sum_eq_zero fun v hv => ?_
    simp only [List.mem_map] at hv
    obtain ⟨t, ht, rfl⟩ := hv
    have := hrowsN μ t ht
    rw [if_neg (by omega)]
  simp [this, G]

/-- **Range splitting.** -/
theorem zeros_of_ranges (trX trY : T) {N : ℕ} (hN : N ≤ 2 ^ 8)
    (hrowsN : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < N) (ps : List Term) (rs : List (ℕ × ℕ))
    (hcov : ((List.range N).all fun j => rs.any fun r => Nat.ble r.1 j && Nat.blt j r.2) = true)
    (hz : ∀ r ∈ rs, (evalO2 (trX.mapRows (rowsIn r.1 r.2)) trY ps).allZero = true) :
    ∀ j < 2 ^ 8, (evalO2 trX trY ps).V j = 0 := by
  have hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ 8 := fun μ t ht => lt_of_lt_of_le (hrowsN μ t ht) hN
  intro j hj
  by_cases hNj : N ≤ j
  · exact evalO2_beyond trX trY hN hrowsN ps j hj hNj
  · have h1 := List.all_eq_true.mp hcov j (List.mem_range.mpr (by omega))
    obtain ⟨r, hr, hrj⟩ := List.any_eq_true.mp h1
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hrj
    have hperf : (evalO2 (trX.mapRows (rowsIn r.1 r.2)) trY ps).Perfect 8 :=
      (evalO2_spec trY _ (fun μ t ht => by
        rw [T.find_mapRows] at ht; exact hrows μ t (List.mem_of_mem_filter ht)) ps).1
    have h2 := AT.allZero_spec hperf (hz r hr) j hj
    rw [evalO2_range trX trY hrows r.1 r.2 ps j hj, if_pos hrj] at h2
    exact h2

section Semantics

variable {R : Type*} [CommRing R]

lemma xmono_pow8 (x : Fin 9 → R) (f : Fin 9) : xmono x (8 ^ (f : ℕ)) = x f := by
  fin_cases f <;> simp [xmono, digit, Fin.prod_univ_succ]

lemma evalSP_shiftX (x y : Fin 9 → R) (f : Fin 9) (p : SP) (h : shiftXOK f p = true) :
    evalSP x y (shiftX f p) = x f * evalSP x y p := by
  unfold shiftXOK at h
  unfold evalSP shiftX
  rw [List.map_map, lsum_mul_left]
  refine lsum_congr fun r hr => ?_
  simp only [Function.comp_apply]
  rw [xmono_add x (List.all_eq_true.mp h r hr), xmono_pow8]; ring

lemma evalSP_shiftY (x y : Fin 9 → R) (f : Fin 9) (p : SP) (h : shiftYOK f p = true) :
    evalSP x y (shiftY f p) = y f * evalSP x y p := by
  unfold shiftYOK at h
  unfold evalSP shiftY
  rw [List.map_map, lsum_mul_left]
  refine lsum_congr fun r hr => ?_
  simp only [Function.comp_apply]
  unfold evalRow
  rw [List.map_map, lsum_mul_left, lsum_mul_left, lsum_mul_left]
  refine lsum_congr fun t ht => ?_
  simp only [Function.comp_apply]
  rw [xmono_add y (List.all_eq_true.mp (List.all_eq_true.mp h r hr) t ht), xmono_pow8]; ring

lemma nfValid_of_idOK (tr : T) (stdc : List ℕ) (h : idOK tr stdc = true) (x : Fin 9 → R) :
    NFValid tr stdc 1 x := by
  intro l hl
  have := List.all_eq_true.mp h l hl
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  rw [this.1]
  simp only [evalNF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sval,
    Bool.false_eq_true, if_false, Nat.cast_one, Int.cast_one, one_mul, this.2]

lemma nfValid_of_sameRows (t₁ t₂ : T) (stdc : List ℕ) (δ : ℕ) (h : sameRows t₁ t₂ = true)
    (x : Fin 9 → R) (h₁ : NFValid t₁ stdc δ x) : NFValid t₂ stdc δ x := by
  unfold sameRows at h
  rw [decide_eq_true_eq] at h
  intro l hl
  have : (l.key, l.row) ∈ t₁.leaves.map fun l => (l.key, l.row) := by
    rw [h]; exact List.mem_map_of_mem hl
  obtain ⟨l', hl', he⟩ := List.mem_map.mp this
  simp only [Prod.mk.injEq] at he
  rw [← he.1, ← he.2]
  exact h₁ l' hl'

end Semantics

end LSG.Jac
