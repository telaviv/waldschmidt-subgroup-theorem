/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.CheckerSound
import LSG.Jac.CheckerSplit

/-!
# Soundness of split certificates

`evalO2_split`: if the accumulator after `ps₁` equals the literal `L` slotwise and the computation continued from `L`
over `ps₂` ends at zero, then every slot of `evalO2 trX trY (ps₁ ++ ps₂)` is zero (the hypothesis of `sound2V`).
-/

namespace LSG.Jac

open Finset

lemma AT.perfect_ofFn : ∀ (d : ℕ) (f : ℕ → ℕ × ℕ), (AT.ofFn d f).Perfect d
  | 0, _ => .leaf _
  | d + 1, f => .node (AT.perfect_ofFn d _) (AT.perfect_ofFn d _)

lemma AT.get_ofFn : ∀ (d : ℕ) (f : ℕ → ℕ × ℕ) (j : ℕ), j < 2 ^ d → (AT.ofFn d f).get j = f j
  | 0, f, j, hj => by
    simp only [pow_zero, Nat.lt_one_iff] at hj; subst hj; rfl
  | d + 1, f, j, hj => by
    have hj2 : j / 2 < 2 ^ d := by rw [pow_succ] at hj; omega
    rw [AT.ofFn, AT.get_node]
    split_ifs with h
    · rw [AT.get_ofFn d _ _ hj2]; congr 1; omega
    · rw [AT.get_ofFn d _ _ hj2]; congr 1; omega

lemma slotsEq_spec {t : AT} {L : List (ℕ × ℕ)} (h : slotsEq t L = true) :
    ∀ j < 2 ^ 8, t.V j = (AT.ofList L).V j := by
  intro j hj
  unfold slotsEq at h
  have := List.all_eq_true.mp h j (List.mem_range.mpr (by simpa using hj))
  simp only [beq_iff_eq] at this
  unfold AT.V sv
  rw [AT.ofList, AT.get_ofFn 8 _ j hj]
  omega

lemma terms_append (ps₁ ps₂ : List Term) : terms (ps₁ ++ ps₂) = terms ps₁ ++ terms ps₂ := by
  simp [terms, List.flatMap_append]

lemma G_append {R : Type*} [CommRing R] (ps₁ ps₂ : List Term) (F : ℕ → ℕ → R) :
    G (ps₁ ++ ps₂) F = G ps₁ F + G ps₂ F := by
  simp [G, terms_append]

/-- The accumulator from any perfect start. -/
theorem evalFrom_spec (tr trX : T) (hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ 8) (acc : AT)
    (hacc : acc.Perfect 8) (ps : List Term) :
    (evalFrom trX tr acc ps).Perfect 8 ∧ ∀ j < 2 ^ 8, (evalFrom trX tr acc ps).V j =
      acc.V j + G ps (fun μ ν => fiber (rowL (trX.find μ).row) j * sv (tr.find ν).ky) := by
  simp only [evalFrom, lfold_eq]
  obtain ⟨h1, h2⟩ := AT.foldl_spec 8 ps _ _
    (fun acc q _ hp => prodNF_spec tr trX hrows q.c q.neg q.a q.b acc hp) acc hacc
  refine ⟨h1, fun j hj => ?_⟩
  rw [h2 j hj, G_spec]
  congr 1
  refine lsum_congr fun q _ => lsum_congr fun ra _ => lsum_congr fun rb _ => ?_
  rw [sv_yprod, sv_zero, zero_add, lsum_mul_left]
  refine lsum_congr fun t _ => ?_
  rw [lsum_mul_left]
  exact lsum_congr fun u _ => by simp only [Int.cast_id]; ring

/-- **Split certificates.** -/
theorem evalO2_split (trX trY : T) {NX MX : ℕ} (hNX : NX ≤ 2 ^ 8)
    (hlX : ∀ l ∈ trX.leaves, leafOKX NX MX l = true) (ps₁ ps₂ : List Term) (L : List (ℕ × ℕ))
    (h₁ : slotsEq (evalO2 trX trY ps₁) L = true)
    (h₂ : (evalFrom trX trY (AT.ofList L) ps₂).allZero = true) :
    ∀ j < 2 ^ 8, (evalO2 trX trY (ps₁ ++ ps₂)).V j = 0 := by
  have hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ 8 :=
    fun μ t ht => lt_of_lt_of_le ((leafOKX_spec (hlX _ (trX.find_mem μ))).1 t ht) hNX
  intro j hj
  obtain ⟨-, hA⟩ := evalO2_spec trY trX hrows (ps₁ ++ ps₂)
  obtain ⟨-, hB⟩ := evalO2_spec trY trX hrows ps₁
  obtain ⟨hP, hC⟩ := evalFrom_spec trY trX hrows (AT.ofList L) (AT.perfect_ofFn 8 _) ps₂
  have h0 := AT.allZero_spec hP h₂ j hj
  rw [hA j hj, G_append, ← hB j hj, slotsEq_spec h₁ j hj]
  rw [hC j hj] at h0
  exact h0

/-- **Three-part split certificates.** -/
theorem evalO2_split3 (trX trY : T) {NX MX : ℕ} (hNX : NX ≤ 2 ^ 8)
    (hlX : ∀ l ∈ trX.leaves, leafOKX NX MX l = true) (ps₁ ps₂ ps₃ : List Term) (L₁ L₂ : List (ℕ × ℕ))
    (h₁ : slotsEq (evalO2 trX trY ps₁) L₁ = true)
    (h₂ : slotsEq (evalFrom trX trY (AT.ofList L₁) ps₂) L₂ = true)
    (h₃ : (evalFrom trX trY (AT.ofList L₂) ps₃).allZero = true) :
    ∀ j < 2 ^ 8, (evalO2 trX trY (ps₁ ++ ps₂ ++ ps₃)).V j = 0 := by
  have hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ 8 :=
    fun μ t ht => lt_of_lt_of_le ((leafOKX_spec (hlX _ (trX.find_mem μ))).1 t ht) hNX
  intro j hj
  obtain ⟨-, hA⟩ := evalO2_spec trY trX hrows (ps₁ ++ ps₂ ++ ps₃)
  obtain ⟨-, hB⟩ := evalO2_spec trY trX hrows ps₁
  obtain ⟨-, hC⟩ := evalFrom_spec trY trX hrows (AT.ofList L₁) (AT.perfect_ofFn 8 _) ps₂
  obtain ⟨hP, hD⟩ := evalFrom_spec trY trX hrows (AT.ofList L₂) (AT.perfect_ofFn 8 _) ps₃
  have h0 := AT.allZero_spec hP h₃ j hj
  have e2 := slotsEq_spec h₂ j hj
  rw [hC j hj, ← slotsEq_spec h₁ j hj, hB j hj] at e2
  rw [hD j hj, ← e2] at h0
  rw [hA j hj, G_append, G_append]
  linear_combination h0

end LSG.Jac
