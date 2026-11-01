/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Laws
import LSG.Jac.Model
import LSG.Jac.CheckerSym

/-!
# The symmetries (S1), (S2) of the nine laws (ABVAR §A0.2)

* **`law_S1`**: `A_k^{(m)}(x, [−1]y) = A_m^{(k)}(x, y)` identically (any commutative ring; `[−1] = negP`).
* **`law_S2`**: `A_k^{(m)}(y, x) = ε_m A_k^{(m)}(x, y)` identically, `ε_m = +1` for `m ∈ {4, 5, 6, 7}` and `−1`
  otherwise (`lawEps`).

Both are exact identities of the data, checked by `decide +kernel` (`s1OK`, `s2OK`).
-/

namespace LSG.Jac

open Data Finset

variable {R : Type*} [CommRing R]

lemma evalSP_flat (x y : Fin 9 → R) (p : SP) :
    evalSP x y p = ((flat p).map fun e => (sval e.2.2.1 e.2.2.2 : R) * xmono x e.1 * xmono y e.2.1).sum := by
  unfold evalSP flat evalRow
  rw [map_flatMap_sum]
  refine lsum_congr fun ra _ => ?_
  rw [lsum_mul_left, List.map_map]
  exact lsum_congr fun t _ => by simp only [Function.comp_apply]; ring

lemma sval_xor (n : ℕ) (a b : Bool) : sval n (xor a b) = (if b then -1 else 1) * sval n a := by
  cases a <;> cases b <;> simp [sval]

lemma xmono_negP (y : Fin 9 → R) (β : ℕ) :
    xmono (negP y) β = (if oddY β then -1 else 1) * xmono y β := by
  have h : xmono (negP y) β = (-1) ^ (digit β 4 + digit β 5 + digit β 6 + digit β 7) * xmono y β := by
    simp only [xmono, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, negP, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    rw [neg_pow (y 4), neg_pow (y 5), neg_pow (y 6), neg_pow (y 7), pow_add, pow_add, pow_add]
    have e4 : ((4 : Fin 9) : ℕ) = 4 := rfl
    have e5 : ((5 : Fin 9) : ℕ) = 5 := rfl
    have e6 : ((6 : Fin 9) : ℕ) = 6 := rfl
    have e7 : ((7 : Fin 9) : ℕ) = 7 := rfl
    simp only [Fin.isValue, Fin.reduceSucc, e4, e5, e6, e7]
    ring
  rw [h]
  congr 1
  unfold oddY
  rcases Nat.even_or_odd (digit β 4 + digit β 5 + digit β 6 + digit β 7) with he | ho
  · rw [he.neg_one_pow]; simp [Nat.even_iff.mp he]
  · rw [ho.neg_one_pow]; simp [Nat.odd_iff.mp ho]

lemma eval_s1 (x y : Fin 9 → R) (p q : SP) (h : s1OK p q = true) :
    evalSP x (negP y) p = evalSP x y q := by
  unfold s1OK at h
  rw [decide_eq_true_eq] at h
  rw [evalSP_flat, evalSP_flat, h, List.map_map]
  refine lsum_congr fun e _ => ?_
  simp only [Function.comp_apply, xmono_negP, sval_xor]
  split_ifs <;> push_cast <;> ring

lemma insLex_perm (e : ℕ × ℕ × ℕ × Bool) (l : List (ℕ × ℕ × ℕ × Bool)) : (insLex e l).Perm (e :: l) := by
  induction l with
  | nil => simp [insLex]
  | cons f l ih =>
    unfold insLex
    split_ifs
    · exact List.Perm.refl _
    · exact (ih.cons f).trans (List.Perm.swap e f l)

lemma sortLex_perm (l : List (ℕ × ℕ × ℕ × Bool)) : (sortLex l).Perm l := by
  induction l with
  | nil => simp [sortLex]
  | cons e l ih => exact (insLex_perm e _).trans (ih.cons e)

lemma eval_s2 (x y : Fin 9 → R) (p : SP) (neg : Bool) (h : s2OK p neg = true) :
    evalSP x y p = (if neg then -1 else 1) * evalSP y x p := by
  unfold s2OK at h
  rw [decide_eq_true_eq] at h
  have h2 := congrArg (fun l => (l.map fun e => (sval e.2.2.1 e.2.2.2 : R) * xmono x e.1 * xmono y e.2.1).sum) h
  rw [((sortLex_perm _).map _).sum_eq, List.map_map] at h2
  rw [evalSP_flat, h2, evalSP_flat, lsum_mul_left]
  refine lsum_congr fun e _ => ?_
  simp only [Function.comp_apply, sval_xor]
  split_ifs <;> push_cast <;> ring

/-- `ε_m`: `+1` for `m ∈ {4, 5, 6, 7}`, `−1` otherwise. -/
def lawEps (m : Fin 9) : Bool := !(decide (4 ≤ (m : ℕ) ∧ (m : ℕ) ≤ 7))

lemma law_s1OK : ∀ k m : Fin 9, s1OK (law k m) (law m k) = true := by decide +kernel

lemma law_s2OK : ∀ k m : Fin 9, s2OK (law k m) (lawEps m) = true := by decide +kernel

/-- **(S1)**: `A_k^{(m)}(x, [−1]y) = A_m^{(k)}(x, y)`. -/
theorem law_S1 (k m : Fin 9) (x y : Fin 9 → R) : A32 k m x (negP y) = A32 m k x y :=
  eval_s1 x y _ _ (law_s1OK k m)

/-- **(S2)**: `A_k^{(m)}(x, y) = ε_m A_k^{(m)}(y, x)`. -/
theorem law_S2 (k m : Fin 9) (x y : Fin 9 → R) :
    A32 k m x y = (if lawEps m then -1 else 1) * A32 k m y x :=
  eval_s2 x y _ _ (law_s2OK k m)

end LSG.Jac
