/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Kronecker packing: signed-digit uniqueness and grouping (Stage A1c)

The certificate checker of Stage A1c (ABVAR §A0.3) evaluates a formal integer combination `Σ wᵢ [kᵢ]` of
"slots" `kᵢ < n` at `2^b`, i.e. computes `Σ wᵢ 2^{b kᵢ}`, and checks that it is `0`. If `Σ |wᵢ| < 2^b` this forces
every slot total `Σ_{kᵢ = k} wᵢ` to vanish (`digits_eq_zero`), hence `Σ wᵢ h(kᵢ) = 0` for *every* `h` with values in
any commutative ring (`kron_zero`).

* `sum_fiber`: a list sum `Σ wᵢ • g(kᵢ)` regroups as `Σ_{k < n} (Σ_{kᵢ = k} wᵢ) • g(k)`.
* `digits_eq_zero`: `Σ_{k<n} d_k 2^{bk} = 0` and `|d_k| < 2^b` imply `d = 0` on `[0, n)`.
* `kron_zero`: the packed form of the statement above.
* `sum_range_mul'`: reindexing `Σ_{s<m} Σ_{t<n} f(n s + t) = Σ_{k<mn} f k` (two-level packing).
-/

namespace LSG.Jac

open Finset

/-- The slot total `Σ_{p ∈ L, p.2 = k} p.1`. -/
def fiber (L : List (ℤ × ℕ)) (k : ℕ) : ℤ := (L.map fun p => if p.2 = k then p.1 else 0).sum

lemma fiber_cons (p : ℤ × ℕ) (L : List (ℤ × ℕ)) (k : ℕ) :
    fiber (p :: L) k = (if p.2 = k then p.1 else 0) + fiber L k := by
  simp [fiber]

lemma abs_fiber_le (L : List (ℤ × ℕ)) (k : ℕ) : |fiber L k| ≤ (L.map fun p => |p.1|).sum := by
  induction L with
  | nil => simp [fiber]
  | cons p L ih =>
    rw [fiber_cons, List.map_cons, List.sum_cons]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    split_ifs <;> simp

/-- Regrouping a list sum by slots. -/
lemma sum_fiber {M : Type*} [AddCommGroup M] (L : List (ℤ × ℕ)) (n : ℕ) (hL : ∀ p ∈ L, p.2 < n)
    (g : ℕ → M) : (L.map fun p => p.1 • g p.2).sum = ∑ k ∈ range n, fiber L k • g k := by
  induction L with
  | nil => simp [fiber]
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, ih fun q hq => hL q (List.mem_cons_of_mem _ hq)]
    simp only [fiber_cons, add_smul, sum_add_distrib, ite_smul, zero_smul]
    rw [sum_ite_eq (range n) p.2 (fun k => p.1 • g k)]
    simp [hL p List.mem_cons_self]

/-- **Signed-digit uniqueness**: if `Σ_{k<n} d_k 2^{bk} = 0` with every `|d_k| < 2^b`, all `d_k` vanish. -/
theorem digits_eq_zero (b : ℕ) :
    ∀ (n : ℕ) (d : ℕ → ℤ), (∀ k < n, |d k| < 2 ^ b) →
      ∑ k ∈ range n, d k * 2 ^ (b * k) = 0 → ∀ k < n, d k = 0 := by
  intro n
  induction n with
  | zero => intro d _ _ k hk; omega
  | succ n ih =>
    intro d hd hs
    rw [sum_range_succ'] at hs
    simp only [mul_zero, pow_zero, mul_one] at hs
    have hsplit : ∑ k ∈ range n, d (k + 1) * 2 ^ (b * (k + 1)) =
        2 ^ b * ∑ k ∈ range n, d (k + 1) * 2 ^ (b * k) := by
      rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; rw [mul_add, mul_one, pow_add]; ring
    rw [hsplit] at hs
    have h0 : d 0 = 0 := by
      have hdvd : (2 : ℤ) ^ b ∣ d 0 := ⟨-∑ k ∈ range n, d (k + 1) * 2 ^ (b * k), by linarith⟩
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_
      have := hd 0 (Nat.succ_pos n)
      rw [abs_lt] at this
      have h2 : ((2 : ℤ) ^ b).natAbs = 2 ^ b := by simp [Int.natAbs_pow]
      rw [h2]; zify; rw [abs_lt]; exact this
    have hrest : ∑ k ∈ range n, d (k + 1) * 2 ^ (b * k) = 0 := by
      rw [h0, add_zero] at hs
      exact (mul_eq_zero.mp hs).resolve_left (pow_ne_zero _ two_ne_zero)
    have ih' := ih (fun k => d (k + 1)) (fun k hk => hd (k + 1) (by omega)) hrest
    intro k hk
    rcases k with _ | k
    · exact h0
    · exact ih' k (by omega)

/-- **Kronecker grouping.** If `Σ_{p ∈ L} p.1 2^{b p.2} = 0`, all slots are `< n`, and `Σ |p.1| < 2^b`, then
`Σ_{p ∈ L} p.1 h(p.2) = 0` for every `h : ℕ → R`. -/
theorem kron_zero {R : Type*} [CommRing R] (L : List (ℤ × ℕ)) (n b : ℕ) (hidx : ∀ p ∈ L, p.2 < n)
    (hbound : (L.map fun p => |p.1|).sum < 2 ^ b)
    (hz : (L.map fun p => p.1 * 2 ^ (b * p.2)).sum = 0) (h : ℕ → R) :
    (L.map fun p => (p.1 : R) * h p.2).sum = 0 := by
  have hz' := hz
  have e1 : (L.map fun p => p.1 * (2 : ℤ) ^ (b * p.2)) = L.map fun p => p.1 • ((2 : ℤ) ^ (b * p.2)) := by
    simp
  rw [e1, sum_fiber L n hidx (fun k => (2 : ℤ) ^ (b * k))] at hz'
  have hd : ∀ k < n, fiber L k = 0 := by
    refine digits_eq_zero b n (fiber L) (fun k _ => (abs_fiber_le L k).trans_lt hbound) ?_
    simpa [smul_eq_mul] using hz'
  have e2 : (L.map fun p => (p.1 : R) * h p.2) = L.map fun p => p.1 • h p.2 := by
    simp [zsmul_eq_mul]
  rw [e2, sum_fiber L n hidx h]
  exact sum_eq_zero fun k hk => by rw [hd k (mem_range.mp hk), zero_smul]

/-- Two-level reindexing `Σ_{s<m} Σ_{t<n} f(n s + t) = Σ_{k < m n} f k`. -/
lemma sum_range_mul' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∀ m : ℕ, ∑ s ∈ range m, ∑ t ∈ range n, f (n * s + t) = ∑ k ∈ range (m * n), f k := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih, Nat.succ_mul, sum_range_add, Nat.mul_comm n m]

end LSG.Jac
