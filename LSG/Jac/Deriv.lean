/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Laws
import LSG.Jac.CheckerDeriv

/-!
# Formal partial derivatives of sparse polynomials: semantics (Stage A1, flow identities)

* `xmono_lower`: `X^c = X_i · X^{c − 8^i}` when digit `i` of `c` is `≥ 1` (under the decidable `decOK1`).
* `hasDerivAt_xmono`, **`hasDerivAt_evalSP`**: along differentiable curves `x(t), y(t)` in `𝕜⁹`,
  `d/dt evalSP (x t) (y t) p = Σ_i x_i' · evalSP x y (dXsp i p) + Σ_i y_i' · evalSP x y (dYsp i p)`,
  for every `SP` with `decOK p` (checked by `decide` for the law data: `law_decOK`).

So the formal derivatives `dXsp`, `dYsp` used in the flow certificates (`LSG.Jac.Flow`) are the partial derivatives.
-/

namespace LSG.Jac

open Finset

lemma decOK1_spec {i c : ℕ} (h : decOK1 i c = true) (hd : digit c i ≠ 0) {k : ℕ} (hk : k < 9) :
    digit (lowerCode i c) k = if k = i then digit c i - 1 else digit c k := by
  unfold decOK1 at h
  simp only [Bool.or_eq_true, beq_iff_eq, hd, false_or, List.all_eq_true, List.mem_range] at h
  have := h k hk
  by_cases hki : k = i <;> simp_all

/-- `X^c = X_i · X^{c − 8^i}` when digit `i` of `c` is nonzero. -/
lemma xmono_lower {R : Type*} [CommMonoid R] (x : Fin 9 → R) (i : Fin 9) {c : ℕ}
    (h : decOK1 i c = true) (hd : digit c i ≠ 0) :
    xmono x c = x i * xmono x (lowerCode i c) := by
  unfold xmono
  rw [← mul_prod_erase univ (fun k => x k ^ digit c k) (mem_univ i),
    ← mul_prod_erase univ (fun k => x k ^ digit (lowerCode i c) k) (mem_univ i),
    decOK1_spec h hd i.2, if_pos rfl]
  have hrest : ∏ k ∈ univ.erase i, x k ^ digit (lowerCode i c) k = ∏ k ∈ univ.erase i, x k ^ digit c k := by
    refine prod_congr rfl fun k hk => ?_
    rw [decOK1_spec h hd k.2, if_neg (fun h' => (mem_erase.mp hk).1 (Fin.ext h'))]
  rw [hrest, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)]

section Calculus

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Derivative of a monomial along a curve. -/
theorem hasDerivAt_xmono {x : 𝕜 → Fin 9 → 𝕜} {x' : Fin 9 → 𝕜} {t₀ : 𝕜}
    (hx : ∀ k, HasDerivAt (fun t => x t k) (x' k) t₀) (c : ℕ) (hc : ∀ i : Fin 9, decOK1 i c = true) :
    HasDerivAt (fun t => xmono (x t) c)
      (∑ i : Fin 9, x' i * ((digit c i : 𝕜) * xmono (x t₀) (lowerCode i c))) t₀ := by
  unfold xmono
  have h := HasDerivAt.fun_finsetProd (u := univ) (f := fun k t => x t k ^ digit c k)
    (f' := fun k => ((digit c k : ℕ) : 𝕜) * x t₀ k ^ (digit c k - 1) * x' k)
    (fun k _ => (hx k).pow (digit c k))
  refine h.congr_deriv (sum_congr rfl fun i _ => ?_)
  by_cases hd : digit c i = 0
  · simp [hd]
  · have := xmono_lower (x t₀) i (hc i) hd
    unfold xmono at this
    rw [← mul_prod_erase univ (fun k => x t₀ k ^ digit c k) (mem_univ i)] at this
    rw [← mul_prod_erase univ (fun k => x t₀ k ^ digit (lowerCode i c) k) (mem_univ i),
      decOK1_spec (hc i) hd i.2, if_pos rfl]
    have hrest : ∏ k ∈ univ.erase i, x t₀ k ^ digit (lowerCode i c) k =
        ∏ k ∈ univ.erase i, x t₀ k ^ digit c k := by
      refine prod_congr rfl fun k hk => ?_
      rw [decOK1_spec (hc i) hd k.2, if_neg (fun h' => (mem_erase.mp hk).1 (Fin.ext h'))]
    rw [hrest, smul_eq_mul]
    ring

lemma hasDerivAt_lsum {α : Type*} (l : List α) {F : α → 𝕜 → 𝕜} {F' : α → 𝕜} {t₀ : 𝕜}
    (h : ∀ a ∈ l, HasDerivAt (F a) (F' a) t₀) :
    HasDerivAt (fun t => (l.map fun a => F a t).sum) (l.map F').sum t₀ := by
  induction l with
  | nil => simpa using hasDerivAt_const t₀ (0 : 𝕜)
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

lemma evalRow_dY (y : Fin 9 → 𝕜) (i : ℕ) (r : List (ℕ × ℕ × Bool)) :
    evalRow y ((r.filter fun t => digit t.1 i != 0).map fun t => (lowerCode i t.1, digit t.1 i * t.2.1, t.2.2)) =
      (r.map fun t => (sval t.2.1 t.2.2 : 𝕜) * ((digit t.1 i : 𝕜) * xmono y (lowerCode i t.1))).sum := by
  unfold evalRow
  induction r with
  | nil => rfl
  | cons t r ih =>
    by_cases hd : digit t.1 i = 0
    · rw [List.filter_cons_of_neg (by simp [hd]), ih, List.map_cons, List.sum_cons]
      simp [hd]
    · rw [List.filter_cons_of_pos (by simpa using hd), List.map_cons, List.map_cons, List.sum_cons, ih,
        List.map_cons, List.sum_cons]
      congr 1
      cases t.2.2 <;> simp [sval] <;> ring

/-- The `X_i`-derivative of an `SP`, evaluated. -/
lemma evalSP_dX (x y : Fin 9 → 𝕜) (i : ℕ) (p : SP) :
    evalSP x y (dXsp i p) =
      (p.rows.map fun r => (digit r.1 i : 𝕜) * xmono x (lowerCode i r.1) * evalRow y r.2).sum := by
  unfold evalSP dXsp
  simp only [List.map_map, Function.comp_def]
  induction p.rows with
  | nil => simp
  | cons r rs ih =>
    by_cases hd : digit r.1 i = 0
    · simp [List.filter_cons, hd, ih]
    · simp only [List.filter_cons, hd, bne_iff_ne, ne_eq, not_false_eq_true, decide_true, if_true,
        List.map_cons, List.sum_cons, ih]
      congr 1
      unfold evalRow
      rw [List.map_map, lsum_mul_left, lsum_mul_left]
      refine lsum_congr fun t _ => ?_
      simp only [Function.comp_apply]
      cases t.2.2 <;> simp [sval] <;> ring

/-- The `Y_i`-derivative of an `SP`, evaluated. -/
lemma evalSP_dY (x y : Fin 9 → 𝕜) (i : ℕ) (p : SP) :
    evalSP x y (dYsp i p) = (p.rows.map fun r => xmono x r.1 *
      (r.2.map fun t => (sval t.2.1 t.2.2 : 𝕜) * ((digit t.1 i : 𝕜) * xmono y (lowerCode i t.1))).sum).sum := by
  unfold evalSP dYsp
  simp only [List.map_map, Function.comp_def, evalRow_dY]

/-- **Derivative of an `SP` along a curve** (chain rule with the formal partial derivatives). -/
theorem hasDerivAt_evalSP {x y : 𝕜 → Fin 9 → 𝕜} {x' y' : Fin 9 → 𝕜} {t₀ : 𝕜}
    (hx : ∀ k, HasDerivAt (fun t => x t k) (x' k) t₀) (hy : ∀ k, HasDerivAt (fun t => y t k) (y' k) t₀)
    (p : SP) (hp : decOK p = true) :
    HasDerivAt (fun t => evalSP (x t) (y t) p)
      (∑ i : Fin 9, x' i * evalSP (x t₀) (y t₀) (dXsp i p) +
        ∑ i : Fin 9, y' i * evalSP (x t₀) (y t₀) (dYsp i p)) t₀ := by
  have hc : ∀ r ∈ p.rows, (∀ i : Fin 9, decOK1 i r.1 = true) ∧
      ∀ t ∈ r.2, ∀ i : Fin 9, decOK1 i t.1 = true := by
    intro r hr
    unfold decOK at hp
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hp
    exact ⟨fun i => (hp i i.2 r hr).1, fun t ht i => (hp i i.2 r hr).2 t ht⟩
  rw [show (fun t => evalSP (x t) (y t) p) =
    fun t => (p.rows.map fun r => xmono (x t) r.1 * evalRow (y t) r.2).sum from rfl]
  have hrow : ∀ r ∈ p.rows, HasDerivAt (fun t => evalRow (y t) r.2)
      ((r.2.map fun t => (sval t.2.1 t.2.2 : 𝕜) *
        ∑ i : Fin 9, y' i * ((digit t.1 i : 𝕜) * xmono (y t₀) (lowerCode i t.1))).sum) t₀ := by
    intro r hr
    unfold evalRow
    exact hasDerivAt_lsum r.2 fun t ht => (hasDerivAt_xmono hy t.1 ((hc r hr).2 t ht)).const_mul _
  refine (hasDerivAt_lsum p.rows fun r hr =>
    (hasDerivAt_xmono hx r.1 (hc r hr).1).mul (hrow r hr)).congr_deriv ?_
  simp only [evalSP_dX, evalSP_dY]
  rw [show (∑ i : Fin 9, x' i * (p.rows.map fun r => (digit r.1 i : 𝕜) * xmono (x t₀) (lowerCode i r.1) *
        evalRow (y t₀) r.2).sum) = (p.rows.map fun r => ∑ i : Fin 9, x' i * ((digit r.1 i : 𝕜) *
        xmono (x t₀) (lowerCode i r.1) * evalRow (y t₀) r.2)).sum by
      rw [lsum_finset_comm]; exact sum_congr rfl fun i _ => lsum_mul_left _ _ _,
    show (∑ i : Fin 9, y' i * (p.rows.map fun r => xmono (x t₀) r.1 * (r.2.map fun t =>
        (sval t.2.1 t.2.2 : 𝕜) * ((digit t.1 i : 𝕜) * xmono (y t₀) (lowerCode i t.1))).sum).sum) =
        (p.rows.map fun r => ∑ i : Fin 9, y' i * (xmono (x t₀) r.1 * (r.2.map fun t =>
        (sval t.2.1 t.2.2 : 𝕜) * ((digit t.1 i : 𝕜) * xmono (y t₀) (lowerCode i t.1))).sum)).sum by
      rw [lsum_finset_comm]; exact sum_congr rfl fun i _ => lsum_mul_left _ _ _,
    ← List.sum_map_add]
  refine lsum_congr fun r _ => ?_
  rw [sum_mul]
  congr 1
  · exact sum_congr rfl fun i _ => by unfold evalRow; ring
  · have e : ∀ t : ℕ × ℕ × Bool, (sval t.2.1 t.2.2 : 𝕜) *
        ∑ i : Fin 9, y' i * ((digit t.1 i : 𝕜) * xmono (y t₀) (lowerCode i t.1)) =
        ∑ i : Fin 9, y' i * ((sval t.2.1 t.2.2 : 𝕜) * ((digit t.1 i : 𝕜) * xmono (y t₀) (lowerCode i t.1))) := by
      intro t; rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    simp only [e]
    rw [lsum_finset_comm, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← lsum_mul_left]
    ring

end Calculus

/-- The digit check holds for all law data (so `hasDerivAt_evalSP` applies to every `A32 k m`). -/
theorem law_decOK : ∀ k m : Fin 9, decOK (Data.law k m) = true := by decide +kernel


end LSG.Jac
