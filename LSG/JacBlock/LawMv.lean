/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Glue
import LSG.MEB.Block

/-!
# A1's sparse polynomials (`SP`) as `MvPolynomial`s (for the `law` field of the A-block)

* `spMv p : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ`, with **`eval_spMv`**: `eval (Sum.elim x y) (spMv p) = evalSP x y p`;
* **`spMv_isWeightedHomogeneous`**: `degOK p dx dy` gives bidegree `(dx, dy)` for the weights `biW 9`.
-/

noncomputable section

open MvPolynomial LSG.Jac

namespace LSG.JacBlock

variable {σ : Type*}

/-- `X^c` for a code `c`, in the variables `inj i`. -/
def xmonoMv (inj : Fin 9 → σ) (c : ℕ) : MvPolynomial σ ℂ := ∏ i : Fin 9, X (inj i) ^ digit c i

/-- A row `Σ ±n X^c`. -/
def rowMv (inj : Fin 9 → σ) (r : List (ℕ × ℕ × Bool)) : MvPolynomial σ ℂ :=
  (r.map fun t => C ((sval t.2.1 t.2.2 : ℤ) : ℂ) * xmonoMv inj t.1).sum

/-- An `SP` as a polynomial in `X = inl`, `Y = inr`. -/
def spMv (p : SP) : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ :=
  (p.rows.map fun r => xmonoMv Sum.inl r.1 * rowMv Sum.inr r.2).sum

lemma eval_xmonoMv (f : σ → ℂ) (inj : Fin 9 → σ) (c : ℕ) : eval f (xmonoMv inj c) = xmono (f ∘ inj) c := by
  simp [xmonoMv, xmono]

lemma eval_rowMv (f : σ → ℂ) (inj : Fin 9 → σ) (r : List (ℕ × ℕ × Bool)) :
    eval f (rowMv inj r) = evalRow (f ∘ inj) r := by
  simp [rowMv, evalRow, map_list_sum, List.map_map, Function.comp_def, eval_xmonoMv]

theorem eval_spMv (x y : Fin 9 → ℂ) (p : SP) : eval (Sum.elim x y) (spMv p) = evalSP x y p := by
  simp only [spMv, evalSP, map_list_sum, List.map_map, Function.comp_def, map_mul, eval_xmonoMv, eval_rowMv]
  rfl

lemma xmonoMv_hom (c : ℕ) (w : Fin 9 ⊕ Fin 9 → ℕ × ℕ) (inj : Fin 9 → Fin 9 ⊕ Fin 9) (u : ℕ × ℕ)
    (hw : ∀ i, w (inj i) = u) : (xmonoMv inj c).IsWeightedHomogeneous w (degc c • u) := by
  rw [degc_eq, Finset.sum_smul]
  unfold xmonoMv
  refine IsWeightedHomogeneous.prod _ _ _ fun i _ => ?_
  have := (isWeightedHomogeneous_X ℂ w (inj i)).pow (digit c i)
  rwa [hw] at this

lemma mem_whs_list {w : Fin 9 ⊕ Fin 9 → ℕ × ℕ} {m : ℕ × ℕ} {l : List (MvPolynomial (Fin 9 ⊕ Fin 9) ℂ)}
    (h : ∀ q ∈ l, q.IsWeightedHomogeneous w m) : l.sum.IsWeightedHomogeneous w m := by
  have : l.sum ∈ weightedHomogeneousSubmodule ℂ w m :=
    list_sum_mem fun q hq => (mem_weightedHomogeneousSubmodule ℂ w m q).mpr (h q hq)
  exact (mem_weightedHomogeneousSubmodule ℂ w m _).mp this

theorem spMv_isWeightedHomogeneous (p : SP) {dx dy : ℕ} (h : degOK p dx dy = true) :
    (spMv p).IsWeightedHomogeneous (LSG.MEB.biW 9) (dx, dy) := by
  unfold spMv
  refine mem_whs_list fun q hq => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  have hr' := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hr'
  have hx := xmonoMv_hom r.1 (LSG.MEB.biW 9) Sum.inl (1, 0) (fun i => rfl)
  rw [hr'.1] at hx
  have hy : (rowMv Sum.inr r.2).IsWeightedHomogeneous (LSG.MEB.biW 9) (dy • ((0, 1) : ℕ × ℕ)) := by
    unfold rowMv
    refine mem_whs_list fun q' hq' => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq'
    have := (List.all_eq_true.mp hr'.2 t ht)
    simp only [beq_iff_eq] at this
    have h2 := xmonoMv_hom t.1 (LSG.MEB.biW 9) Sum.inr (0, 1) (fun i => rfl)
    rw [this] at h2
    have h3 := (isWeightedHomogeneous_C (LSG.MEB.biW 9) (((sval t.2.1 t.2.2 : ℤ)) : ℂ)).mul h2
    rwa [zero_add] at h3
  have := hx.mul hy
  convert this using 1
  ext <;> simp

end LSG.JacBlock
