/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Laws
import LSG.Jac.Model

/-!
# Law 0 at the origin (Stage A1, ABVAR §A0.2 "`A^{(m)}(X, O) ∝ X`")

`law0_origin`: `A_k^{(0)}(x, O) = −x₀ x_k / 4` **identically** (any commutative ring, any `x`), where `O = e₄` is the
origin of the model. So `A^{(0)}(x, O) = −(x₀/4) · x`: translation by `O` is the identity wherever `x₀ ≠ 0`.

(For general `m`, `A_k^{(m)}(X, e₄) ≡ −X_k X_m / 4` only modulo the quadrics: the data are normalised modulo `I₂`.)
-/

namespace LSG.Jac

open Data

/-! ## Restriction to `Y = e₄` (the origin) -/

/-- The `X`-polynomial `Σ_α X^α · coeff(Y^{β₀})` of an `SP` (rows with `β = β₀`). -/
def ySlice (p : SP) (β₀ : Nat) : List (Nat × Nat × Bool) :=
  p.rows.flatMap fun ra => (ra.2.filter fun t => t.1 == β₀).map fun t => (ra.1, t.2.1, t.2.2)

/-- Every `Y`-code of `p` is either `Y₄²` (code `8192`) or involves a variable other than `Y₄`. -/
def originOK (p : SP) : Bool :=
  p.yc.all fun β => β == 8192 || (List.range 9).any fun i => i != 4 && digit β i != 0

variable {R : Type*} [CommRing R]

lemma xmono_origin_of_ne {β : ℕ} {i : Fin 9} (hi : i ≠ 4) (hd : digit β i ≠ 0) :
    xmono (origin : Fin 9 → R) β = 0 := by
  unfold xmono
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [origin, hi, zero_pow hd]

lemma xmono_origin_8192 : xmono (origin : Fin 9 → R) 8192 = 1 := by
  simp [xmono, origin, digit, Fin.prod_univ_succ, Pi.single_apply]

lemma filter_sum (l : List (ℕ × ℕ × Bool)) (c : R) :
    c * (l.map fun t => if t.1 = 8192 then (sval t.2.1 t.2.2 : R) else 0).sum =
      ((l.filter fun t => t.1 == 8192).map fun t => (sval t.2.1 t.2.2 : R) * c).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    by_cases h8 : t.1 = 8192
    · simp only [List.map_cons, List.sum_cons, h8, if_true, List.filter_cons, beq_self_eq_true,
        mul_add, ih]; ring
    · simp only [List.map_cons, List.sum_cons, h8, if_false, List.filter_cons, mul_add, ih,
        mul_zero, zero_add]
      simp [h8]

/-- Restricting to `y = O` keeps exactly the `Y₄²` coefficients. -/
theorem evalSP_origin (x : Fin 9 → R) (p : SP) (hwf : p.wf = true) (hok : originOK p = true) :
    evalSP x origin p = evalRow x (ySlice p 8192) := by
  unfold evalSP ySlice
  rw [evalRow, map_flatMap_sum]
  refine lsum_congr fun ra hra => ?_
  have key : ∀ t ∈ ra.2, (sval t.2.1 t.2.2 : R) * xmono origin t.1 =
      if t.1 = 8192 then (sval t.2.1 t.2.2 : R) else 0 := by
    intro t ht
    have hy := SP.wf_spec hwf hra ht
    have h2 := List.all_eq_true.mp hok _ hy
    by_cases h8 : t.1 = 8192
    · rw [if_pos h8, h8, xmono_origin_8192, mul_one]
    · rw [if_neg h8]
      have h3 : ∃ i, i < 9 ∧ i ≠ 4 ∧ digit t.1 i ≠ 0 := by simpa [h8] using h2
      obtain ⟨i, hi9, hi4, hd⟩ := h3
      rw [xmono_origin_of_ne (i := ⟨i, hi9⟩) (fun h => hi4 (by simpa using congrArg Fin.val h)) hd,
        mul_zero]
  rw [evalRow, lsum_congr key, filter_sum, List.map_map]
  rfl

lemma law0_slice : ∀ k : Fin 9, ySlice (law k 0) 8192 = [(8 ^ (k : ℕ) + 1, 8, true)] := by
  decide +kernel

lemma law0_originOK : ∀ k : Fin 9, (law k 0).wf = true ∧ originOK (law k 0) = true := by
  decide +kernel

lemma xmono_pair0 (x : Fin 9 → R) (k : Fin 9) : xmono x (8 ^ (k : ℕ) + 1) = x 0 * x k := by
  fin_cases k <;> simp [xmono, digit, Fin.prod_univ_succ] <;> ring

/-- **Law 0 at the origin**: `32 A_k^{(0)}(x, O) = −8 x₀ x_k`. -/
theorem law0_origin (k : Fin 9) (x : Fin 9 → R) : A32 k 0 x origin = -8 * x 0 * x k := by
  simp only [A32, Fin.val_zero]
  rw [evalSP_origin _ _ (law0_originOK k).1 (law0_originOK k).2, law0_slice k]
  simp [evalRow, sval, xmono_pair0]
  ring

/-- `A^{(0)}(x, O) = −(x₀/4) x` (scaled by 32: `lawPt 0 x O = −8 x₀ • x`). -/
theorem lawPt0_origin (x : Fin 9 → R) : lawPt 0 x origin = (-8 * x 0) • x := by
  funext k; simp [lawPt, law0_origin, mul_assoc]

end LSG.Jac
