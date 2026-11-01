/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Sym
import LSG.Jac.Origin
import LSG.Jac.CheckerDiag

/-!
# Single-copy identities; law 0 on `(X, −X)`; `dup` at the origin (STAGE_A1 §8.4, field (P))

* `single_of_check`: a checked single-copy form vanishes on `V(Q)` (`X`-table `nfTree`, `Y`-table `T0`).
* `evalSP_diagSP`: `diagSP p` evaluates to `p(x, x)`.
* `dup_origin`: `dup e₄ = −8 • e₄`.
-/

namespace LSG.Jac

open Data

variable {R : Type*} [CommRing R]

lemma T0_leaves : T0.leaves = [⟨0, 0, [(0, 1, false)], (1, 0)⟩] := rfl

lemma nfValid_T0 (y : Fin 9 → R) : NFValid T0 [0] 1 y := by
  intro l hl
  rw [T0_leaves, List.mem_singleton] at hl
  subst hl
  simp [evalNF, sval]

lemma leafOK_T0 (b : ℕ) (hb : 0 < b) : ∀ l ∈ T0.leaves, leafOK 1 b 1 l = true := by
  intro l hl
  rw [T0_leaves, List.mem_singleton] at hl
  subst hl
  simp [leafOK, packS, addS, rowN]

lemma evalSP_oneSP (x y : Fin 9 → R) : evalSP x y oneSP = 1 := by
  simp [evalSP, oneSP, evalRow, sval, xmono, digit]

lemma evalSP_diagSP (x y : Fin 9 → R) (p : SP) (h : diagOK p = true) :
    evalSP x y (diagSP p) = evalSP x x p := by
  unfold diagOK at h
  unfold evalSP diagSP
  rw [map_flatMap_sum]
  refine lsum_congr fun ra hra => ?_
  unfold evalRow
  rw [lsum_mul_left, List.map_map]
  refine lsum_congr fun t ht => ?_
  have hn := List.all_eq_true.mp (List.all_eq_true.mp h ra hra) t ht
  simp only [Function.comp_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    xmono_add x hn]
  have : xmono y 0 = (1 : R) := by simp [xmono, digit]
  rw [this]; ring

/-- **A checked single-copy form vanishes on the model.** -/
theorem single_of_check [Algebra ℚ R] (p : SP)
    (hO : (evalO2 nfTree T0 [⟨1, false, p, oneSP⟩]).allZero = true)
    (hB : wsum [⟨1, false, p, oneSP⟩] * (rowM * 1) < 2 ^ kb)
    (hT : termOK2 nfTree T0 ⟨1, false, p, oneSP⟩ = true) (hw : p.wf = true)
    (x y : Fin 9 → R) (hx : OnQ x) : evalSP x y p = 0 := by
  have hX : ∀ l ∈ nfTree.leaves, leafOKX 144 rowM l = true := fun l hl => leafOKX_of_leafOK (leaves_ok l hl)
  have h := sound2 nfTree T0 stdc [0] 144 1 kb rowM 1 nfDelta 1 (by norm_num) hX (leafOK_T0 kb (by decide))
    _ hO hB (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact ⟨hT, hw, by show oneSP.wf = true; decide⟩) x y (nfValid x hx) (nfValid_T0 y)
  simp only [evalTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sval,
    Bool.false_eq_true, if_false, Nat.cast_one, Int.cast_one, one_mul, evalSP_oneSP, mul_one] at h
  exact ((natCast_isUnit (R := R) (by decide : nfDelta ≠ 0)).mul_right_eq_zero).mp h

/-- Every code of a row is `X₄²` or involves a variable other than `X₄`. -/
def rowOriginOK (r : List (ℕ × ℕ × Bool)) : Bool :=
  r.all fun t => t.1 == 8192 || (List.range 9).any fun i => i != 4 && digit t.1 i != 0

lemma evalRow_origin (r : List (ℕ × ℕ × Bool)) (h : rowOriginOK r = true) :
    evalRow (origin : Fin 9 → R) r = ((r.filter fun t => t.1 == 8192).map fun t => (sval t.2.1 t.2.2 : R)).sum := by
  unfold rowOriginOK at h
  unfold evalRow
  induction r with
  | nil => rfl
  | cons t r ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    by_cases h8 : t.1 = 8192
    · rw [List.filter_cons_of_pos (by simp [h8]), List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
        ih h.2, h8, xmono_origin_8192, mul_one]
    · have h3 : ∃ i, i < 9 ∧ i ≠ 4 ∧ digit t.1 i ≠ 0 := by simpa [h8] using h.1
      obtain ⟨i, hi9, hi4, hd⟩ := h3
      rw [List.filter_cons_of_neg (by simp [h8]), List.map_cons, List.sum_cons, ih h.2,
        xmono_origin_of_ne (i := ⟨i, hi9⟩) (fun h' => hi4 (by simpa using congrArg Fin.val h')) hd, mul_zero,
        zero_add]

lemma dup_origin_data : ∀ k : Fin 9, (law k 4).wf = true ∧ originOK (law k 4) = true ∧
    rowOriginOK (ySlice (law k 4) 8192) = true ∧
    ((ySlice (law k 4) 8192).filter fun t => t.1 == 8192) = (if (k : ℕ) = 4 then [(8192, 8, true)] else []) := by
  decide +kernel

/-- **`dup` at the origin**: `dup e₄ = −8 • e₄` (scaled data; `c = −8 ≠ 0`). -/
theorem dup_origin : dup (origin : Fin 9 → R) = (-8 : R) • origin := by
  funext k
  obtain ⟨h1, h2, h3, h4⟩ := dup_origin_data k
  simp only [dup, lawPt, A32]
  rw [show ((4 : Fin 9) : ℕ) = 4 from rfl, evalSP_origin _ _ h1 h2, evalRow_origin _ h3, h4]
  fin_cases k <;> simp [sval, origin, Pi.single_apply]

end LSG.Jac
