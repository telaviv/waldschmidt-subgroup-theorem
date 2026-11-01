/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.TableFacts
import LSG.Jac.Data.Laws
import LSG.Jac.SplitSound

/-!
# The nine (2,2) addition laws on the P⁸ model (Stage A1, ABVAR §A0.2)

`A32 k m x y = 32 · A_k^{(m)}(x, y)`: coordinate `k` of law `m` (Lange–Ruppert form
`A_k^{(m)}(P, Q) = X_k(P + Q) X_m(P − Q) B(P, Q)³` in affine normalisation; data `Data.law`, interpolated in the A0b
spike and *not* trusted: every property used is re-checked in Lean). All laws are bihomogeneous of bidegree `(2, 2)`,
so the factor 32 is irrelevant projectively.

* `identity_of_check`: the bridge from a kernel check to an identity on `V(Q) × V(Q)` over any `ℚ`-algebra.
* `natCast_isUnit`: integers are units in a `ℚ`-algebra.
-/

namespace LSG.Jac

open Data

variable {R : Type*} [CommRing R]

/-- `32 · A_k^{(m)}(x, y)`. -/
noncomputable def A32 (k m : Fin 9) (x y : Fin 9 → R) : R := evalSP x y (law k m)

/-- The output point of law `m` (scaled by 32). -/
noncomputable def lawPt (m : Fin 9) (x y : Fin 9 → R) : Fin 9 → R := fun k => A32 k m x y

/-- The duplication map `Dup(x) = A^{(4)}(x, x)` (ABVAR A0.2: law 4 is the one whose section `X₄` is nonzero at the
origin `e₄`; degree 4, scaled by 32). -/
noncomputable def dup (x : Fin 9 → R) : Fin 9 → R := lawPt 4 x x

lemma natCast_isUnit [Algebra ℚ R] {n : ℕ} (hn : n ≠ 0) : IsUnit (n : R) := by
  have h : (n : R) = algebraMap ℚ R n := by simp
  rw [h]
  exact (IsUnit.mk0 (n : ℚ) (by exact_mod_cast hn)).map _

/-- **From a kernel check to an identity on the model.** -/
theorem identity_of_check (ps : List Term) (hO : (evalO nfTree ps).allZero = true)
    (hB : wsum ps * rowM ^ 2 < 2 ^ kb)
    (hT : ps.all (fun q => termOK nfTree q && q.a.wf && q.b.wf) = true)
    [Algebra ℚ R] (x y : Fin 9 → R) (hx : OnQ x) (hy : OnQ y) : evalTerms x y ps = 0 := by
  have h := sound_bidegree nfTree stdc 144 kb rowM nfDelta (by norm_num) leaves_ok ps hO hB
    (fun q hq => by
      have := List.all_eq_true.mp hT q hq
      simpa [Bool.and_eq_true, and_assoc] using this)
    x y (nfValid x hx) (nfValid y hy)
  have hu : IsUnit ((nfDelta : R) ^ 2) := (natCast_isUnit (R := R) (by decide)).pow 2
  exact hu.mul_right_eq_zero.mp h

/-- **From a split kernel check to an identity on the model** (two declarations, see `LSG.Jac.CheckerSplit`). -/
theorem identity_of_check_split (ps₁ ps₂ : List Term) (L : List (ℕ × ℕ))
    (h₁ : slotsEq (evalO nfTree ps₁) L = true)
    (h₂ : (evalFrom nfTree nfTree (AT.ofList L) ps₂).allZero = true)
    (hB : wsum (ps₁ ++ ps₂) * rowM ^ 2 < 2 ^ kb)
    (hT : (ps₁ ++ ps₂).all (fun q => termOK nfTree q && q.a.wf && q.b.wf) = true)
    [Algebra ℚ R] (x y : Fin 9 → R) (hx : OnQ x) (hy : OnQ y) : evalTerms x y (ps₁ ++ ps₂) = 0 := by
  have hX : ∀ l ∈ nfTree.leaves, leafOKX 144 rowM l = true := fun l hl => leafOKX_of_leafOK (leaves_ok l hl)
  have h := sound2V nfTree nfTree stdc stdc 144 144 kb rowM rowM nfDelta nfDelta (by norm_num) hX leaves_ok
    (ps₁ ++ ps₂) (evalO2_split nfTree nfTree (by norm_num) hX ps₁ ps₂ L h₁ h₂) (by rw [← sq]; exact hB)
    (fun q hq => by
      have := List.all_eq_true.mp hT q hq
      simpa [termOK, Bool.and_eq_true, and_assoc] using this)
    x y (nfValid x hx) (nfValid y hy)
  have hu : IsUnit ((nfDelta : R) * nfDelta) :=
    (natCast_isUnit (R := R) (by decide)).mul (natCast_isUnit (R := R) (by decide))
  exact hu.mul_right_eq_zero.mp h

/-- **From a three-part split kernel check to an identity on the model.** -/
theorem identity_of_check_split3 (ps₁ ps₂ ps₃ : List Term) (L₁ L₂ : List (ℕ × ℕ))
    (h₁ : slotsEq (evalO nfTree ps₁) L₁ = true)
    (h₂ : slotsEq (evalFrom nfTree nfTree (AT.ofList L₁) ps₂) L₂ = true)
    (h₃ : (evalFrom nfTree nfTree (AT.ofList L₂) ps₃).allZero = true)
    (hB : wsum (ps₁ ++ ps₂ ++ ps₃) * rowM ^ 2 < 2 ^ kb)
    (hT : (ps₁ ++ ps₂ ++ ps₃).all (fun q => termOK nfTree q && q.a.wf && q.b.wf) = true)
    [Algebra ℚ R] (x y : Fin 9 → R) (hx : OnQ x) (hy : OnQ y) : evalTerms x y (ps₁ ++ ps₂ ++ ps₃) = 0 := by
  have hX : ∀ l ∈ nfTree.leaves, leafOKX 144 rowM l = true := fun l hl => leafOKX_of_leafOK (leaves_ok l hl)
  have h := sound2V nfTree nfTree stdc stdc 144 144 kb rowM rowM nfDelta nfDelta (by norm_num) hX leaves_ok
    (ps₁ ++ ps₂ ++ ps₃) (evalO2_split3 nfTree nfTree (by norm_num) hX ps₁ ps₂ ps₃ L₁ L₂ h₁ h₂ h₃)
    (by rw [← sq]; exact hB)
    (fun q hq => by
      have := List.all_eq_true.mp hT q hq
      simpa [termOK, Bool.and_eq_true, and_assoc] using this)
    x y (nfValid x hx) (nfValid y hy)
  have hu : IsUnit ((nfDelta : R) * nfDelta) :=
    (natCast_isUnit (R := R) (by decide)).mul (natCast_isUnit (R := R) (by decide))
  exact hu.mul_right_eq_zero.mp h

end LSG.Jac

