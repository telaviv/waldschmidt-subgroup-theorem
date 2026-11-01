/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.TableFacts5
import LSG.Jac.Laws

/-!
# Bridges from the E1 kernel checks to identities

* `identity_X5`: bidegree (5,4) (`X`-table `nfTree5`, `Y`-table `nfTree4b`), split by `X`-slot ranges.
* `identity_Y5`: bidegree (4,5) (`X`-table `nfTree`, `Y`-table `nfTree5`), split by `X`-slot ranges.
* `identity_exact`: exact polynomial identities through the identity tables (`X`-degree 3/2, `Y`-degree 2/3).
-/

namespace LSG.Jac

open Data Cert

variable {R : Type*} [CommRing R]

lemma leavesX5 : ∀ l ∈ nfTree5.leaves, leafOKX 225 rowM5 l = true :=
  fun l hl => leafOKX_of_leafOK (List.all_eq_true.mp leaves_ok5 l hl)

lemma leavesY4b : ∀ l ∈ nfTree4b.leaves, leafOK 144 kb4b rowM l = true :=
  fun l hl => List.all_eq_true.mp leaves_ok4b l hl

lemma leavesX4 : ∀ l ∈ nfTree.leaves, leafOKX 144 rowM l = true :=
  fun l hl => leafOKX_of_leafOK (leaves_ok l hl)

lemma leavesY5 : ∀ l ∈ nfTree5.leaves, leafOK 225 kb5 rowM5 l = true :=
  fun l hl => List.all_eq_true.mp leaves_ok5 l hl

lemma rowsN_of {tr : T} {N M : ℕ} (h : ∀ l ∈ tr.leaves, leafOKX N M l = true) :
    ∀ μ, ∀ t ∈ (tr.find μ).row, t.1 < N := fun μ t ht => (leafOKX_spec (h _ (tr.find_mem μ))).1 t ht

lemma termOK2_all {trX trY : T} {ps : List Term}
    (hT : ps.all (fun q => termOK2 trX trY q && q.a.wf && q.b.wf) = true) :
    ∀ q ∈ ps, termOK2 trX trY q = true ∧ q.a.wf = true ∧ q.b.wf = true := fun q hq => by
  have := List.all_eq_true.mp hT q hq
  simpa [Bool.and_eq_true, and_assoc] using this

/-- **Bidegree (5,4), split by `X`-slot ranges.** -/
theorem identity_X5 [Algebra ℚ R] (ps : List Term) (rs : List (ℕ × ℕ))
    (hcov : ((List.range 225).all fun j => rs.any fun r => Nat.ble r.1 j && Nat.blt j r.2) = true)
    (hz : ∀ r ∈ rs, (evalO2 (nfTree5.mapRows (rowsIn r.1 r.2)) nfTree4b ps).allZero = true)
    (hB : wsum ps * (rowM5 * rowM) < 2 ^ kb4b)
    (hT : ps.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true)
    (x y : Fin 9 → R) (hx : OnQ x) (hy : OnQ y) : evalTerms x y ps = 0 := by
  have h := sound2V nfTree5 nfTree4b stdc5 stdc 225 144 kb4b rowM5 rowM nfDelta5 nfDelta (by norm_num)
    leavesX5 leavesY4b ps (zeros_of_ranges nfTree5 nfTree4b (by norm_num) (rowsN_of leavesX5) ps rs hcov hz)
    hB (termOK2_all hT) x y (nfValid5 x hx) (nfValid4b y hy)
  have hu : IsUnit ((nfDelta5 : R) * nfDelta) :=
    (natCast_isUnit (R := R) (by decide)).mul (natCast_isUnit (R := R) (by decide))
  exact hu.mul_right_eq_zero.mp h

/-- **Bidegree (4,5), split by `X`-slot ranges.** -/
theorem identity_Y5 [Algebra ℚ R] (ps : List Term) (rs : List (ℕ × ℕ))
    (hcov : ((List.range 144).all fun j => rs.any fun r => Nat.ble r.1 j && Nat.blt j r.2) = true)
    (hz : ∀ r ∈ rs, (evalO2 (nfTree.mapRows (rowsIn r.1 r.2)) nfTree5 ps).allZero = true)
    (hB : wsum ps * (rowM * rowM5) < 2 ^ kb5)
    (hT : ps.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true)
    (x y : Fin 9 → R) (hx : OnQ x) (hy : OnQ y) : evalTerms x y ps = 0 := by
  have h := sound2V nfTree nfTree5 stdc stdc5 144 225 kb5 rowM rowM5 nfDelta nfDelta5 (by norm_num)
    leavesX4 leavesY5 ps (zeros_of_ranges nfTree nfTree5 (by norm_num) (rowsN_of leavesX4) ps rs hcov hz)
    hB (termOK2_all hT) x y (nfValid x hx) (nfValid5 y hy)
  have hu : IsUnit ((nfDelta : R) * nfDelta5) :=
    (natCast_isUnit (R := R) (by decide)).mul (natCast_isUnit (R := R) (by decide))
  exact hu.mul_right_eq_zero.mp h

/-- **Exact identities** (`X`-degree 3, `Y`-degree 2). -/
theorem identity_exact32 (ps : List Term) (hO : (evalO2 idTree3 idTree2 ps).allZero = true)
    (hB : wsum ps * (1 * 1) < 2 ^ kbId)
    (hT : ps.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true)
    (x y : Fin 9 → R) : evalTerms x y ps = 0 := by
  have h := sound2 idTree3 idTree2 stdcId3 stdcId2 165 45 kbId 1 1 1 1 (by norm_num)
    (fun l hl => leafOKX_of_leafOK (List.all_eq_true.mp id3_leaves l hl)) (List.all_eq_true.mp id2_leaves)
    ps hO hB (termOK2_all hT) x y (nfValid_id3 x) (nfValid_id2 y)
  simpa using h

/-- **Exact identities** (`X`-degree 2, `Y`-degree 3). -/
theorem identity_exact23 (ps : List Term) (hO : (evalO2 idTree2 idTree3 ps).allZero = true)
    (hB : wsum ps * (1 * 1) < 2 ^ kbId)
    (hT : ps.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true)
    (x y : Fin 9 → R) : evalTerms x y ps = 0 := by
  have h := sound2 idTree2 idTree3 stdcId2 stdcId3 45 165 kbId 1 1 1 1 (by norm_num)
    (fun l hl => leafOKX_of_leafOK (List.all_eq_true.mp id2_leaves l hl)) (List.all_eq_true.mp id3_leaves)
    ps hO hB (termOK2_all hT) x y (nfValid_id2 x) (nfValid_id3 y)
  simpa using h

end LSG.Jac
