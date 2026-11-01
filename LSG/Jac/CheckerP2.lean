/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.CheckerDiag
import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table

/-!
# Checker extensions for P2 (`dup_ne_zero`): exact single-copy identities of degree 7

* `evalOd d`: the accumulator of `evalO2` with `2^d` slots (P2 uses an identity table with 6435 slots, `d = 13`).
* `idSeqOK`: the leaves form an identity table with indices `n, n + 1, …` (no `List.getD` lookups).
* `p2Terms D i Cs Hs`: the identity `D X_i⁷ − Σ_k C_k(X) dup_k(X) − Σ_j H_j(X) Q_j(X)` (single copy `X`; the
  `Y`-side is the degree-0 table `T0`).

Soundness: `LSG.Jac.P2Sound`. Core-only imports.
-/

namespace LSG.Jac

open Data

/-- `evalO2` with `2^d` accumulator slots. -/
noncomputable def evalOd (d : Nat) (trX trY : T) (ps : List Term) : AT := evalFrom trX trY (AT.zero d) ps

/-- The leaves are `⟨_, n + i, [(n + i, 1, false)], _⟩` in order. -/
noncomputable def idSeqOK (ls : List Leaf) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun l _ ih n => (Nat.beq l.idx n && decide (l.row = [(n, 1, false)])) && ih (n + 1)) ls

/-- The single-copy monomial `X^c`. -/
def monoSP (c : Nat) : SP := ⟨[(c, [(0, 1, false)])], [0]⟩

/-- A row `Σ ±n X^c` as a single-copy `SP`. -/
def rowSP (r : List (Nat × Nat × Bool)) : SP := ⟨r.map fun t => (t.1, [(0, t.2.1, t.2.2)]), [0]⟩

/-- The empty single-copy `SP`. -/
def zeroSP : SP := ⟨[], [0]⟩

/-- `D X_i⁷ − Σ_k C_k dup_k − Σ_j H_j Q_j` (single copy). -/
noncomputable def p2Terms (D i : Nat) (Cs Hs : List SP) : List Term :=
  ⟨D, false, monoSP (7 * 8 ^ i), oneSP⟩ ::
    (((List.range 9).map fun k => (⟨1, true, Cs.getD k zeroSP, diagSP (law k 4)⟩ : Term)) ++
      (List.range 9).map fun j => (⟨1, true, Hs.getD j zeroSP, rowSP (Qd.getD j [])⟩ : Term))

end LSG.Jac
