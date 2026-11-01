/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Checker

/-!
# Slot-range splitting, shifted factors, identity tables (computational)

* `T.mapRows f tr`: the table with every normal-form row replaced by `f row`; with `rowsIn lo hi` (keep the slots in
  `[lo, hi)`) a certificate is split over declarations by `X`-slot range, without intermediate literals: each
  declaration checks its slots zero (unneeded inner loops are never forced, the kernel being lazy).
* `shiftX f p`, `shiftY f p`: multiply an `SP` by `X_f` (resp. `Y_f`).
* `idOK tr stdc`: `tr` is an identity table (`row = [(idx, 1, +)]`, `stdc[idx] = key`), valid for `δ = 1` everywhere.
Soundness: `LSG.Jac.RangeSound`. Core-only imports.
-/

namespace LSG.Jac

/-- Replace every row of the table. -/
def T.mapRows (f : List (Nat × Nat × Bool) → List (Nat × Nat × Bool)) : T → T
  | .leaf l => .leaf ⟨l.key, l.idx, f l.row, l.ky⟩
  | .node k l r => .node k (l.mapRows f) (r.mapRows f)

/-- Keep the slots in `[lo, hi)`. -/
def rowsIn (lo hi : Nat) (r : List (Nat × Nat × Bool)) : List (Nat × Nat × Bool) :=
  r.filter fun t => Nat.ble lo t.1 && Nat.blt t.1 hi

/-- `X_f · p`. -/
def shiftX (f : Nat) (p : SP) : SP := ⟨p.rows.map fun r => (r.1 + 8 ^ f, r.2), p.yc⟩

/-- `Y_f · p`. -/
def shiftY (f : Nat) (p : SP) : SP :=
  ⟨p.rows.map fun r => (r.1, r.2.map fun t => (t.1 + 8 ^ f, t.2.1, t.2.2)), p.yc.map (· + 8 ^ f)⟩

/-- No carry when shifting by `X_f` / `Y_f`. -/
def shiftXOK (f : Nat) (p : SP) : Bool := p.rows.all fun r => nocarry r.1 (8 ^ f)

/-- No carry when shifting by `Y_f`. -/
def shiftYOK (f : Nat) (p : SP) : Bool := p.rows.all fun r => r.2.all fun t => nocarry t.1 (8 ^ f)

/-- `tr` is an identity table for `stdc`. -/
def idOK (tr : T) (stdc : List Nat) : Bool :=
  tr.leaves.all fun l => decide (l.row = [(l.idx, 1, false)]) && stdc.getD l.idx 0 == l.key

/-- Two tables have the same keys and rows (leaf by leaf). -/
def sameRows (t₁ t₂ : T) : Bool := decide ((t₁.leaves.map fun l => (l.key, l.row)) = t₂.leaves.map fun l => (l.key, l.row))

end LSG.Jac
