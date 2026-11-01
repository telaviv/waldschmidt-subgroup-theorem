/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Checker

/-!
# Splitting a certificate over several declarations (computational)

Kernel memory grows with the work done inside one declaration (≈ 0.9 GB per (2,2)×(2,2) product). An identity with
many products is checked in two declarations: `slotsEq (evalO2 trX trY ps₁) L` (the accumulator after the first
products equals the literal slot list `L`), then `(evalFrom trX trY (AT.ofList L) ps₂).allZero` (continuing from
`L`). Soundness: `LSG.Jac.SplitSound`. Core-only imports.
-/

namespace LSG.Jac

/-- The perfect tree of depth `d` whose slot `j` is `f j`. -/
def AT.ofFn : Nat → (Nat → Nat × Nat) → AT
  | 0, f => .leaf (f 0)
  | d + 1, f => .node (AT.ofFn d fun i => f (2 * i)) (AT.ofFn d fun i => f (2 * i + 1))

/-- The depth-8 tree with slots read from a list. -/
def AT.ofList (L : List (Nat × Nat)) : AT := AT.ofFn 8 fun j => L.getD j (0, 0)

/-- Slot-by-slot equality of signed values (`P − N`) between a tree and a list (256 slots). -/
noncomputable def slotsEq (t : AT) (L : List (Nat × Nat)) : Bool :=
  (List.range 256).all fun j => (t.get j).1 + (L.getD j (0, 0)).2 == (L.getD j (0, 0)).1 + (t.get j).2

end LSG.Jac
