/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Checker

/-!
# Data checks for the symmetries (S1), (S2) of the addition laws (computational)

`flat p` lists the terms `(α, β, |c|, sign)` of an `SP`. (S1) `A_k^{(m)}(X, [−1]Y) = A_m^{(k)}(X, Y)` is the exact list
equality `s1OK` (signs flipped where `Y^β` has odd degree in `Y₄ … Y₇`); (S2) `A(Y, X) = ε A(X, Y)` is `s2OK`
(equality after swapping `α ↔ β` and sorting). Soundness: `LSG.Jac.Sym`. Core-only imports.
-/

namespace LSG.Jac

/-- The terms `(α, β, |c|, sign)` of an `SP`. -/
def flat (p : SP) : List (Nat × Nat × Nat × Bool) :=
  p.rows.flatMap fun ra => ra.2.map fun t => (ra.1, t.1, t.2.1, t.2.2)

/-- `Y^β` has odd degree in `Y₄, …, Y₇`. -/
def oddY (β : Nat) : Bool := (digit β 4 + digit β 5 + digit β 6 + digit β 7) % 2 == 1

/-- (S1) for the pair `p = A_k^{(m)}`, `q = A_m^{(k)}`. -/
def s1OK (p q : SP) : Bool :=
  decide (flat q = (flat p).map fun e => (e.1, e.2.1, e.2.2.1, xor e.2.2.2 (oddY e.2.1)))

/-- Lexicographic order on `(α, β)`. -/
def lexle (e f : Nat × Nat × Nat × Bool) : Bool := e.1 < f.1 || (e.1 == f.1 && e.2.1 ≤ f.2.1)

/-- Insertion into a `lexle`-sorted list (structural, kernel-reducible). -/
def insLex (e : Nat × Nat × Nat × Bool) : List (Nat × Nat × Nat × Bool) → List (Nat × Nat × Nat × Bool)
  | [] => [e]
  | f :: l => if lexle e f then e :: f :: l else f :: insLex e l

/-- Insertion sort for `lexle`. -/
def sortLex : List (Nat × Nat × Nat × Bool) → List (Nat × Nat × Nat × Bool)
  | [] => []
  | e :: l => insLex e (sortLex l)

/-- (S2) with sign `(−1)^neg`: the swapped, re-signed term list is a permutation of the original. -/
def s2OK (p : SP) (neg : Bool) : Bool :=
  decide (flat p = sortLex ((flat p).map fun e => (e.2.1, e.1, e.2.2.1, xor e.2.2.2 neg)))

end LSG.Jac
