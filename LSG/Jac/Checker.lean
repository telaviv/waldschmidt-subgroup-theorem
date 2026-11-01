/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Tactic.Linter.Header

/-!
# The normal-form + Kronecker certificate checker: definitions (Stage A1c)

Everything here is *computable* and meant to be run by the kernel (`decide +kernel`); soundness is proved in
`LSG.Jac.CheckerSound`. Design: ABVAR §A0.3 (normal form modulo the quadrics plus two-level Kronecker packing, Nat-only
with sign-split pairs, no stored cofactors).

This file imports no mathematics (only the header linter option), so that the kernel checks run with a small
memory footprint; the semantics (`xmono`, `evalSP`, …) live in `LSG.Jac.CheckerSound`.

**Monomials.** A monomial `X^e` in 9 variables with all `e_i < 8` is encoded by its *code* `Σ e_i 8^i`;
`xmono x c = ∏ x_i ^ digit c i` (`LSG.Jac.CheckerSound`). Adding codes multiplies monomials when no base-8 digit carries (`nocarry`).

**Sparse polynomials.** A row entry `(c, n, s)` is the term `(−1)^s n X^c` (`sval n s = ±n`). A bihomogeneous
polynomial `F(X, Y)` is an `SP`: rows `(α, [(β, n, s)])` standing for `Σ_α X^α Σ_β ±n Y^β`, plus a list `yc`
containing every `β` that occurs.

**Normal-form table.** A search tree `T` of `Leaf`s. A leaf stores a degree-`d` monomial code `key`, an index `idx`,
its normal form `row = [(slot s, n, sign)]` (a combination of the standard monomials, scaled by a fixed `δ`), and the
Kronecker packing `ky = Σ ±n 2^{b s}` (`N` slots of `b` bits).

**The checker** for an identity `Σ_q ±c_q F_q G_q ≡ 0` (bidegree `(d, d)`) computes
for every standard slot `s` of the `X`-side the integer `Σ_q ±c_q Σ_{α,α'} NF(α+α')_s · Σ_{β,β'} ±n n' ky(β+β')`, i.e.
row `s` of `(NF ⊗ NF)(Σ_q ±c_q F_q G_q)` packed along the `Y`-side, in an accumulator tree `AT` with one signed pair
per slot (the `X`-side is not packed: this keeps all intermediate numbers at `N b` bits, which bounds kernel memory).
-/

namespace LSG.Jac

/-! ## Monomial codes -/

/-- The `i`-th base-8 digit of a code. -/
def digit (c i : Nat) : Nat := c / 8 ^ i % 8

/-- No base-8 carry in `a + b` (in the 9 digits that matter). -/
def nocarry (a b : Nat) : Bool := (List.range 9).all fun i => digit (a + b) i == digit a i + digit b i

/-- The signed integer `±n`. -/
def sval (n : Nat) (s : Bool) : Int := if s then -(n : Int) else n

/-! ## Data structures -/

/-- A leaf of the normal-form table. -/
structure Leaf where
  key : Nat
  idx : Nat
  row : List (Nat × Nat × Bool)
  ky : Nat × Nat

/-- The normal-form table: a binary search tree on codes. -/
inductive T where
  | leaf (l : Leaf)
  | node (k : Nat) (l r : T)

/-- Lookup (total: returns *some* leaf; the checks verify that its key is the one asked for). Defined through
the recursor with `cond`/`Nat.blt` (no `brecOn` or `Decidable` unfolding in the kernel; equations in
`LSG.Jac.CheckerSound`). -/
noncomputable def T.find (t : T) : Nat → Leaf :=
  T.rec (motive := fun _ => Nat → Leaf) (fun v _ => v)
    (fun k _ _ fl fr c => cond (Nat.blt c k) (fl c) (fr c)) t

/-- All leaves. -/
def T.leaves : T → List Leaf
  | .leaf v => [v]
  | .node _ l r => l.leaves ++ r.leaves

/-- A sparse bihomogeneous polynomial in `(X, Y)`. -/
structure SP where
  rows : List (Nat × List (Nat × Nat × Bool))
  yc : List Nat

/-- One product `±c · a · b` of an identity. -/
structure Term where
  c : Nat
  neg : Bool
  a : SP
  b : SP

/-! ## Signed Nat-pair arithmetic (`(P, N)` stands for `P − N`) -/

/-- `acc + (±c) · v`. -/
def addS (acc : Nat × Nat) (c : Nat) (neg : Bool) (v : Nat × Nat) : Nat × Nat :=
  cond neg (acc.1 + c * v.2, acc.2 + c * v.1) (acc.1 + c * v.1, acc.2 + c * v.2)

/-- Left fold through the recursor (`lfold f l b = l.foldl f b`, `lfold_eq`): cheaper in the kernel than the
structural `List.foldl` (measured: −40% memory, −45% time on a V2′ identity). -/
noncomputable def lfold {α β : Type} (f : β → α → β) (l : List α) : β → β :=
  List.rec (motive := fun _ => β → β) (fun b => b) (fun a _ ih b => ih (f b a)) l

/-- Product of signed pairs. -/
def mulS (x y : Nat × Nat) : Nat × Nat := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Kronecker packing of a row with slot width `w`: `Σ ±n 2^{w s}`. -/
def packS (w : Nat) (row : List (Nat × Nat × Bool)) : Nat × Nat :=
  row.foldl (fun acc t => addS acc t.2.1 t.2.2 (1 <<< (w * t.1), 0)) (0, 0)

/-! ## The checker -/

/-- Inner loop: `acc + Σ_{t ∈ p, u ∈ q} ±n_t n_u · ky(β_t + β_u)`. -/
noncomputable def yprod (tr : T) (p q : List (Nat × Nat × Bool)) (acc : Nat × Nat) : Nat × Nat :=
  lfold (fun acc t => lfold (fun acc2 u =>
    addS acc2 (t.2.1 * u.2.1) (t.2.2 != u.2.2) (tr.find (t.1 + u.1)).ky) q acc) p acc

/-- Accumulator: a binary tree of signed pairs (slot `i` is reached through the bits of `i`). -/
inductive AT where
  | leaf (v : Nat × Nat)
  | node (l r : AT)

/-- The zero tree of depth `d` (`2^d` slots). -/
def AT.zero : Nat → AT
  | 0 => .leaf (0, 0)
  | d + 1 => .node (AT.zero d) (AT.zero d)

/-- Slot `i`. -/
noncomputable def AT.get (t : AT) : Nat → Nat × Nat :=
  AT.rec (motive := fun _ => Nat → Nat × Nat) (fun a _ => a)
    (fun _ _ gl gr i => cond (Nat.beq (i % 2) 0) (gl (i / 2)) (gr (i / 2))) t

/-- Add `±c · v` to slot `i`. -/
noncomputable def AT.addAt (t : AT) : Nat → Nat → Bool → Nat × Nat → AT :=
  AT.rec (motive := fun _ => Nat → Nat → Bool → Nat × Nat → AT)
    (fun a _ c neg v => .leaf (addS a c neg v))
    (fun l r fl fr i c neg v =>
      cond (Nat.beq (i % 2) 0) (.node (fl (i / 2) c neg v) r) (.node l (fr (i / 2) c neg v))) t

/-- Every slot is zero. -/
noncomputable def AT.allZero (t : AT) : Bool :=
  AT.rec (motive := fun _ => Bool) (fun a => Nat.beq a.1 a.2) (fun _ _ zl zr => cond zl zr false) t

/-- Add `±c · NF(μ)_s · v` to every slot `s` (`row` = the normal form of `μ`). -/
noncomputable def addRow (acc : AT) (row : List (Nat × Nat × Bool)) (c : Nat) (neg : Bool) (v : Nat × Nat) :
    AT :=
  lfold (fun acc t => acc.addAt t.1 (c * t.2.1) (neg != t.2.2) v) row acc

/-- `acc + (±c) Σ_{α, α'} NF(α + α') ⊗ yprod(rows)`. -/
noncomputable def prodNF (trX trY : T) (c : Nat) (neg : Bool) (A B : SP) (acc : AT) : AT :=
  lfold (fun acc ra => lfold (fun acc rb =>
    addRow acc (trX.find (ra.1 + rb.1)).row c neg (yprod trY ra.2 rb.2 (0, 0))) B.rows acc) A.rows acc

/-- The normal form of `Σ_q ±c_q a_q b_q`, `Y`-side packed, one slot per `X`-side standard monomial
(256 slots). -/
noncomputable def evalFrom (trX trY : T) (acc : AT) (ps : List Term) : AT :=
  lfold (fun acc q => prodNF trX trY q.c q.neg q.a q.b acc) ps acc

/-- The normal form of `Σ_q ±c_q a_q b_q` from the zero tree, with an `X`-side table `trX` and a `Y`-side
table `trY` (they may have different degrees, e.g. bidegree `(5, 4)`). -/
noncomputable def evalO2 (trX trY : T) (ps : List Term) : AT := evalFrom trX trY (AT.zero 8) ps

/-- The same table on both sides (bidegree `(4, 4)`). -/
noncomputable def evalO (tr : T) (ps : List Term) : AT := evalO2 tr tr ps

/-- `L¹` norm of a row. -/
def rowN (r : List (Nat × Nat × Bool)) : Nat := (r.map fun t => t.2.1).sum

/-- `Σ_q c_q Σ_{α, α'} ‖row_α‖₁ ‖row_α'‖₁` (`= Σ_q c_q ‖a_q‖₁ ‖b_q‖₁`): the total weight of the expanded identity. -/
def wsum (ps : List Term) : Nat :=
  (ps.map fun q => q.c * (q.a.rows.map fun ra => (q.b.rows.map fun rb => rowN ra.2 * rowN rb.2).sum).sum).sum

/-- Every pair of codes adds without carry to a key of the table. -/
noncomputable def pairOK (tr : T) (l₁ l₂ : List Nat) : Bool :=
  l₁.all fun a => l₂.all fun c => nocarry a c && (tr.find (a + c)).key == a + c

/-- Structural check of one product: code pairs on both sides. -/
noncomputable def termOK2 (trX trY : T) (q : Term) : Bool :=
  pairOK trX (q.a.rows.map (·.1)) (q.b.rows.map (·.1)) && pairOK trY q.a.yc q.b.yc

/-- `termOK2` with one table. -/
noncomputable def termOK (tr : T) (q : Term) : Bool := termOK2 tr tr q

/-- Well-formedness of an `SP`: `yc` lists every `Y`-code. -/
def SP.wf (p : SP) : Bool := p.rows.all fun r => r.2.all fun t => p.yc.contains t.1

/-- The `X`-side table invariants: slots `< N`, row norms `≤ M`. -/
def leafOKX (N M : Nat) (l : Leaf) : Bool := l.row.all (fun t => decide (t.1 < N)) && decide (rowN l.row ≤ M)

/-- The table invariants: correct packings, slots `< N`, row norms `≤ M`. -/
def leafOK (N b M : Nat) (l : Leaf) : Bool :=
  l.ky == packS b l.row && l.row.all (fun t => decide (t.1 < N)) &&
    decide (rowN l.row ≤ M)

/-! ## The normal-form certificate checker (soundness: `LSG.Jac.NFSound`) -/

/-- The signed terms `(|w|, sign, code)` of `δ X^μ − NF(μ) − Σ_j c_j Q_j`. -/
def nfTerms (δ : Nat) (stdc : List Nat) (Qd : List (List (Nat × Nat × Bool))) (μ : Nat)
    (row : List (Nat × Nat × Bool)) (cofs : List (List (Nat × Nat × Bool))) : List (Nat × Bool × Nat) :=
  (δ, false, μ) :: ((row.map fun t => (t.2.1, !t.2.2, stdc.getD t.1 0)) ++
    ((cofs.zip Qd).flatMap fun cq => cq.1.flatMap fun a => cq.2.map fun q =>
      (a.2.1 * q.2.1, !(a.2.2 != q.2.2), a.1 + q.1)))

/-- `Σ ±w 2^{B · idx(code)}` as a signed Nat pair. -/
noncomputable def nfPack (tr : T) (B : Nat) (L : List (Nat × Bool × Nat)) : Nat × Nat :=
  L.foldl (fun acc e => addS acc e.1 e.2.1 (1 <<< (B * (tr.find e.2.2).idx), 0)) (0, 0)

/-- The check of one leaf against its cofactors. -/
noncomputable def nfEntryOK (tr : T) (B K δ : Nat) (stdc : List Nat) (Qd : List (List (Nat × Nat × Bool))) (l : Leaf)
    (cofs : List (List (Nat × Nat × Bool))) : Bool :=
  let L := nfTerms δ stdc Qd l.key l.row cofs
  L.all (fun e => (tr.find e.2.2).key == e.2.2 && decide ((tr.find e.2.2).idx < K)) &&
    (cofs.zip Qd).all (fun cq => cq.1.all fun a => cq.2.all fun q => nocarry a.1 q.1) &&
    decide ((L.map (·.1)).sum < 2 ^ B) &&
    (nfPack tr B L).1 == (nfPack tr B L).2

/-- The check of a whole table: keys by index, and every leaf against its certificate (same order). -/
noncomputable def nfAllOK (tr : T) (B K δ : Nat) (stdc : List Nat) (Qd : List (List (Nat × Nat × Bool))) (keys : List Nat)
    (cert : List (Nat × List (List (Nat × Nat × Bool)))) : Bool :=
  tr.leaves.all (fun l => keys.getD l.idx 0 == l.key) && tr.leaves.length == cert.length &&
    (tr.leaves.zip cert).all fun p => p.2.1 == p.1.key && nfEntryOK tr B K δ stdc Qd p.1 p.2.2

end LSG.Jac
