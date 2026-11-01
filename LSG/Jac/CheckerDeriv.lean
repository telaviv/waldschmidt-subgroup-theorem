/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Checker

/-!
# Formal partial derivatives of sparse polynomials (computational; Stage A1, flow identities)

`dXsp i p` and `dYsp i p` are the formal partial derivatives `∂p/∂X_i`, `∂p/∂Y_i` of an `SP` (monomial code `c` with
`d = digit c i ≥ 1` becomes `d · X^{c − 8^i}`). They are computed by the kernel inside the flow certificates; their
semantics (the evaluation identities, under the decidable `decOK` digit check) are in `LSG.Jac.Deriv`.
Core-only imports, like `LSG.Jac.Checker`.
-/

namespace LSG.Jac

/-- Lower the `i`-th digit of a monomial code (`X^c ↦ X^{c − 8^i}`). -/
def lowerCode (i c : Nat) : Nat := c - 8 ^ i

/-- `∂/∂X_i` of an `SP`. -/
def dXsp (i : Nat) (p : SP) : SP :=
  ⟨(p.rows.filter fun ra => digit ra.1 i != 0).map fun ra =>
      (lowerCode i ra.1, ra.2.map fun t => (t.1, digit ra.1 i * t.2.1, t.2.2)), p.yc⟩

/-- `∂/∂Y_i` of an `SP`. -/
def dYsp (i : Nat) (p : SP) : SP :=
  ⟨p.rows.map fun ra =>
      (ra.1, (ra.2.filter fun t => digit t.1 i != 0).map fun t =>
        (lowerCode i t.1, digit t.1 i * t.2.1, t.2.2)),
    (p.yc.filter fun β => digit β i != 0).map (lowerCode i)⟩

/-- Lowering digit `i` of `c` (when it is `≥ 1`) changes no other digit. -/
def decOK1 (i c : Nat) : Bool :=
  digit c i == 0 || (List.range 9).all fun k =>
    digit (lowerCode i c) k == (if k == i then digit c i - 1 else digit c k)

/-- The digit check for all codes of an `SP` (both sides), for every variable. -/
def decOK (p : SP) : Bool :=
  (List.range 9).all fun i => p.rows.all fun ra => decOK1 i ra.1 && ra.2.all fun t => decOK1 i t.1

end LSG.Jac
