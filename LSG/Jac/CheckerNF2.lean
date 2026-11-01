/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Checker

/-!
# Chunked normal-form table checks (computational)

`nfRangeOK tr … a cert` checks the leaves `a, a+1, …` of `tr` against consecutive certificates `cert` (so a large
table is checked over several declarations); `keysOK tr keys` checks the index→key list. Soundness:
`LSG.Jac.NFSound` (`nfRange_sound`). Core-only imports.
-/

namespace LSG.Jac

/-- Leaves `a, …, a + |cert| − 1` against `cert`. -/
noncomputable def nfRangeOK (tr : T) (B K δ : Nat) (stdc : List Nat) (Qd : List (List (Nat × Nat × Bool)))
    (a : Nat) (cert : List (Nat × List (List (Nat × Nat × Bool)))) : Bool :=
  decide (a + cert.length ≤ tr.leaves.length) &&
    ((tr.leaves.drop a).zip cert).all fun p => p.2.1 == p.1.key && nfEntryOK tr B K δ stdc Qd p.1 p.2.2

/-- The key list by index. -/
def keysOK (tr : T) (keys : List Nat) : Bool := tr.leaves.all fun l => keys.getD l.idx 0 == l.key

end LSG.Jac
