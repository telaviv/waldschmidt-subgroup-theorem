/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.NFSound
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert

/-!
# The degree-4 normal-form table is valid on the P⁸ model (Stage A1c)

Kernel checks (`decide +kernel`) of the generated table `Data.nfTree` (495 leaves, 144 standard monomials, slot width
`Data.kb`, scale `Data.nfDelta = 23040`):

* `leaves_ok`: the Kronecker packings `kx`, `ky` of every leaf are those of its row, slots are `< 144`, and row norms
  are `≤ Data.rowM`;
* `nf_ok`: every leaf is `δ X^μ ≡ NF(μ)` modulo the 9 quadrics, by its cofactor certificate (`Data.nfCert`).

Consequence (`nfValid`): at every point `x` of `V(Q₀, …, Q₈)` over any commutative ring, the table is a valid normal
form (`NFValid`), which is the hypothesis of the checker's soundness theorem `sound_bidegree`.
-/

namespace LSG.Jac

open Data

/-- The quadric `Q_j` of the P⁸ model, evaluated at `x` (from the data `Data.Qd`). -/
def Qe {R : Type*} [CommRing R] (j : Fin 9) (x : Fin 9 → R) : R := evalRow x (Qd.getD j [])

/-- The point `x` lies on the 9 quadrics. -/
def OnQ {R : Type*} [CommRing R] (x : Fin 9 → R) : Prop := ∀ j : Fin 9, Qe j x = 0

theorem leaves_ok : ∀ l ∈ nfTree.leaves, leafOK 144 kb rowM l = true := by
  have h : nfTree.leaves.all (leafOK 144 kb rowM) = true := by decide +kernel
  exact List.all_eq_true.mp h

theorem nf_ok : nfAllOK nfTree 32 495 nfDelta stdc Qd keys nfCert = true := by decide +kernel

theorem Qd_length : Qd.length = 9 := rfl

/-- **The normal-form table is valid at every point of the model.** -/
theorem nfValid {R : Type*} [CommRing R] (x : Fin 9 → R) (hx : OnQ x) : NFValid nfTree stdc nfDelta x := by
  refine nfValid_of_check _ _ _ _ _ _ _ _ nf_ok x fun q hq => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  have := hx ⟨i, Qd_length ▸ hi⟩
  simpa [Qe, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

end LSG.Jac
