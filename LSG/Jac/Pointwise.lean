/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Diag
import LSG.Jac.Cert.Neg

/-!
# `law0(X, −X) ∝ e₄` (field `law0_neg` of `A1Facts`)

`law0_neg`: on `V(Q)` (any `ℚ`-algebra), `lawPt 0 x (negP x) k = 0` for `k ≠ 4`. By (S1) this is
`A_0^{(k)}(x, x) = 0`, a single-copy degree-4 identity checked in `LSG.Jac.Cert.Neg`.
-/

namespace LSG.Jac

open Data Cert

variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma diag_law_zero (k : ℕ) (x : Fin 9 → R) (hx : OnQ x)
    (hO : (evalO2 nfTree T0 [⟨1, false, diagSP (law 0 k), oneSP⟩]).allZero = true)
    (hB : wsum [⟨1, false, diagSP (law 0 k), oneSP⟩] * (rowM * 1) < 2 ^ kb)
    (hT : termOK2 nfTree T0 ⟨1, false, diagSP (law 0 k), oneSP⟩ = true)
    (hW : (diagSP (law 0 k)).wf = true) (hD : diagOK (law 0 k) = true) :
    evalSP x x (law 0 k) = 0 := by
  rw [← evalSP_diagSP x x _ hD]
  exact single_of_check _ hO hB hT hW x x hx

/-- **`law0(x, −x) ∝ e₄`** on the model. -/
theorem law0_neg (x : Fin 9 → R) (hx : OnQ x) (k : Fin 9) (hk : k ≠ 4) : lawPt 0 x (negP x) k = 0 := by
  simp only [lawPt]
  rw [law_S1]
  show evalSP x x (law ((0 : Fin 9) : ℕ) (k : ℕ)) = 0
  fin_cases k
  · exact diag_law_zero 0 x hx neg_0_O neg_0_B neg_0_T neg_0_W neg_0_D
  · exact diag_law_zero 1 x hx neg_1_O neg_1_B neg_1_T neg_1_W neg_1_D
  · exact diag_law_zero 2 x hx neg_2_O neg_2_B neg_2_T neg_2_W neg_2_D
  · exact diag_law_zero 3 x hx neg_3_O neg_3_B neg_3_T neg_3_W neg_3_D
  · exact absurd rfl hk
  · exact diag_law_zero 5 x hx neg_5_O neg_5_B neg_5_T neg_5_W neg_5_D
  · exact diag_law_zero 6 x hx neg_6_O neg_6_B neg_6_T neg_6_W neg_6_D
  · exact diag_law_zero 7 x hx neg_7_O neg_7_B neg_7_T neg_7_W neg_7_D
  · exact diag_law_zero 8 x hx neg_8_O neg_8_B neg_8_T neg_8_W neg_8_D

end LSG.Jac
