/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.P2Sound
import LSG.Jac.Cert.P2base
import LSG.Jac.Cert.P2_0
import LSG.Jac.Cert.P2_1
import LSG.Jac.Cert.P2_2
import LSG.Jac.Cert.P2_3
import LSG.Jac.Cert.P2_4
import LSG.Jac.Cert.P2_5
import LSG.Jac.Cert.P2_6
import LSG.Jac.Cert.P2_7
import LSG.Jac.Cert.P2_8

/-!
# P2: `dup` has no zeros on `V(Q) ∖ {0}` (degree-7 Nullstellensatz, STAGE_A1 §9.7, §10)

For each `i`: `D_i X_i⁷ = Σ_k C_ik(X) dup_k(X) + Σ_j H_ij(X) Q_j(X)` exactly (`Cert/P2_<i>.lean`, kernel-checked
through the degree-7 identity table; cofactors from `scripts/jac/gen_jac_p2.py`, untrusted). Hence on `V(Q)`,
`dup X = 0` forces `X_i⁷ = 0` for every `i`. Holds over any domain of characteristic 0.
-/

namespace LSG.Jac

open Data Cert

variable {R : Type*} [CommRing R]

/-- **P2, pointwise form.** -/
theorem eq_zero_of_dup [IsDomain R] [CharZero R] (x : Fin 9 → R) (hx : OnQ x)
    (hd : ∀ k : Fin 9, evalSP x x (law k 4) = 0) : x = 0 := by
  have key : ∀ (i : Fin 9) (ps : List Term) (D : ℕ) (Cs Hs : List SP), D ≠ 0 → ps = p2Terms D i Cs Hs →
      evalTerms x x ps = 0 → x i = 0 := by
    intro i ps D Cs Hs hD hps h
    rw [hps, evalTerms_p2 D i Cs Hs x x hx hd dup_diagOK] at h
    have hD' : (D : R) ≠ 0 := Nat.cast_ne_zero.mpr hD
    exact pow_eq_zero_iff (n := 7) (by norm_num) |>.mp ((mul_eq_zero.mp h).resolve_left hD')
  have hN : idTree7.leaves.length ≤ 2 ^ 13 := by rw [p7_len]; norm_num
  funext i
  fin_cases i
  · exact key _ p2ps_0 _ _ _ (by decide) rfl (exact_of_idSeq 13 idTree7 p7_seq hN _ p2_O_0 p2_B_0 p2_T_0 x x)
  · exact key _ p2ps_1 _ _ _ (by decide) rfl (exact_of_idSeq 13 idTree7 p7_seq hN _ p2_O_1 p2_B_1 p2_T_1 x x)
  · exact key _ p2ps_2 _ _ _ (by decide) rfl (exact_of_idSeq 13 idTree7 p7_seq hN _ p2_O_2 p2_B_2 p2_T_2 x x)
  · exact key _ p2ps_3 _ _ _ (by decide) rfl (exact_of_idSeq 13 idTree7 p7_seq hN _ p2_O_3 p2_B_3 p2_T_3 x x)
  · exact key _ p2ps_4 _ _ _ (by decide) rfl (exact_of_idSeq 13 idTree7 p7_seq hN _ p2_O_4 p2_B_4 p2_T_4 x x)
  · exact key _ p2ps_5 _ _ _ (by decide) rfl (exact_of_idSeq 13 idTree7 p7_seq hN _ p2_O_5 p2_B_5 p2_T_5 x x)
  · exact key _ p2ps_6 _ _ _ (by decide) rfl (exact_of_idSeq 13 idTree7 p7_seq hN _ p2_O_6 p2_B_6 p2_T_6 x x)
  · exact key _ p2ps_7 _ _ _ (by decide) rfl (exact_of_idSeq 13 idTree7 p7_seq hN _ p2_O_7 p2_B_7 p2_T_7 x x)
  · exact key _ p2ps_8 _ _ _ (by decide) rfl (exact_of_idSeq 13 idTree7 p7_seq hN _ p2_O_8 p2_B_8 p2_T_8 x x)

/-- **P2 (`dup_ne_zero`)**, in the form of the `A1Facts` field. -/
theorem dup_ne_zeroC : ∀ X : Fin 9 → ℂ, OnQ X → X ≠ 0 → dup X ≠ 0 := by
  intro X hX hne hdup
  exact hne (eq_zero_of_dup X hX fun k => by simpa [dup, lawPt, A32] using congrFun hdup k)

end LSG.Jac
