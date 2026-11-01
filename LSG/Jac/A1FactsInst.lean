/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.A1Facts
import LSG.Jac.V2
import LSG.Jac.V1
import LSG.Jac.V1L4
import LSG.Jac.Sym
import LSG.Jac.W4
import LSG.Jac.Pointwise
import LSG.Jac.Glue
import LSG.Jac.Special
import LSG.Jac.WTables

/-!
# The A1 → A2 interface: building `LSG.JacAn.A1Facts` (STAGE_A1 §9)

`mkA1Facts` builds the structure from A1's certified facts. The fields that are not certified yet are its
hypotheses, stated exactly as in `A1Facts`: the equivariance identities `E1_40`, `E1_44`, `E1_4`, `E2_4` (queue item
5) and `dup_ne_zero` (P2, a named hypothesis by the coordinator's decision). Everything else is discharged here.
-/

noncomputable section

namespace LSG.Jac

open LSG.JacAn Finset

/-- `law0 = lawPt 0` over `ℂ`. -/
abbrev law0C : P9 → P9 → P9 := lawPt 0

/-- `dup` over `ℂ`. -/
abbrev dupC : P9 → P9 := dup

/-- Formal partials of law 0 in the first argument. -/
def dlaw0C (i : Fin 9) (X Y : P9) : P9 := fun l => evalSP X Y (dXsp i (Data.law l 0))

/-- Formal partials of `dup`. -/
def ddupC (i : Fin 9) (X : P9) : P9 :=
  fun l => evalSP X X (dXsp i (Data.law l 4)) + evalSP X X (dYsp i (Data.law l 4))

/-- The chart-4 flow `W4 = W4n / 4`. -/
def W4C (j : Fin 2) (X : P9) : P9 := fun i => W4n X j i / 4

lemma prj_comp_sum (v : Fin 9 → P9) (l : Fin 9) :
    (prj l).comp (∑ i : Fin 9, (prj i).smulRight (v i)) = ∑ i : Fin 9, (v i l) • prj i := by
  ext w; simp [prj, Finset.sum_apply]
  exact sum_congr rfl fun i _ => mul_comm _ _

lemma hasFDerivAt_law0C (X Y : P9) :
    HasFDerivAt (fun X => law0C X Y) (∑ i : Fin 9, (prj i).smulRight (dlaw0C i X Y)) X := by
  refine hasFDerivAt_pi'' fun l => ?_
  rw [prj_comp_sum]
  have h := hasFDerivAt_evalSP_left X Y (Data.law l 0) (law_decOK l 0)
  simpa [law0C, lawPt, A32, dlaw0C, pj, prj] using h

lemma hasFDerivAt_dupC (X : P9) : HasFDerivAt dupC (∑ i : Fin 9, (prj i).smulRight (ddupC i X)) X := by
  refine hasFDerivAt_pi'' fun l => ?_
  rw [prj_comp_sum]
  have h := hasFDerivAt_evalSP_diag X (Data.law l 4) (law_decOK l 4)
  simpa [dupC, dup, lawPt, A32, ddupC, pj, prj] using h

@[fun_prop]
lemma analyticAt_coord (k : Fin 9) (X : P9) : AnalyticAt ℂ (fun X : P9 => X k) X :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 9 => ℂ) k).analyticAt X

lemma W4C_analytic (j : Fin 2) : AnalyticOnNhd ℂ (W4C j) Set.univ := by
  intro X _
  refine (analyticAt_pi_iff (f := fun (i : Fin 9) (X : P9) => W4n X j i / 4)).mpr fun i => ?_
  fin_cases j <;> fin_cases i <;> simp [W4n] <;> fun_prop

lemma W4C_smul (j : Fin 2) (a : ℂ) (X : P9) : W4C j (a • X) = a ^ 2 • W4C j X := by
  funext i
  fin_cases j <;> fin_cases i <;> simp [W4C, W4n] <;> ring

lemma flowW_eq (j : Fin 2) (X : P9) (l : Fin 9) : flowW j X l = Wn X j l / 2 := by
  fin_cases j <;> fin_cases l <;> simp [flowW, Wn] <;> ring

lemma grantJ_eq (m : Fin 4 → ℂ) : grantJ m = grant m := by
  funext k; fin_cases k <;> simp [grantJ, grant, grantZ] <;> ring

lemma law0_analyticC : AnalyticOnNhd ℂ (fun XY : P9 × P9 => law0C XY.1 XY.2) Set.univ := by
  intro XY _
  refine analyticAt_pi_iff.mpr fun l => ?_
  exact analyticAt_evalSP analyticAt_fst analyticAt_snd (Data.law l 0)

lemma dup_analyticC : AnalyticOnNhd ℂ dupC Set.univ := by
  intro X _
  refine analyticAt_pi_iff.mpr fun l => ?_
  exact analyticAt_evalSP analyticAt_id analyticAt_id (Data.law l 4)

lemma onQ_closedC : IsClosed {X : P9 | OnQ X} := by
  have : {X : P9 | OnQ X} = ⋂ j : Fin 9, (fun X : P9 => quad X j) ⁻¹' {0} := by
    ext X; simp [onQ_iff]
  rw [this]
  refine isClosed_iInter fun j => isClosed_singleton.preimage ?_
  fin_cases j <;> simp [quad] <;> fun_prop

lemma W4C_negP (j : Fin 2) (X : P9) : W4C j (negP X) = negP (W4C j X) := by
  funext i
  fin_cases j <;> fin_cases i <;> simp [W4C, W4n, negP] <;> ring

lemma lawK_analyticC (k m : Fin 9) : AnalyticOnNhd ℂ (fun XY : P9 × P9 => A32 k m XY.1 XY.2) Set.univ :=
  fun _ _ => analyticAt_evalSP analyticAt_fst analyticAt_snd (Data.law k m)

/-- **The interface instance**, given the not-yet-certified fields. -/
def mkA1Facts
    (E1_40 : ∀ X Y : P9, OnQ X → OnQ Y → ∀ (j : Fin 2) (l : Fin 9),
      law0C X Y 0 * derivAlong W4C j (fun i X => dlaw0C i X Y) X l -
        law0C X Y l * derivAlong W4C j (fun i X => dlaw0C i X Y) X 0 = X 4 * flowW j (law0C X Y) l)
    (E1_44 : ∀ X Y : P9, OnQ X → OnQ Y → ∀ (j : Fin 2) (l : Fin 9),
      law0C X Y 4 * derivAlong W4C j (fun i X => dlaw0C i X Y) X l -
        law0C X Y l * derivAlong W4C j (fun i X => dlaw0C i X Y) X 4 = X 4 * W4C j (law0C X Y) l)
    (E1_4 : ∀ X Y : P9, OnQ X → OnQ Y → ∀ (j : Fin 2) (l : Fin 9),
      law0C X Y 4 * derivAlong flowW j (fun i X => dlaw0C i X Y) X l -
        law0C X Y l * derivAlong flowW j (fun i X => dlaw0C i X Y) X 4 = X 0 * W4C j (law0C X Y) l)
    (E2_4 : ∀ X : P9, OnQ X → ∀ (j : Fin 2) (l : Fin 9),
      dupC X 4 * derivAlong W4C j ddupC X l - dupC X l * derivAlong W4C j ddupC X 4 =
        2 * X 4 * W4C j (dupC X) l)
    (dup_ne_zero : ∀ X : P9, OnQ X → X ≠ 0 → dupC X ≠ 0) : A1Facts where
  OnQ := OnQ
  onQ_smul a X hX := onQ_smul a hX
  law0 := law0C
  dup := dupC
  negP := negP
  dlaw0 := dlaw0C
  ddup := ddupC
  hasFDerivAt_law0 := hasFDerivAt_law0C
  hasFDerivAt_dup := hasFDerivAt_dupC
  W4 := W4C
  W4_contDiff j := (W4C_analytic j).contDiff.restrict_scalars ℝ
  W4_analytic := W4C_analytic
  W4_smul := W4C_smul
  W4_four j X := by simp [W4C, W4n]
  E1_40 := E1_40
  E1_44 := E1_44
  E1_4 := E1_4
  E2_4 := E2_4
  law0_onQ X Y hX hY := law0_onQ X Y hX hY
  dup_onQ X hX := dup_onQ X hX
  negP_onQ X hX := negP_onQ hX
  origin_onQ := origin_onQ
  grantJ_onQ m h1 h0 := by rw [grantJ_eq]; exact grant_onQ ⟨h1, h0⟩
  law0_neg X hX k hk := law0_neg X hX k hk
  dup_origin := ⟨-8, by norm_num, dup_origin⟩
  law0_origin X := lawPt0_origin X
  law0_analytic := law0_analyticC
  dup_analytic := dup_analyticC
  dup_smul a X := dup_smul a X
  dup_ne_zero := dup_ne_zero
  special_hP₀ := special_hP0
  onQ_closed := onQ_closedC
  negP_eq _ := rfl
  lawK := A32
  law0_lawK _ _ _ := rfl
  lawK_S1 k m X Y := law_S1 k m X Y
  rank_one k m X Y hX hY := rank_one k m X Y hX hY
  lawK_smul_left k m a X Y := by simpa [lawPt] using congrFun (lawPt_smul_left m a X Y) k
  lawK_smul_right k m a X Y := by simpa [lawPt] using congrFun (lawPt_smul_right m a X Y) k
  lawK_analytic := lawK_analyticC
  W4_negP j X _ := W4C_negP j X
  law0_smul_left a X Y := lawPt_smul_left 0 a X Y
  law0_smul_right a X Y := lawPt_smul_right 0 a X Y
  swapSign := -1
  swapSign_ne := by norm_num
  law0_swap X Y := by
    funext k
    have := law_S2 k 0 Y X
    simp only [lawPt, Pi.smul_apply, smul_eq_mul]
    rw [this]; simp [lawEps]
  W4_origin_indep := by
    simp [W4C, W4n, origin9]
  W4rel X hX j l := by
    have h := W4rel j j.2 l X hX
    simp only [flowW_eq, W4C, Fin.val_zero]
    linear_combination h / 4
  onQ_quad := onQ_quadC
  W4num := W4num
  W4den := 4
  W4den_pos := by norm_num
  W4H := 32
  W4num_bound := W4num_bound
  W4_table j X l := W4_tableN j X l
  W8 := W8C
  W8num := W8num
  W8den := 4
  W8den_pos := by norm_num
  W8H := 48
  W8num_bound := W8num_bound
  W8_table j X l := W8_tableN j X l
  W8rel X hX j l := by
    have h := W8rel j j.2 l X hX
    simp only [flowW_eq, W8C, Fin.val_zero]
    linear_combination h / 4
  W8_eight := W8_eightC

end LSG.Jac
