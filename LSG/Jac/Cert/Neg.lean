import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.CheckerDiag

/-! Raw kernel checks for `law0_neg` (STAGE_A1 §8.4): `A_0^{(k)}(X, X) ∈ I` for `k ≠ 4`, as single-copy forms
(`X`-table `nfTree`, `Y`-table `T0`). Written by hand (loop); the statements are uniform in `k`. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem neg_0_O : (evalO2 nfTree T0 [⟨1, false, diagSP (law 0 0), oneSP⟩]).allZero = true := by decide +kernel
theorem neg_0_B : wsum [⟨1, false, diagSP (law 0 0), oneSP⟩] * (rowM * 1) < 2 ^ kb := by decide +kernel
theorem neg_0_T : termOK2 nfTree T0 ⟨1, false, diagSP (law 0 0), oneSP⟩ = true := by decide +kernel
theorem neg_0_W : (diagSP (law 0 0)).wf = true := by decide +kernel
theorem neg_0_D : diagOK (law 0 0) = true := by decide +kernel

theorem neg_1_O : (evalO2 nfTree T0 [⟨1, false, diagSP (law 0 1), oneSP⟩]).allZero = true := by decide +kernel
theorem neg_1_B : wsum [⟨1, false, diagSP (law 0 1), oneSP⟩] * (rowM * 1) < 2 ^ kb := by decide +kernel
theorem neg_1_T : termOK2 nfTree T0 ⟨1, false, diagSP (law 0 1), oneSP⟩ = true := by decide +kernel
theorem neg_1_W : (diagSP (law 0 1)).wf = true := by decide +kernel
theorem neg_1_D : diagOK (law 0 1) = true := by decide +kernel

theorem neg_2_O : (evalO2 nfTree T0 [⟨1, false, diagSP (law 0 2), oneSP⟩]).allZero = true := by decide +kernel
theorem neg_2_B : wsum [⟨1, false, diagSP (law 0 2), oneSP⟩] * (rowM * 1) < 2 ^ kb := by decide +kernel
theorem neg_2_T : termOK2 nfTree T0 ⟨1, false, diagSP (law 0 2), oneSP⟩ = true := by decide +kernel
theorem neg_2_W : (diagSP (law 0 2)).wf = true := by decide +kernel
theorem neg_2_D : diagOK (law 0 2) = true := by decide +kernel

theorem neg_3_O : (evalO2 nfTree T0 [⟨1, false, diagSP (law 0 3), oneSP⟩]).allZero = true := by decide +kernel
theorem neg_3_B : wsum [⟨1, false, diagSP (law 0 3), oneSP⟩] * (rowM * 1) < 2 ^ kb := by decide +kernel
theorem neg_3_T : termOK2 nfTree T0 ⟨1, false, diagSP (law 0 3), oneSP⟩ = true := by decide +kernel
theorem neg_3_W : (diagSP (law 0 3)).wf = true := by decide +kernel
theorem neg_3_D : diagOK (law 0 3) = true := by decide +kernel

theorem neg_5_O : (evalO2 nfTree T0 [⟨1, false, diagSP (law 0 5), oneSP⟩]).allZero = true := by decide +kernel
theorem neg_5_B : wsum [⟨1, false, diagSP (law 0 5), oneSP⟩] * (rowM * 1) < 2 ^ kb := by decide +kernel
theorem neg_5_T : termOK2 nfTree T0 ⟨1, false, diagSP (law 0 5), oneSP⟩ = true := by decide +kernel
theorem neg_5_W : (diagSP (law 0 5)).wf = true := by decide +kernel
theorem neg_5_D : diagOK (law 0 5) = true := by decide +kernel

theorem neg_6_O : (evalO2 nfTree T0 [⟨1, false, diagSP (law 0 6), oneSP⟩]).allZero = true := by decide +kernel
theorem neg_6_B : wsum [⟨1, false, diagSP (law 0 6), oneSP⟩] * (rowM * 1) < 2 ^ kb := by decide +kernel
theorem neg_6_T : termOK2 nfTree T0 ⟨1, false, diagSP (law 0 6), oneSP⟩ = true := by decide +kernel
theorem neg_6_W : (diagSP (law 0 6)).wf = true := by decide +kernel
theorem neg_6_D : diagOK (law 0 6) = true := by decide +kernel

theorem neg_7_O : (evalO2 nfTree T0 [⟨1, false, diagSP (law 0 7), oneSP⟩]).allZero = true := by decide +kernel
theorem neg_7_B : wsum [⟨1, false, diagSP (law 0 7), oneSP⟩] * (rowM * 1) < 2 ^ kb := by decide +kernel
theorem neg_7_T : termOK2 nfTree T0 ⟨1, false, diagSP (law 0 7), oneSP⟩ = true := by decide +kernel
theorem neg_7_W : (diagSP (law 0 7)).wf = true := by decide +kernel
theorem neg_7_D : diagOK (law 0 7) = true := by decide +kernel

theorem neg_8_O : (evalO2 nfTree T0 [⟨1, false, diagSP (law 0 8), oneSP⟩]).allZero = true := by decide +kernel
theorem neg_8_B : wsum [⟨1, false, diagSP (law 0 8), oneSP⟩] * (rowM * 1) < 2 ^ kb := by decide +kernel
theorem neg_8_T : termOK2 nfTree T0 ⟨1, false, diagSP (law 0 8), oneSP⟩ = true := by decide +kernel
theorem neg_8_W : (diagSP (law 0 8)).wf = true := by decide +kernel
theorem neg_8_D : diagOK (law 0 8) = true := by decide +kernel

end LSG.Jac.Cert
