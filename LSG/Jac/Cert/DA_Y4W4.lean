import LSG.Jac.Data.Laws
import LSG.Jac.Data.IdTab
import LSG.Jac.Data.E1
import LSG.Jac.CheckerDeriv
import LSG.Jac.CheckerDiag

/-! GENERATED — exact checks `DA_Y4W4_j_l = Σ_i WY4_j_i · dYsp i (law l 4)`. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

noncomputable def da_Y4W4_0_0 : List Term := [⟨1, false, WY4_0_0, dYsp 0 (law 0 4)⟩, ⟨1, false, WY4_0_1, dYsp 1 (law 0 4)⟩, ⟨1, false, WY4_0_2, dYsp 2 (law 0 4)⟩, ⟨1, false, WY4_0_3, dYsp 3 (law 0 4)⟩, ⟨1, false, WY4_0_5, dYsp 5 (law 0 4)⟩, ⟨1, false, WY4_0_6, dYsp 6 (law 0 4)⟩, ⟨1, false, WY4_0_7, dYsp 7 (law 0 4)⟩, ⟨1, false, WY4_0_8, dYsp 8 (law 0 4)⟩, ⟨1, true, DA_Y4W4_0_0, oneSP⟩]
theorem da_Y4W4_0_0_O : (evalO2 idTree2 idTree3 da_Y4W4_0_0).allZero = true := by decide +kernel
theorem da_Y4W4_0_0_B : wsum da_Y4W4_0_0 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_0_0_T : da_Y4W4_0_0.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_0_1 : List Term := [⟨1, false, WY4_0_0, dYsp 0 (law 1 4)⟩, ⟨1, false, WY4_0_1, dYsp 1 (law 1 4)⟩, ⟨1, false, WY4_0_2, dYsp 2 (law 1 4)⟩, ⟨1, false, WY4_0_3, dYsp 3 (law 1 4)⟩, ⟨1, false, WY4_0_5, dYsp 5 (law 1 4)⟩, ⟨1, false, WY4_0_6, dYsp 6 (law 1 4)⟩, ⟨1, false, WY4_0_7, dYsp 7 (law 1 4)⟩, ⟨1, false, WY4_0_8, dYsp 8 (law 1 4)⟩, ⟨1, true, DA_Y4W4_0_1, oneSP⟩]
theorem da_Y4W4_0_1_O : (evalO2 idTree2 idTree3 da_Y4W4_0_1).allZero = true := by decide +kernel
theorem da_Y4W4_0_1_B : wsum da_Y4W4_0_1 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_0_1_T : da_Y4W4_0_1.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_0_2 : List Term := [⟨1, false, WY4_0_0, dYsp 0 (law 2 4)⟩, ⟨1, false, WY4_0_1, dYsp 1 (law 2 4)⟩, ⟨1, false, WY4_0_2, dYsp 2 (law 2 4)⟩, ⟨1, false, WY4_0_3, dYsp 3 (law 2 4)⟩, ⟨1, false, WY4_0_5, dYsp 5 (law 2 4)⟩, ⟨1, false, WY4_0_6, dYsp 6 (law 2 4)⟩, ⟨1, false, WY4_0_7, dYsp 7 (law 2 4)⟩, ⟨1, false, WY4_0_8, dYsp 8 (law 2 4)⟩, ⟨1, true, DA_Y4W4_0_2, oneSP⟩]
theorem da_Y4W4_0_2_O : (evalO2 idTree2 idTree3 da_Y4W4_0_2).allZero = true := by decide +kernel
theorem da_Y4W4_0_2_B : wsum da_Y4W4_0_2 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_0_2_T : da_Y4W4_0_2.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_0_3 : List Term := [⟨1, false, WY4_0_0, dYsp 0 (law 3 4)⟩, ⟨1, false, WY4_0_1, dYsp 1 (law 3 4)⟩, ⟨1, false, WY4_0_2, dYsp 2 (law 3 4)⟩, ⟨1, false, WY4_0_3, dYsp 3 (law 3 4)⟩, ⟨1, false, WY4_0_5, dYsp 5 (law 3 4)⟩, ⟨1, false, WY4_0_6, dYsp 6 (law 3 4)⟩, ⟨1, false, WY4_0_7, dYsp 7 (law 3 4)⟩, ⟨1, false, WY4_0_8, dYsp 8 (law 3 4)⟩, ⟨1, true, DA_Y4W4_0_3, oneSP⟩]
theorem da_Y4W4_0_3_O : (evalO2 idTree2 idTree3 da_Y4W4_0_3).allZero = true := by decide +kernel
theorem da_Y4W4_0_3_B : wsum da_Y4W4_0_3 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_0_3_T : da_Y4W4_0_3.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_0_4 : List Term := [⟨1, false, WY4_0_0, dYsp 0 (law 4 4)⟩, ⟨1, false, WY4_0_1, dYsp 1 (law 4 4)⟩, ⟨1, false, WY4_0_2, dYsp 2 (law 4 4)⟩, ⟨1, false, WY4_0_3, dYsp 3 (law 4 4)⟩, ⟨1, false, WY4_0_5, dYsp 5 (law 4 4)⟩, ⟨1, false, WY4_0_6, dYsp 6 (law 4 4)⟩, ⟨1, false, WY4_0_7, dYsp 7 (law 4 4)⟩, ⟨1, false, WY4_0_8, dYsp 8 (law 4 4)⟩, ⟨1, true, DA_Y4W4_0_4, oneSP⟩]
theorem da_Y4W4_0_4_O : (evalO2 idTree2 idTree3 da_Y4W4_0_4).allZero = true := by decide +kernel
theorem da_Y4W4_0_4_B : wsum da_Y4W4_0_4 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_0_4_T : da_Y4W4_0_4.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_0_5 : List Term := [⟨1, false, WY4_0_0, dYsp 0 (law 5 4)⟩, ⟨1, false, WY4_0_1, dYsp 1 (law 5 4)⟩, ⟨1, false, WY4_0_2, dYsp 2 (law 5 4)⟩, ⟨1, false, WY4_0_3, dYsp 3 (law 5 4)⟩, ⟨1, false, WY4_0_5, dYsp 5 (law 5 4)⟩, ⟨1, false, WY4_0_6, dYsp 6 (law 5 4)⟩, ⟨1, false, WY4_0_7, dYsp 7 (law 5 4)⟩, ⟨1, false, WY4_0_8, dYsp 8 (law 5 4)⟩, ⟨1, true, DA_Y4W4_0_5, oneSP⟩]
theorem da_Y4W4_0_5_O : (evalO2 idTree2 idTree3 da_Y4W4_0_5).allZero = true := by decide +kernel
theorem da_Y4W4_0_5_B : wsum da_Y4W4_0_5 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_0_5_T : da_Y4W4_0_5.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_0_6 : List Term := [⟨1, false, WY4_0_0, dYsp 0 (law 6 4)⟩, ⟨1, false, WY4_0_1, dYsp 1 (law 6 4)⟩, ⟨1, false, WY4_0_2, dYsp 2 (law 6 4)⟩, ⟨1, false, WY4_0_3, dYsp 3 (law 6 4)⟩, ⟨1, false, WY4_0_5, dYsp 5 (law 6 4)⟩, ⟨1, false, WY4_0_6, dYsp 6 (law 6 4)⟩, ⟨1, false, WY4_0_7, dYsp 7 (law 6 4)⟩, ⟨1, false, WY4_0_8, dYsp 8 (law 6 4)⟩, ⟨1, true, DA_Y4W4_0_6, oneSP⟩]
theorem da_Y4W4_0_6_O : (evalO2 idTree2 idTree3 da_Y4W4_0_6).allZero = true := by decide +kernel
theorem da_Y4W4_0_6_B : wsum da_Y4W4_0_6 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_0_6_T : da_Y4W4_0_6.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_0_7 : List Term := [⟨1, false, WY4_0_0, dYsp 0 (law 7 4)⟩, ⟨1, false, WY4_0_1, dYsp 1 (law 7 4)⟩, ⟨1, false, WY4_0_2, dYsp 2 (law 7 4)⟩, ⟨1, false, WY4_0_3, dYsp 3 (law 7 4)⟩, ⟨1, false, WY4_0_5, dYsp 5 (law 7 4)⟩, ⟨1, false, WY4_0_6, dYsp 6 (law 7 4)⟩, ⟨1, false, WY4_0_7, dYsp 7 (law 7 4)⟩, ⟨1, false, WY4_0_8, dYsp 8 (law 7 4)⟩, ⟨1, true, DA_Y4W4_0_7, oneSP⟩]
theorem da_Y4W4_0_7_O : (evalO2 idTree2 idTree3 da_Y4W4_0_7).allZero = true := by decide +kernel
theorem da_Y4W4_0_7_B : wsum da_Y4W4_0_7 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_0_7_T : da_Y4W4_0_7.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_0_8 : List Term := [⟨1, false, WY4_0_0, dYsp 0 (law 8 4)⟩, ⟨1, false, WY4_0_1, dYsp 1 (law 8 4)⟩, ⟨1, false, WY4_0_2, dYsp 2 (law 8 4)⟩, ⟨1, false, WY4_0_3, dYsp 3 (law 8 4)⟩, ⟨1, false, WY4_0_5, dYsp 5 (law 8 4)⟩, ⟨1, false, WY4_0_6, dYsp 6 (law 8 4)⟩, ⟨1, false, WY4_0_7, dYsp 7 (law 8 4)⟩, ⟨1, false, WY4_0_8, dYsp 8 (law 8 4)⟩, ⟨1, true, DA_Y4W4_0_8, oneSP⟩]
theorem da_Y4W4_0_8_O : (evalO2 idTree2 idTree3 da_Y4W4_0_8).allZero = true := by decide +kernel
theorem da_Y4W4_0_8_B : wsum da_Y4W4_0_8 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_0_8_T : da_Y4W4_0_8.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_1_0 : List Term := [⟨1, false, WY4_1_0, dYsp 0 (law 0 4)⟩, ⟨1, false, WY4_1_1, dYsp 1 (law 0 4)⟩, ⟨1, false, WY4_1_2, dYsp 2 (law 0 4)⟩, ⟨1, false, WY4_1_3, dYsp 3 (law 0 4)⟩, ⟨1, false, WY4_1_5, dYsp 5 (law 0 4)⟩, ⟨1, false, WY4_1_6, dYsp 6 (law 0 4)⟩, ⟨1, false, WY4_1_7, dYsp 7 (law 0 4)⟩, ⟨1, false, WY4_1_8, dYsp 8 (law 0 4)⟩, ⟨1, true, DA_Y4W4_1_0, oneSP⟩]
theorem da_Y4W4_1_0_O : (evalO2 idTree2 idTree3 da_Y4W4_1_0).allZero = true := by decide +kernel
theorem da_Y4W4_1_0_B : wsum da_Y4W4_1_0 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_1_0_T : da_Y4W4_1_0.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_1_1 : List Term := [⟨1, false, WY4_1_0, dYsp 0 (law 1 4)⟩, ⟨1, false, WY4_1_1, dYsp 1 (law 1 4)⟩, ⟨1, false, WY4_1_2, dYsp 2 (law 1 4)⟩, ⟨1, false, WY4_1_3, dYsp 3 (law 1 4)⟩, ⟨1, false, WY4_1_5, dYsp 5 (law 1 4)⟩, ⟨1, false, WY4_1_6, dYsp 6 (law 1 4)⟩, ⟨1, false, WY4_1_7, dYsp 7 (law 1 4)⟩, ⟨1, false, WY4_1_8, dYsp 8 (law 1 4)⟩, ⟨1, true, DA_Y4W4_1_1, oneSP⟩]
theorem da_Y4W4_1_1_O : (evalO2 idTree2 idTree3 da_Y4W4_1_1).allZero = true := by decide +kernel
theorem da_Y4W4_1_1_B : wsum da_Y4W4_1_1 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_1_1_T : da_Y4W4_1_1.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_1_2 : List Term := [⟨1, false, WY4_1_0, dYsp 0 (law 2 4)⟩, ⟨1, false, WY4_1_1, dYsp 1 (law 2 4)⟩, ⟨1, false, WY4_1_2, dYsp 2 (law 2 4)⟩, ⟨1, false, WY4_1_3, dYsp 3 (law 2 4)⟩, ⟨1, false, WY4_1_5, dYsp 5 (law 2 4)⟩, ⟨1, false, WY4_1_6, dYsp 6 (law 2 4)⟩, ⟨1, false, WY4_1_7, dYsp 7 (law 2 4)⟩, ⟨1, false, WY4_1_8, dYsp 8 (law 2 4)⟩, ⟨1, true, DA_Y4W4_1_2, oneSP⟩]
theorem da_Y4W4_1_2_O : (evalO2 idTree2 idTree3 da_Y4W4_1_2).allZero = true := by decide +kernel
theorem da_Y4W4_1_2_B : wsum da_Y4W4_1_2 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_1_2_T : da_Y4W4_1_2.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_1_3 : List Term := [⟨1, false, WY4_1_0, dYsp 0 (law 3 4)⟩, ⟨1, false, WY4_1_1, dYsp 1 (law 3 4)⟩, ⟨1, false, WY4_1_2, dYsp 2 (law 3 4)⟩, ⟨1, false, WY4_1_3, dYsp 3 (law 3 4)⟩, ⟨1, false, WY4_1_5, dYsp 5 (law 3 4)⟩, ⟨1, false, WY4_1_6, dYsp 6 (law 3 4)⟩, ⟨1, false, WY4_1_7, dYsp 7 (law 3 4)⟩, ⟨1, false, WY4_1_8, dYsp 8 (law 3 4)⟩, ⟨1, true, DA_Y4W4_1_3, oneSP⟩]
theorem da_Y4W4_1_3_O : (evalO2 idTree2 idTree3 da_Y4W4_1_3).allZero = true := by decide +kernel
theorem da_Y4W4_1_3_B : wsum da_Y4W4_1_3 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_1_3_T : da_Y4W4_1_3.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_1_4 : List Term := [⟨1, false, WY4_1_0, dYsp 0 (law 4 4)⟩, ⟨1, false, WY4_1_1, dYsp 1 (law 4 4)⟩, ⟨1, false, WY4_1_2, dYsp 2 (law 4 4)⟩, ⟨1, false, WY4_1_3, dYsp 3 (law 4 4)⟩, ⟨1, false, WY4_1_5, dYsp 5 (law 4 4)⟩, ⟨1, false, WY4_1_6, dYsp 6 (law 4 4)⟩, ⟨1, false, WY4_1_7, dYsp 7 (law 4 4)⟩, ⟨1, false, WY4_1_8, dYsp 8 (law 4 4)⟩, ⟨1, true, DA_Y4W4_1_4, oneSP⟩]
theorem da_Y4W4_1_4_O : (evalO2 idTree2 idTree3 da_Y4W4_1_4).allZero = true := by decide +kernel
theorem da_Y4W4_1_4_B : wsum da_Y4W4_1_4 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_1_4_T : da_Y4W4_1_4.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_1_5 : List Term := [⟨1, false, WY4_1_0, dYsp 0 (law 5 4)⟩, ⟨1, false, WY4_1_1, dYsp 1 (law 5 4)⟩, ⟨1, false, WY4_1_2, dYsp 2 (law 5 4)⟩, ⟨1, false, WY4_1_3, dYsp 3 (law 5 4)⟩, ⟨1, false, WY4_1_5, dYsp 5 (law 5 4)⟩, ⟨1, false, WY4_1_6, dYsp 6 (law 5 4)⟩, ⟨1, false, WY4_1_7, dYsp 7 (law 5 4)⟩, ⟨1, false, WY4_1_8, dYsp 8 (law 5 4)⟩, ⟨1, true, DA_Y4W4_1_5, oneSP⟩]
theorem da_Y4W4_1_5_O : (evalO2 idTree2 idTree3 da_Y4W4_1_5).allZero = true := by decide +kernel
theorem da_Y4W4_1_5_B : wsum da_Y4W4_1_5 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_1_5_T : da_Y4W4_1_5.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_1_6 : List Term := [⟨1, false, WY4_1_0, dYsp 0 (law 6 4)⟩, ⟨1, false, WY4_1_1, dYsp 1 (law 6 4)⟩, ⟨1, false, WY4_1_2, dYsp 2 (law 6 4)⟩, ⟨1, false, WY4_1_3, dYsp 3 (law 6 4)⟩, ⟨1, false, WY4_1_5, dYsp 5 (law 6 4)⟩, ⟨1, false, WY4_1_6, dYsp 6 (law 6 4)⟩, ⟨1, false, WY4_1_7, dYsp 7 (law 6 4)⟩, ⟨1, false, WY4_1_8, dYsp 8 (law 6 4)⟩, ⟨1, true, DA_Y4W4_1_6, oneSP⟩]
theorem da_Y4W4_1_6_O : (evalO2 idTree2 idTree3 da_Y4W4_1_6).allZero = true := by decide +kernel
theorem da_Y4W4_1_6_B : wsum da_Y4W4_1_6 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_1_6_T : da_Y4W4_1_6.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_1_7 : List Term := [⟨1, false, WY4_1_0, dYsp 0 (law 7 4)⟩, ⟨1, false, WY4_1_1, dYsp 1 (law 7 4)⟩, ⟨1, false, WY4_1_2, dYsp 2 (law 7 4)⟩, ⟨1, false, WY4_1_3, dYsp 3 (law 7 4)⟩, ⟨1, false, WY4_1_5, dYsp 5 (law 7 4)⟩, ⟨1, false, WY4_1_6, dYsp 6 (law 7 4)⟩, ⟨1, false, WY4_1_7, dYsp 7 (law 7 4)⟩, ⟨1, false, WY4_1_8, dYsp 8 (law 7 4)⟩, ⟨1, true, DA_Y4W4_1_7, oneSP⟩]
theorem da_Y4W4_1_7_O : (evalO2 idTree2 idTree3 da_Y4W4_1_7).allZero = true := by decide +kernel
theorem da_Y4W4_1_7_B : wsum da_Y4W4_1_7 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_1_7_T : da_Y4W4_1_7.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_Y4W4_1_8 : List Term := [⟨1, false, WY4_1_0, dYsp 0 (law 8 4)⟩, ⟨1, false, WY4_1_1, dYsp 1 (law 8 4)⟩, ⟨1, false, WY4_1_2, dYsp 2 (law 8 4)⟩, ⟨1, false, WY4_1_3, dYsp 3 (law 8 4)⟩, ⟨1, false, WY4_1_5, dYsp 5 (law 8 4)⟩, ⟨1, false, WY4_1_6, dYsp 6 (law 8 4)⟩, ⟨1, false, WY4_1_7, dYsp 7 (law 8 4)⟩, ⟨1, false, WY4_1_8, dYsp 8 (law 8 4)⟩, ⟨1, true, DA_Y4W4_1_8, oneSP⟩]
theorem da_Y4W4_1_8_O : (evalO2 idTree2 idTree3 da_Y4W4_1_8).allZero = true := by decide +kernel
theorem da_Y4W4_1_8_B : wsum da_Y4W4_1_8 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_Y4W4_1_8_T : da_Y4W4_1_8.all (fun q => termOK2 idTree2 idTree3 q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
