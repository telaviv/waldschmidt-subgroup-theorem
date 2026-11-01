import LSG.Jac.Data.Laws
import LSG.Jac.Data.IdTab
import LSG.Jac.Data.E1
import LSG.Jac.CheckerDeriv
import LSG.Jac.CheckerDiag

/-! GENERATED — exact checks `DA_X0W_j_l = Σ_i WX0_j_i · dXsp i (law l 0)`. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

noncomputable def da_X0W_0_0 : List Term := [⟨1, false, WX0_0_1, dXsp 1 (law 0 0)⟩, ⟨1, false, WX0_0_2, dXsp 2 (law 0 0)⟩, ⟨1, false, WX0_0_3, dXsp 3 (law 0 0)⟩, ⟨1, false, WX0_0_4, dXsp 4 (law 0 0)⟩, ⟨1, false, WX0_0_5, dXsp 5 (law 0 0)⟩, ⟨1, false, WX0_0_6, dXsp 6 (law 0 0)⟩, ⟨1, false, WX0_0_7, dXsp 7 (law 0 0)⟩, ⟨1, false, WX0_0_8, dXsp 8 (law 0 0)⟩, ⟨1, true, DA_X0W_0_0, oneSP⟩]
theorem da_X0W_0_0_O : (evalO2 idTree3 idTree2 da_X0W_0_0).allZero = true := by decide +kernel
theorem da_X0W_0_0_B : wsum da_X0W_0_0 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_0_0_T : da_X0W_0_0.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_0_1 : List Term := [⟨1, false, WX0_0_1, dXsp 1 (law 1 0)⟩, ⟨1, false, WX0_0_2, dXsp 2 (law 1 0)⟩, ⟨1, false, WX0_0_3, dXsp 3 (law 1 0)⟩, ⟨1, false, WX0_0_4, dXsp 4 (law 1 0)⟩, ⟨1, false, WX0_0_5, dXsp 5 (law 1 0)⟩, ⟨1, false, WX0_0_6, dXsp 6 (law 1 0)⟩, ⟨1, false, WX0_0_7, dXsp 7 (law 1 0)⟩, ⟨1, false, WX0_0_8, dXsp 8 (law 1 0)⟩, ⟨1, true, DA_X0W_0_1, oneSP⟩]
theorem da_X0W_0_1_O : (evalO2 idTree3 idTree2 da_X0W_0_1).allZero = true := by decide +kernel
theorem da_X0W_0_1_B : wsum da_X0W_0_1 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_0_1_T : da_X0W_0_1.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_0_2 : List Term := [⟨1, false, WX0_0_1, dXsp 1 (law 2 0)⟩, ⟨1, false, WX0_0_2, dXsp 2 (law 2 0)⟩, ⟨1, false, WX0_0_3, dXsp 3 (law 2 0)⟩, ⟨1, false, WX0_0_4, dXsp 4 (law 2 0)⟩, ⟨1, false, WX0_0_5, dXsp 5 (law 2 0)⟩, ⟨1, false, WX0_0_6, dXsp 6 (law 2 0)⟩, ⟨1, false, WX0_0_7, dXsp 7 (law 2 0)⟩, ⟨1, false, WX0_0_8, dXsp 8 (law 2 0)⟩, ⟨1, true, DA_X0W_0_2, oneSP⟩]
theorem da_X0W_0_2_O : (evalO2 idTree3 idTree2 da_X0W_0_2).allZero = true := by decide +kernel
theorem da_X0W_0_2_B : wsum da_X0W_0_2 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_0_2_T : da_X0W_0_2.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_0_3 : List Term := [⟨1, false, WX0_0_1, dXsp 1 (law 3 0)⟩, ⟨1, false, WX0_0_2, dXsp 2 (law 3 0)⟩, ⟨1, false, WX0_0_3, dXsp 3 (law 3 0)⟩, ⟨1, false, WX0_0_4, dXsp 4 (law 3 0)⟩, ⟨1, false, WX0_0_5, dXsp 5 (law 3 0)⟩, ⟨1, false, WX0_0_6, dXsp 6 (law 3 0)⟩, ⟨1, false, WX0_0_7, dXsp 7 (law 3 0)⟩, ⟨1, false, WX0_0_8, dXsp 8 (law 3 0)⟩, ⟨1, true, DA_X0W_0_3, oneSP⟩]
theorem da_X0W_0_3_O : (evalO2 idTree3 idTree2 da_X0W_0_3).allZero = true := by decide +kernel
theorem da_X0W_0_3_B : wsum da_X0W_0_3 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_0_3_T : da_X0W_0_3.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_0_4 : List Term := [⟨1, false, WX0_0_1, dXsp 1 (law 4 0)⟩, ⟨1, false, WX0_0_2, dXsp 2 (law 4 0)⟩, ⟨1, false, WX0_0_3, dXsp 3 (law 4 0)⟩, ⟨1, false, WX0_0_4, dXsp 4 (law 4 0)⟩, ⟨1, false, WX0_0_5, dXsp 5 (law 4 0)⟩, ⟨1, false, WX0_0_6, dXsp 6 (law 4 0)⟩, ⟨1, false, WX0_0_7, dXsp 7 (law 4 0)⟩, ⟨1, false, WX0_0_8, dXsp 8 (law 4 0)⟩, ⟨1, true, DA_X0W_0_4, oneSP⟩]
theorem da_X0W_0_4_O : (evalO2 idTree3 idTree2 da_X0W_0_4).allZero = true := by decide +kernel
theorem da_X0W_0_4_B : wsum da_X0W_0_4 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_0_4_T : da_X0W_0_4.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_0_5 : List Term := [⟨1, false, WX0_0_1, dXsp 1 (law 5 0)⟩, ⟨1, false, WX0_0_2, dXsp 2 (law 5 0)⟩, ⟨1, false, WX0_0_3, dXsp 3 (law 5 0)⟩, ⟨1, false, WX0_0_4, dXsp 4 (law 5 0)⟩, ⟨1, false, WX0_0_5, dXsp 5 (law 5 0)⟩, ⟨1, false, WX0_0_6, dXsp 6 (law 5 0)⟩, ⟨1, false, WX0_0_7, dXsp 7 (law 5 0)⟩, ⟨1, false, WX0_0_8, dXsp 8 (law 5 0)⟩, ⟨1, true, DA_X0W_0_5, oneSP⟩]
theorem da_X0W_0_5_O : (evalO2 idTree3 idTree2 da_X0W_0_5).allZero = true := by decide +kernel
theorem da_X0W_0_5_B : wsum da_X0W_0_5 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_0_5_T : da_X0W_0_5.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_0_6 : List Term := [⟨1, false, WX0_0_1, dXsp 1 (law 6 0)⟩, ⟨1, false, WX0_0_2, dXsp 2 (law 6 0)⟩, ⟨1, false, WX0_0_3, dXsp 3 (law 6 0)⟩, ⟨1, false, WX0_0_4, dXsp 4 (law 6 0)⟩, ⟨1, false, WX0_0_5, dXsp 5 (law 6 0)⟩, ⟨1, false, WX0_0_6, dXsp 6 (law 6 0)⟩, ⟨1, false, WX0_0_7, dXsp 7 (law 6 0)⟩, ⟨1, false, WX0_0_8, dXsp 8 (law 6 0)⟩, ⟨1, true, DA_X0W_0_6, oneSP⟩]
theorem da_X0W_0_6_O : (evalO2 idTree3 idTree2 da_X0W_0_6).allZero = true := by decide +kernel
theorem da_X0W_0_6_B : wsum da_X0W_0_6 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_0_6_T : da_X0W_0_6.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_0_7 : List Term := [⟨1, false, WX0_0_1, dXsp 1 (law 7 0)⟩, ⟨1, false, WX0_0_2, dXsp 2 (law 7 0)⟩, ⟨1, false, WX0_0_3, dXsp 3 (law 7 0)⟩, ⟨1, false, WX0_0_4, dXsp 4 (law 7 0)⟩, ⟨1, false, WX0_0_5, dXsp 5 (law 7 0)⟩, ⟨1, false, WX0_0_6, dXsp 6 (law 7 0)⟩, ⟨1, false, WX0_0_7, dXsp 7 (law 7 0)⟩, ⟨1, false, WX0_0_8, dXsp 8 (law 7 0)⟩, ⟨1, true, DA_X0W_0_7, oneSP⟩]
theorem da_X0W_0_7_O : (evalO2 idTree3 idTree2 da_X0W_0_7).allZero = true := by decide +kernel
theorem da_X0W_0_7_B : wsum da_X0W_0_7 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_0_7_T : da_X0W_0_7.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_0_8 : List Term := [⟨1, false, WX0_0_1, dXsp 1 (law 8 0)⟩, ⟨1, false, WX0_0_2, dXsp 2 (law 8 0)⟩, ⟨1, false, WX0_0_3, dXsp 3 (law 8 0)⟩, ⟨1, false, WX0_0_4, dXsp 4 (law 8 0)⟩, ⟨1, false, WX0_0_5, dXsp 5 (law 8 0)⟩, ⟨1, false, WX0_0_6, dXsp 6 (law 8 0)⟩, ⟨1, false, WX0_0_7, dXsp 7 (law 8 0)⟩, ⟨1, false, WX0_0_8, dXsp 8 (law 8 0)⟩, ⟨1, true, DA_X0W_0_8, oneSP⟩]
theorem da_X0W_0_8_O : (evalO2 idTree3 idTree2 da_X0W_0_8).allZero = true := by decide +kernel
theorem da_X0W_0_8_B : wsum da_X0W_0_8 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_0_8_T : da_X0W_0_8.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_1_0 : List Term := [⟨1, false, WX0_1_1, dXsp 1 (law 0 0)⟩, ⟨1, false, WX0_1_2, dXsp 2 (law 0 0)⟩, ⟨1, false, WX0_1_3, dXsp 3 (law 0 0)⟩, ⟨1, false, WX0_1_4, dXsp 4 (law 0 0)⟩, ⟨1, false, WX0_1_5, dXsp 5 (law 0 0)⟩, ⟨1, false, WX0_1_6, dXsp 6 (law 0 0)⟩, ⟨1, false, WX0_1_7, dXsp 7 (law 0 0)⟩, ⟨1, false, WX0_1_8, dXsp 8 (law 0 0)⟩, ⟨1, true, DA_X0W_1_0, oneSP⟩]
theorem da_X0W_1_0_O : (evalO2 idTree3 idTree2 da_X0W_1_0).allZero = true := by decide +kernel
theorem da_X0W_1_0_B : wsum da_X0W_1_0 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_1_0_T : da_X0W_1_0.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_1_1 : List Term := [⟨1, false, WX0_1_1, dXsp 1 (law 1 0)⟩, ⟨1, false, WX0_1_2, dXsp 2 (law 1 0)⟩, ⟨1, false, WX0_1_3, dXsp 3 (law 1 0)⟩, ⟨1, false, WX0_1_4, dXsp 4 (law 1 0)⟩, ⟨1, false, WX0_1_5, dXsp 5 (law 1 0)⟩, ⟨1, false, WX0_1_6, dXsp 6 (law 1 0)⟩, ⟨1, false, WX0_1_7, dXsp 7 (law 1 0)⟩, ⟨1, false, WX0_1_8, dXsp 8 (law 1 0)⟩, ⟨1, true, DA_X0W_1_1, oneSP⟩]
theorem da_X0W_1_1_O : (evalO2 idTree3 idTree2 da_X0W_1_1).allZero = true := by decide +kernel
theorem da_X0W_1_1_B : wsum da_X0W_1_1 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_1_1_T : da_X0W_1_1.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_1_2 : List Term := [⟨1, false, WX0_1_1, dXsp 1 (law 2 0)⟩, ⟨1, false, WX0_1_2, dXsp 2 (law 2 0)⟩, ⟨1, false, WX0_1_3, dXsp 3 (law 2 0)⟩, ⟨1, false, WX0_1_4, dXsp 4 (law 2 0)⟩, ⟨1, false, WX0_1_5, dXsp 5 (law 2 0)⟩, ⟨1, false, WX0_1_6, dXsp 6 (law 2 0)⟩, ⟨1, false, WX0_1_7, dXsp 7 (law 2 0)⟩, ⟨1, false, WX0_1_8, dXsp 8 (law 2 0)⟩, ⟨1, true, DA_X0W_1_2, oneSP⟩]
theorem da_X0W_1_2_O : (evalO2 idTree3 idTree2 da_X0W_1_2).allZero = true := by decide +kernel
theorem da_X0W_1_2_B : wsum da_X0W_1_2 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_1_2_T : da_X0W_1_2.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_1_3 : List Term := [⟨1, false, WX0_1_1, dXsp 1 (law 3 0)⟩, ⟨1, false, WX0_1_2, dXsp 2 (law 3 0)⟩, ⟨1, false, WX0_1_3, dXsp 3 (law 3 0)⟩, ⟨1, false, WX0_1_4, dXsp 4 (law 3 0)⟩, ⟨1, false, WX0_1_5, dXsp 5 (law 3 0)⟩, ⟨1, false, WX0_1_6, dXsp 6 (law 3 0)⟩, ⟨1, false, WX0_1_7, dXsp 7 (law 3 0)⟩, ⟨1, false, WX0_1_8, dXsp 8 (law 3 0)⟩, ⟨1, true, DA_X0W_1_3, oneSP⟩]
theorem da_X0W_1_3_O : (evalO2 idTree3 idTree2 da_X0W_1_3).allZero = true := by decide +kernel
theorem da_X0W_1_3_B : wsum da_X0W_1_3 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_1_3_T : da_X0W_1_3.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_1_4 : List Term := [⟨1, false, WX0_1_1, dXsp 1 (law 4 0)⟩, ⟨1, false, WX0_1_2, dXsp 2 (law 4 0)⟩, ⟨1, false, WX0_1_3, dXsp 3 (law 4 0)⟩, ⟨1, false, WX0_1_4, dXsp 4 (law 4 0)⟩, ⟨1, false, WX0_1_5, dXsp 5 (law 4 0)⟩, ⟨1, false, WX0_1_6, dXsp 6 (law 4 0)⟩, ⟨1, false, WX0_1_7, dXsp 7 (law 4 0)⟩, ⟨1, false, WX0_1_8, dXsp 8 (law 4 0)⟩, ⟨1, true, DA_X0W_1_4, oneSP⟩]
theorem da_X0W_1_4_O : (evalO2 idTree3 idTree2 da_X0W_1_4).allZero = true := by decide +kernel
theorem da_X0W_1_4_B : wsum da_X0W_1_4 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_1_4_T : da_X0W_1_4.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_1_5 : List Term := [⟨1, false, WX0_1_1, dXsp 1 (law 5 0)⟩, ⟨1, false, WX0_1_2, dXsp 2 (law 5 0)⟩, ⟨1, false, WX0_1_3, dXsp 3 (law 5 0)⟩, ⟨1, false, WX0_1_4, dXsp 4 (law 5 0)⟩, ⟨1, false, WX0_1_5, dXsp 5 (law 5 0)⟩, ⟨1, false, WX0_1_6, dXsp 6 (law 5 0)⟩, ⟨1, false, WX0_1_7, dXsp 7 (law 5 0)⟩, ⟨1, false, WX0_1_8, dXsp 8 (law 5 0)⟩, ⟨1, true, DA_X0W_1_5, oneSP⟩]
theorem da_X0W_1_5_O : (evalO2 idTree3 idTree2 da_X0W_1_5).allZero = true := by decide +kernel
theorem da_X0W_1_5_B : wsum da_X0W_1_5 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_1_5_T : da_X0W_1_5.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_1_6 : List Term := [⟨1, false, WX0_1_1, dXsp 1 (law 6 0)⟩, ⟨1, false, WX0_1_2, dXsp 2 (law 6 0)⟩, ⟨1, false, WX0_1_3, dXsp 3 (law 6 0)⟩, ⟨1, false, WX0_1_4, dXsp 4 (law 6 0)⟩, ⟨1, false, WX0_1_5, dXsp 5 (law 6 0)⟩, ⟨1, false, WX0_1_6, dXsp 6 (law 6 0)⟩, ⟨1, false, WX0_1_7, dXsp 7 (law 6 0)⟩, ⟨1, false, WX0_1_8, dXsp 8 (law 6 0)⟩, ⟨1, true, DA_X0W_1_6, oneSP⟩]
theorem da_X0W_1_6_O : (evalO2 idTree3 idTree2 da_X0W_1_6).allZero = true := by decide +kernel
theorem da_X0W_1_6_B : wsum da_X0W_1_6 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_1_6_T : da_X0W_1_6.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_1_7 : List Term := [⟨1, false, WX0_1_1, dXsp 1 (law 7 0)⟩, ⟨1, false, WX0_1_2, dXsp 2 (law 7 0)⟩, ⟨1, false, WX0_1_3, dXsp 3 (law 7 0)⟩, ⟨1, false, WX0_1_4, dXsp 4 (law 7 0)⟩, ⟨1, false, WX0_1_5, dXsp 5 (law 7 0)⟩, ⟨1, false, WX0_1_6, dXsp 6 (law 7 0)⟩, ⟨1, false, WX0_1_7, dXsp 7 (law 7 0)⟩, ⟨1, false, WX0_1_8, dXsp 8 (law 7 0)⟩, ⟨1, true, DA_X0W_1_7, oneSP⟩]
theorem da_X0W_1_7_O : (evalO2 idTree3 idTree2 da_X0W_1_7).allZero = true := by decide +kernel
theorem da_X0W_1_7_B : wsum da_X0W_1_7 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_1_7_T : da_X0W_1_7.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

noncomputable def da_X0W_1_8 : List Term := [⟨1, false, WX0_1_1, dXsp 1 (law 8 0)⟩, ⟨1, false, WX0_1_2, dXsp 2 (law 8 0)⟩, ⟨1, false, WX0_1_3, dXsp 3 (law 8 0)⟩, ⟨1, false, WX0_1_4, dXsp 4 (law 8 0)⟩, ⟨1, false, WX0_1_5, dXsp 5 (law 8 0)⟩, ⟨1, false, WX0_1_6, dXsp 6 (law 8 0)⟩, ⟨1, false, WX0_1_7, dXsp 7 (law 8 0)⟩, ⟨1, false, WX0_1_8, dXsp 8 (law 8 0)⟩, ⟨1, true, DA_X0W_1_8, oneSP⟩]
theorem da_X0W_1_8_O : (evalO2 idTree3 idTree2 da_X0W_1_8).allZero = true := by decide +kernel
theorem da_X0W_1_8_B : wsum da_X0W_1_8 * (1 * 1) < 2 ^ kbId := by decide +kernel
theorem da_X0W_1_8_T : da_X0W_1_8.all (fun q => termOK2 idTree3 idTree2 q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
