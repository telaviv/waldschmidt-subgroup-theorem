import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table5
import LSG.Jac.Data.E1
import LSG.Jac.CheckerRange

/-! GENERATED — equivariance identities `F4Y` (law 4, `Y`-flow, output chart 4), j = 0, split by
`X`-slot ranges `rs_e1_F4Y_0_<l>` (adaptive, `scripts/jac/e1_cost.py`, budget 42000). -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

def rs_e1_F4Y_0_0 : List (Nat × Nat) := [(0, 24), (24, 37), (37, 51), (51, 69), (69, 90), (90, 103), (103, 114), (114, 126), (126, 144)]
noncomputable def e1_F4Y_0_0 : List Term := [⟨4, false, law 4 4, DA_Y4W4_0_0⟩, ⟨4, true, law 0 4, DA_Y4W4_0_4⟩, ⟨96, false, shiftY 4 (law 1 4), law 1 4⟩, ⟨48, true, shiftY 4 (law 0 4), law 3 4⟩]
theorem e1_F4Y_0_0_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 24)) nfTree5 e1_F4Y_0_0).allZero = true := by decide +kernel
theorem e1_F4Y_0_0_R1 : (evalO2 (nfTree.mapRows (rowsIn 24 37)) nfTree5 e1_F4Y_0_0).allZero = true := by decide +kernel
theorem e1_F4Y_0_0_R2 : (evalO2 (nfTree.mapRows (rowsIn 37 51)) nfTree5 e1_F4Y_0_0).allZero = true := by decide +kernel
theorem e1_F4Y_0_0_R3 : (evalO2 (nfTree.mapRows (rowsIn 51 69)) nfTree5 e1_F4Y_0_0).allZero = true := by decide +kernel
theorem e1_F4Y_0_0_R4 : (evalO2 (nfTree.mapRows (rowsIn 69 90)) nfTree5 e1_F4Y_0_0).allZero = true := by decide +kernel
theorem e1_F4Y_0_0_R5 : (evalO2 (nfTree.mapRows (rowsIn 90 103)) nfTree5 e1_F4Y_0_0).allZero = true := by decide +kernel
theorem e1_F4Y_0_0_R6 : (evalO2 (nfTree.mapRows (rowsIn 103 114)) nfTree5 e1_F4Y_0_0).allZero = true := by decide +kernel
theorem e1_F4Y_0_0_R7 : (evalO2 (nfTree.mapRows (rowsIn 114 126)) nfTree5 e1_F4Y_0_0).allZero = true := by decide +kernel
theorem e1_F4Y_0_0_R8 : (evalO2 (nfTree.mapRows (rowsIn 126 144)) nfTree5 e1_F4Y_0_0).allZero = true := by decide +kernel
theorem e1_F4Y_0_0_B : wsum e1_F4Y_0_0 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_0_0_T : e1_F4Y_0_0.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_0_1 : List (Nat × Nat) := [(0, 18), (18, 28), (28, 37), (37, 50), (50, 63), (63, 80), (80, 92), (92, 104), (104, 115), (115, 128), (128, 144)]
noncomputable def e1_F4Y_0_1 : List Term := [⟨4, false, law 4 4, DA_Y4W4_0_1⟩, ⟨4, true, law 1 4, DA_Y4W4_0_4⟩, ⟨24, false, shiftY 4 (law 1 4), law 3 4⟩, ⟨8, false, shiftY 4 (law 4 4), law 4 4⟩, ⟨24, true, shiftY 4 (law 0 4), law 8 4⟩]
theorem e1_F4Y_0_1_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 18)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R1 : (evalO2 (nfTree.mapRows (rowsIn 18 28)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R2 : (evalO2 (nfTree.mapRows (rowsIn 28 37)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R3 : (evalO2 (nfTree.mapRows (rowsIn 37 50)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R4 : (evalO2 (nfTree.mapRows (rowsIn 50 63)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R5 : (evalO2 (nfTree.mapRows (rowsIn 63 80)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R6 : (evalO2 (nfTree.mapRows (rowsIn 80 92)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R7 : (evalO2 (nfTree.mapRows (rowsIn 92 104)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R8 : (evalO2 (nfTree.mapRows (rowsIn 104 115)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R9 : (evalO2 (nfTree.mapRows (rowsIn 115 128)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_R10 : (evalO2 (nfTree.mapRows (rowsIn 128 144)) nfTree5 e1_F4Y_0_1).allZero = true := by decide +kernel
theorem e1_F4Y_0_1_B : wsum e1_F4Y_0_1 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_0_1_T : e1_F4Y_0_1.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_0_2 : List (Nat × Nat) := [(0, 16), (16, 28), (28, 37), (37, 49), (49, 62), (62, 80), (80, 92), (92, 103), (103, 112), (112, 122), (122, 139), (139, 144)]
noncomputable def e1_F4Y_0_2 : List Term := [⟨4, false, law 4 4, DA_Y4W4_0_2⟩, ⟨4, true, law 2 4, DA_Y4W4_0_4⟩, ⟨48, false, shiftY 4 (law 0 4), law 1 4⟩, ⟨24, true, shiftY 4 (law 2 4), law 3 4⟩, ⟨8, false, shiftY 4 (law 4 4), law 5 4⟩]
theorem e1_F4Y_0_2_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 16)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R1 : (evalO2 (nfTree.mapRows (rowsIn 16 28)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R2 : (evalO2 (nfTree.mapRows (rowsIn 28 37)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R3 : (evalO2 (nfTree.mapRows (rowsIn 37 49)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R4 : (evalO2 (nfTree.mapRows (rowsIn 49 62)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R5 : (evalO2 (nfTree.mapRows (rowsIn 62 80)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R6 : (evalO2 (nfTree.mapRows (rowsIn 80 92)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R7 : (evalO2 (nfTree.mapRows (rowsIn 92 103)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R8 : (evalO2 (nfTree.mapRows (rowsIn 103 112)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R9 : (evalO2 (nfTree.mapRows (rowsIn 112 122)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R10 : (evalO2 (nfTree.mapRows (rowsIn 122 139)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_R11 : (evalO2 (nfTree.mapRows (rowsIn 139 144)) nfTree5 e1_F4Y_0_2).allZero = true := by decide +kernel
theorem e1_F4Y_0_2_B : wsum e1_F4Y_0_2 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_0_2_T : e1_F4Y_0_2.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_0_3 : List (Nat × Nat) := [(0, 16), (16, 27), (27, 37), (37, 49), (49, 62), (62, 76), (76, 91), (91, 102), (102, 112), (112, 122), (122, 139), (139, 144)]
noncomputable def e1_F4Y_0_3 : List Term := [⟨4, false, law 4 4, DA_Y4W4_0_3⟩, ⟨4, true, law 3 4, DA_Y4W4_0_4⟩, ⟨24, false, shiftY 4 (law 0 4), law 2 4⟩, ⟨8, false, shiftY 4 (law 4 4), law 6 4⟩, ⟨48, true, shiftY 4 (law 1 4), law 8 4⟩]
theorem e1_F4Y_0_3_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 16)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R1 : (evalO2 (nfTree.mapRows (rowsIn 16 27)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R2 : (evalO2 (nfTree.mapRows (rowsIn 27 37)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R3 : (evalO2 (nfTree.mapRows (rowsIn 37 49)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R4 : (evalO2 (nfTree.mapRows (rowsIn 49 62)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R5 : (evalO2 (nfTree.mapRows (rowsIn 62 76)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R6 : (evalO2 (nfTree.mapRows (rowsIn 76 91)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R7 : (evalO2 (nfTree.mapRows (rowsIn 91 102)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R8 : (evalO2 (nfTree.mapRows (rowsIn 102 112)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R9 : (evalO2 (nfTree.mapRows (rowsIn 112 122)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R10 : (evalO2 (nfTree.mapRows (rowsIn 122 139)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_R11 : (evalO2 (nfTree.mapRows (rowsIn 139 144)) nfTree5 e1_F4Y_0_3).allZero = true := by decide +kernel
theorem e1_F4Y_0_3_B : wsum e1_F4Y_0_3 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_0_3_T : e1_F4Y_0_3.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_0_5 : List (Nat × Nat) := [(0, 16), (16, 27), (27, 36), (36, 48), (48, 55), (55, 69), (69, 81), (81, 92), (92, 103), (103, 112), (112, 122), (122, 136), (136, 144)]
noncomputable def e1_F4Y_0_5 : List Term := [⟨4, false, law 4 4, DA_Y4W4_0_5⟩, ⟨4, true, law 5 4, DA_Y4W4_0_4⟩, ⟨8, true, shiftY 4 (law 0 4), law 4 4⟩, ⟨24, true, shiftY 4 (law 2 4), law 6 4⟩, ⟨24, false, shiftY 4 (law 1 4), law 7 4⟩]
theorem e1_F4Y_0_5_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 16)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R1 : (evalO2 (nfTree.mapRows (rowsIn 16 27)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R2 : (evalO2 (nfTree.mapRows (rowsIn 27 36)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R3 : (evalO2 (nfTree.mapRows (rowsIn 36 48)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R4 : (evalO2 (nfTree.mapRows (rowsIn 48 55)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R5 : (evalO2 (nfTree.mapRows (rowsIn 55 69)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R6 : (evalO2 (nfTree.mapRows (rowsIn 69 81)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R7 : (evalO2 (nfTree.mapRows (rowsIn 81 92)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R8 : (evalO2 (nfTree.mapRows (rowsIn 92 103)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R9 : (evalO2 (nfTree.mapRows (rowsIn 103 112)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R10 : (evalO2 (nfTree.mapRows (rowsIn 112 122)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R11 : (evalO2 (nfTree.mapRows (rowsIn 122 136)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_R12 : (evalO2 (nfTree.mapRows (rowsIn 136 144)) nfTree5 e1_F4Y_0_5).allZero = true := by decide +kernel
theorem e1_F4Y_0_5_B : wsum e1_F4Y_0_5 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_0_5_T : e1_F4Y_0_5.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_0_6 : List (Nat × Nat) := [(0, 16), (16, 27), (27, 36), (36, 48), (48, 55), (55, 69), (69, 82), (82, 94), (94, 106), (106, 115), (115, 126), (126, 140), (140, 144)]
noncomputable def e1_F4Y_0_6 : List Term := [⟨4, false, law 4 4, DA_Y4W4_0_6⟩, ⟨4, true, law 6 4, DA_Y4W4_0_4⟩, ⟨48, false, shiftY 4 (law 0 4), law 5 4⟩, ⟨24, true, shiftY 4 (law 2 4), law 7 4⟩, ⟨16, true, shiftY 4 (law 4 4), law 8 4⟩]
theorem e1_F4Y_0_6_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 16)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R1 : (evalO2 (nfTree.mapRows (rowsIn 16 27)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R2 : (evalO2 (nfTree.mapRows (rowsIn 27 36)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R3 : (evalO2 (nfTree.mapRows (rowsIn 36 48)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R4 : (evalO2 (nfTree.mapRows (rowsIn 48 55)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R5 : (evalO2 (nfTree.mapRows (rowsIn 55 69)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R6 : (evalO2 (nfTree.mapRows (rowsIn 69 82)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R7 : (evalO2 (nfTree.mapRows (rowsIn 82 94)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R8 : (evalO2 (nfTree.mapRows (rowsIn 94 106)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R9 : (evalO2 (nfTree.mapRows (rowsIn 106 115)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R10 : (evalO2 (nfTree.mapRows (rowsIn 115 126)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R11 : (evalO2 (nfTree.mapRows (rowsIn 126 140)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_R12 : (evalO2 (nfTree.mapRows (rowsIn 140 144)) nfTree5 e1_F4Y_0_6).allZero = true := by decide +kernel
theorem e1_F4Y_0_6_B : wsum e1_F4Y_0_6 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_0_6_T : e1_F4Y_0_6.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_0_7 : List (Nat × Nat) := [(0, 16), (16, 27), (27, 36), (36, 48), (48, 55), (55, 69), (69, 81), (81, 92), (92, 103), (103, 112), (112, 122), (122, 136), (136, 144)]
noncomputable def e1_F4Y_0_7 : List Term := [⟨4, false, law 4 4, DA_Y4W4_0_7⟩, ⟨4, true, law 7 4, DA_Y4W4_0_4⟩, ⟨64, true, shiftY 4 (law 1 4), law 4 4⟩, ⟨24, false, shiftY 4 (law 3 4), law 7 4⟩, ⟨48, true, shiftY 4 (law 5 4), law 8 4⟩]
theorem e1_F4Y_0_7_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 16)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R1 : (evalO2 (nfTree.mapRows (rowsIn 16 27)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R2 : (evalO2 (nfTree.mapRows (rowsIn 27 36)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R3 : (evalO2 (nfTree.mapRows (rowsIn 36 48)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R4 : (evalO2 (nfTree.mapRows (rowsIn 48 55)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R5 : (evalO2 (nfTree.mapRows (rowsIn 55 69)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R6 : (evalO2 (nfTree.mapRows (rowsIn 69 81)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R7 : (evalO2 (nfTree.mapRows (rowsIn 81 92)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R8 : (evalO2 (nfTree.mapRows (rowsIn 92 103)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R9 : (evalO2 (nfTree.mapRows (rowsIn 103 112)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R10 : (evalO2 (nfTree.mapRows (rowsIn 112 122)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R11 : (evalO2 (nfTree.mapRows (rowsIn 122 136)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_R12 : (evalO2 (nfTree.mapRows (rowsIn 136 144)) nfTree5 e1_F4Y_0_7).allZero = true := by decide +kernel
theorem e1_F4Y_0_7_B : wsum e1_F4Y_0_7 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_0_7_T : e1_F4Y_0_7.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_0_8 : List (Nat × Nat) := [(0, 16), (16, 27), (27, 36), (36, 48), (48, 55), (55, 68), (68, 81), (81, 92), (92, 102), (102, 112), (112, 122), (122, 136), (136, 144)]
noncomputable def e1_F4Y_0_8 : List Term := [⟨4, false, law 4 4, DA_Y4W4_0_8⟩, ⟨4, true, law 8 4, DA_Y4W4_0_4⟩, ⟨96, false, shiftY 4 (law 1 4), law 2 4⟩, ⟨12, true, shiftY 4 (law 5 4), law 7 4⟩, ⟨24, false, shiftY 4 (law 3 4), law 8 4⟩]
theorem e1_F4Y_0_8_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 16)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R1 : (evalO2 (nfTree.mapRows (rowsIn 16 27)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R2 : (evalO2 (nfTree.mapRows (rowsIn 27 36)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R3 : (evalO2 (nfTree.mapRows (rowsIn 36 48)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R4 : (evalO2 (nfTree.mapRows (rowsIn 48 55)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R5 : (evalO2 (nfTree.mapRows (rowsIn 55 68)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R6 : (evalO2 (nfTree.mapRows (rowsIn 68 81)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R7 : (evalO2 (nfTree.mapRows (rowsIn 81 92)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R8 : (evalO2 (nfTree.mapRows (rowsIn 92 102)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R9 : (evalO2 (nfTree.mapRows (rowsIn 102 112)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R10 : (evalO2 (nfTree.mapRows (rowsIn 112 122)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R11 : (evalO2 (nfTree.mapRows (rowsIn 122 136)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_R12 : (evalO2 (nfTree.mapRows (rowsIn 136 144)) nfTree5 e1_F4Y_0_8).allZero = true := by decide +kernel
theorem e1_F4Y_0_8_B : wsum e1_F4Y_0_8 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_0_8_T : e1_F4Y_0_8.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
