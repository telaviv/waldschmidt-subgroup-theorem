import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table5
import LSG.Jac.Data.E1
import LSG.Jac.CheckerRange

/-! GENERATED — equivariance identities `F4Y` (law 4, `Y`-flow, output chart 4), j = 1, split by
`X`-slot ranges `rs_e1_F4Y_1_<l>` (adaptive, `scripts/jac/e1_cost.py`, budget 42000). -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

def rs_e1_F4Y_1_0 : List (Nat × Nat) := [(0, 20), (20, 31), (31, 43), (43, 53), (53, 69), (69, 89), (89, 101), (101, 112), (112, 123), (123, 140), (140, 144)]
noncomputable def e1_F4Y_1_0 : List Term := [⟨4, false, law 4 4, DA_Y4W4_1_0⟩, ⟨4, true, law 0 4, DA_Y4W4_1_4⟩, ⟨16, true, shiftY 4 (law 0 4), law 0 4⟩, ⟨96, false, shiftY 4 (law 1 4), law 2 4⟩]
theorem e1_F4Y_1_0_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 20)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R1 : (evalO2 (nfTree.mapRows (rowsIn 20 31)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R2 : (evalO2 (nfTree.mapRows (rowsIn 31 43)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R3 : (evalO2 (nfTree.mapRows (rowsIn 43 53)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R4 : (evalO2 (nfTree.mapRows (rowsIn 53 69)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R5 : (evalO2 (nfTree.mapRows (rowsIn 69 89)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R6 : (evalO2 (nfTree.mapRows (rowsIn 89 101)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R7 : (evalO2 (nfTree.mapRows (rowsIn 101 112)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R8 : (evalO2 (nfTree.mapRows (rowsIn 112 123)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R9 : (evalO2 (nfTree.mapRows (rowsIn 123 140)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_R10 : (evalO2 (nfTree.mapRows (rowsIn 140 144)) nfTree5 e1_F4Y_1_0).allZero = true := by decide +kernel
theorem e1_F4Y_1_0_B : wsum e1_F4Y_1_0 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_1_0_T : e1_F4Y_1_0.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_1_1 : List (Nat × Nat) := [(0, 16), (16, 27), (27, 36), (36, 48), (48, 55), (55, 69), (69, 83), (83, 96), (96, 110), (110, 117), (117, 133), (133, 144)]
noncomputable def e1_F4Y_1_1 : List Term := [⟨4, false, law 4 4, DA_Y4W4_1_1⟩, ⟨4, true, law 1 4, DA_Y4W4_1_4⟩, ⟨32, false, shiftY 4 (law 0 4), law 1 4⟩, ⟨24, false, shiftY 4 (law 2 4), law 3 4⟩, ⟨8, false, shiftY 4 (law 4 4), law 5 4⟩]
theorem e1_F4Y_1_1_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 16)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R1 : (evalO2 (nfTree.mapRows (rowsIn 16 27)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R2 : (evalO2 (nfTree.mapRows (rowsIn 27 36)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R3 : (evalO2 (nfTree.mapRows (rowsIn 36 48)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R4 : (evalO2 (nfTree.mapRows (rowsIn 48 55)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R5 : (evalO2 (nfTree.mapRows (rowsIn 55 69)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R6 : (evalO2 (nfTree.mapRows (rowsIn 69 83)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R7 : (evalO2 (nfTree.mapRows (rowsIn 83 96)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R8 : (evalO2 (nfTree.mapRows (rowsIn 96 110)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R9 : (evalO2 (nfTree.mapRows (rowsIn 110 117)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R10 : (evalO2 (nfTree.mapRows (rowsIn 117 133)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_R11 : (evalO2 (nfTree.mapRows (rowsIn 133 144)) nfTree5 e1_F4Y_1_1).allZero = true := by decide +kernel
theorem e1_F4Y_1_1_B : wsum e1_F4Y_1_1 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_1_1_T : e1_F4Y_1_1.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_1_2 : List (Nat × Nat) := [(0, 15), (15, 26), (26, 33), (33, 42), (42, 50), (50, 57), (57, 69), (69, 81), (81, 91), (91, 97), (97, 106), (106, 114), (114, 123), (123, 135), (135, 144)]
noncomputable def e1_F4Y_1_2 : List Term := [⟨4, false, law 4 4, DA_Y4W4_1_2⟩, ⟨4, true, law 2 4, DA_Y4W4_1_4⟩, ⟨8, false, shiftY 4 (law 0 4), law 2 4⟩, ⟨48, false, shiftY 4 (law 3 4), law 3 4⟩, ⟨8, false, shiftY 4 (law 4 4), law 6 4⟩, ⟨48, false, shiftY 4 (law 1 4), law 8 4⟩]
theorem e1_F4Y_1_2_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 15)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R1 : (evalO2 (nfTree.mapRows (rowsIn 15 26)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R2 : (evalO2 (nfTree.mapRows (rowsIn 26 33)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R3 : (evalO2 (nfTree.mapRows (rowsIn 33 42)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R4 : (evalO2 (nfTree.mapRows (rowsIn 42 50)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R5 : (evalO2 (nfTree.mapRows (rowsIn 50 57)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R6 : (evalO2 (nfTree.mapRows (rowsIn 57 69)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R7 : (evalO2 (nfTree.mapRows (rowsIn 69 81)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R8 : (evalO2 (nfTree.mapRows (rowsIn 81 91)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R9 : (evalO2 (nfTree.mapRows (rowsIn 91 97)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R10 : (evalO2 (nfTree.mapRows (rowsIn 97 106)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R11 : (evalO2 (nfTree.mapRows (rowsIn 106 114)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R12 : (evalO2 (nfTree.mapRows (rowsIn 114 123)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R13 : (evalO2 (nfTree.mapRows (rowsIn 123 135)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_R14 : (evalO2 (nfTree.mapRows (rowsIn 135 144)) nfTree5 e1_F4Y_1_2).allZero = true := by decide +kernel
theorem e1_F4Y_1_2_B : wsum e1_F4Y_1_2 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_1_2_T : e1_F4Y_1_2.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_1_3 : List (Nat × Nat) := [(0, 15), (15, 26), (26, 33), (33, 42), (42, 50), (50, 56), (56, 68), (68, 80), (80, 87), (87, 95), (95, 105), (105, 114), (114, 123), (123, 135), (135, 144)]
noncomputable def e1_F4Y_1_3 : List Term := [⟨4, false, law 4 4, DA_Y4W4_1_3⟩, ⟨4, true, law 3 4, DA_Y4W4_1_4⟩, ⟨96, false, shiftY 4 (law 1 4), law 1 4⟩, ⟨16, true, shiftY 4 (law 0 4), law 3 4⟩, ⟨8, false, shiftY 4 (law 4 4), law 7 4⟩, ⟨48, false, shiftY 4 (law 2 4), law 8 4⟩]
theorem e1_F4Y_1_3_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 15)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R1 : (evalO2 (nfTree.mapRows (rowsIn 15 26)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R2 : (evalO2 (nfTree.mapRows (rowsIn 26 33)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R3 : (evalO2 (nfTree.mapRows (rowsIn 33 42)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R4 : (evalO2 (nfTree.mapRows (rowsIn 42 50)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R5 : (evalO2 (nfTree.mapRows (rowsIn 50 56)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R6 : (evalO2 (nfTree.mapRows (rowsIn 56 68)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R7 : (evalO2 (nfTree.mapRows (rowsIn 68 80)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R8 : (evalO2 (nfTree.mapRows (rowsIn 80 87)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R9 : (evalO2 (nfTree.mapRows (rowsIn 87 95)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R10 : (evalO2 (nfTree.mapRows (rowsIn 95 105)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R11 : (evalO2 (nfTree.mapRows (rowsIn 105 114)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R12 : (evalO2 (nfTree.mapRows (rowsIn 114 123)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R13 : (evalO2 (nfTree.mapRows (rowsIn 123 135)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_R14 : (evalO2 (nfTree.mapRows (rowsIn 135 144)) nfTree5 e1_F4Y_1_3).allZero = true := by decide +kernel
theorem e1_F4Y_1_3_B : wsum e1_F4Y_1_3 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_1_3_T : e1_F4Y_1_3.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_1_5 : List (Nat × Nat) := [(0, 16), (16, 26), (26, 35), (35, 44), (44, 51), (51, 62), (62, 76), (76, 90), (90, 97), (97, 107), (107, 115), (115, 126), (126, 139), (139, 144)]
noncomputable def e1_F4Y_1_5 : List Term := [⟨4, false, law 4 4, DA_Y4W4_1_5⟩, ⟨4, true, law 5 4, DA_Y4W4_1_4⟩, ⟨16, true, shiftY 4 (law 0 4), law 5 4⟩, ⟨48, false, shiftY 4 (law 2 4), law 7 4⟩, ⟨32, false, shiftY 4 (law 4 4), law 8 4⟩]
theorem e1_F4Y_1_5_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 16)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R1 : (evalO2 (nfTree.mapRows (rowsIn 16 26)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R2 : (evalO2 (nfTree.mapRows (rowsIn 26 35)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R3 : (evalO2 (nfTree.mapRows (rowsIn 35 44)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R4 : (evalO2 (nfTree.mapRows (rowsIn 44 51)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R5 : (evalO2 (nfTree.mapRows (rowsIn 51 62)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R6 : (evalO2 (nfTree.mapRows (rowsIn 62 76)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R7 : (evalO2 (nfTree.mapRows (rowsIn 76 90)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R8 : (evalO2 (nfTree.mapRows (rowsIn 90 97)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R9 : (evalO2 (nfTree.mapRows (rowsIn 97 107)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R10 : (evalO2 (nfTree.mapRows (rowsIn 107 115)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R11 : (evalO2 (nfTree.mapRows (rowsIn 115 126)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R12 : (evalO2 (nfTree.mapRows (rowsIn 126 139)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_R13 : (evalO2 (nfTree.mapRows (rowsIn 139 144)) nfTree5 e1_F4Y_1_5).allZero = true := by decide +kernel
theorem e1_F4Y_1_5_B : wsum e1_F4Y_1_5 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_1_5_T : e1_F4Y_1_5.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_1_6 : List (Nat × Nat) := [(0, 14), (14, 25), (25, 31), (31, 37), (37, 47), (47, 53), (53, 62), (62, 73), (73, 83), (83, 92), (92, 102), (102, 111), (111, 117), (117, 126), (126, 136), (136, 144)]
noncomputable def e1_F4Y_1_6 : List Term := [⟨4, false, law 4 4, DA_Y4W4_1_6⟩, ⟨4, true, law 6 4, DA_Y4W4_1_4⟩, ⟨32, false, shiftY 4 (law 1 4), law 4 4⟩, ⟨16, true, shiftY 4 (law 0 4), law 6 4⟩, ⟨24, false, shiftY 4 (law 3 4), law 7 4⟩, ⟨48, false, shiftY 4 (law 5 4), law 8 4⟩]
theorem e1_F4Y_1_6_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 14)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R1 : (evalO2 (nfTree.mapRows (rowsIn 14 25)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R2 : (evalO2 (nfTree.mapRows (rowsIn 25 31)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R3 : (evalO2 (nfTree.mapRows (rowsIn 31 37)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R4 : (evalO2 (nfTree.mapRows (rowsIn 37 47)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R5 : (evalO2 (nfTree.mapRows (rowsIn 47 53)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R6 : (evalO2 (nfTree.mapRows (rowsIn 53 62)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R7 : (evalO2 (nfTree.mapRows (rowsIn 62 73)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R8 : (evalO2 (nfTree.mapRows (rowsIn 73 83)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R9 : (evalO2 (nfTree.mapRows (rowsIn 83 92)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R10 : (evalO2 (nfTree.mapRows (rowsIn 92 102)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R11 : (evalO2 (nfTree.mapRows (rowsIn 102 111)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R12 : (evalO2 (nfTree.mapRows (rowsIn 111 117)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R13 : (evalO2 (nfTree.mapRows (rowsIn 117 126)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R14 : (evalO2 (nfTree.mapRows (rowsIn 126 136)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_R15 : (evalO2 (nfTree.mapRows (rowsIn 136 144)) nfTree5 e1_F4Y_1_6).allZero = true := by decide +kernel
theorem e1_F4Y_1_6_B : wsum e1_F4Y_1_6 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_1_6_T : e1_F4Y_1_6.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_1_7 : List (Nat × Nat) := [(0, 15), (15, 26), (26, 33), (33, 42), (42, 51), (51, 62), (62, 76), (76, 89), (89, 96), (96, 107), (107, 115), (115, 125), (125, 139), (139, 144)]
noncomputable def e1_F4Y_1_7 : List Term := [⟨4, false, law 4 4, DA_Y4W4_1_7⟩, ⟨4, true, law 7 4, DA_Y4W4_1_4⟩, ⟨128, false, shiftY 4 (law 1 4), law 5 4⟩, ⟨8, true, shiftY 4 (law 0 4), law 7 4⟩, ⟨48, false, shiftY 4 (law 6 4), law 8 4⟩]
theorem e1_F4Y_1_7_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 15)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R1 : (evalO2 (nfTree.mapRows (rowsIn 15 26)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R2 : (evalO2 (nfTree.mapRows (rowsIn 26 33)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R3 : (evalO2 (nfTree.mapRows (rowsIn 33 42)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R4 : (evalO2 (nfTree.mapRows (rowsIn 42 51)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R5 : (evalO2 (nfTree.mapRows (rowsIn 51 62)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R6 : (evalO2 (nfTree.mapRows (rowsIn 62 76)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R7 : (evalO2 (nfTree.mapRows (rowsIn 76 89)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R8 : (evalO2 (nfTree.mapRows (rowsIn 89 96)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R9 : (evalO2 (nfTree.mapRows (rowsIn 96 107)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R10 : (evalO2 (nfTree.mapRows (rowsIn 107 115)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R11 : (evalO2 (nfTree.mapRows (rowsIn 115 125)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R12 : (evalO2 (nfTree.mapRows (rowsIn 125 139)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_R13 : (evalO2 (nfTree.mapRows (rowsIn 139 144)) nfTree5 e1_F4Y_1_7).allZero = true := by decide +kernel
theorem e1_F4Y_1_7_B : wsum e1_F4Y_1_7 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_1_7_T : e1_F4Y_1_7.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4Y_1_8 : List (Nat × Nat) := [(0, 15), (15, 26), (26, 33), (33, 42), (42, 50), (50, 61), (61, 72), (72, 83), (83, 92), (92, 102), (102, 111), (111, 117), (117, 126), (126, 139), (139, 144)]
noncomputable def e1_F4Y_1_8 : List Term := [⟨4, false, law 4 4, DA_Y4W4_1_8⟩, ⟨4, true, law 8 4, DA_Y4W4_1_4⟩, ⟨48, true, shiftY 4 (law 1 4), law 3 4⟩, ⟨16, true, shiftY 4 (law 4 4), law 4 4⟩, ⟨12, false, shiftY 4 (law 6 4), law 7 4⟩, ⟨8, false, shiftY 4 (law 0 4), law 8 4⟩]
theorem e1_F4Y_1_8_R0 : (evalO2 (nfTree.mapRows (rowsIn 0 15)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R1 : (evalO2 (nfTree.mapRows (rowsIn 15 26)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R2 : (evalO2 (nfTree.mapRows (rowsIn 26 33)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R3 : (evalO2 (nfTree.mapRows (rowsIn 33 42)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R4 : (evalO2 (nfTree.mapRows (rowsIn 42 50)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R5 : (evalO2 (nfTree.mapRows (rowsIn 50 61)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R6 : (evalO2 (nfTree.mapRows (rowsIn 61 72)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R7 : (evalO2 (nfTree.mapRows (rowsIn 72 83)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R8 : (evalO2 (nfTree.mapRows (rowsIn 83 92)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R9 : (evalO2 (nfTree.mapRows (rowsIn 92 102)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R10 : (evalO2 (nfTree.mapRows (rowsIn 102 111)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R11 : (evalO2 (nfTree.mapRows (rowsIn 111 117)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R12 : (evalO2 (nfTree.mapRows (rowsIn 117 126)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R13 : (evalO2 (nfTree.mapRows (rowsIn 126 139)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_R14 : (evalO2 (nfTree.mapRows (rowsIn 139 144)) nfTree5 e1_F4Y_1_8).allZero = true := by decide +kernel
theorem e1_F4Y_1_8_B : wsum e1_F4Y_1_8 * (rowM * rowM5) < 2 ^ kb5 := by decide +kernel
theorem e1_F4Y_1_8_T : e1_F4Y_1_8.all (fun q => termOK2 nfTree nfTree5 q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
