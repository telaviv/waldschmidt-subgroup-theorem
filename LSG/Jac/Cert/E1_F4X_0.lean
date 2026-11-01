import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table5
import LSG.Jac.Data.E1
import LSG.Jac.CheckerRange

/-! GENERATED — equivariance identities `F4X` (law 4, `X`-flow, output chart 4), j = 0, split by
`X`-slot ranges `rs_e1_F4X_0_<l>` (adaptive, `scripts/jac/e1_cost.py`, budget 50000). -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

def rs_e1_F4X_0_0 : List (Nat × Nat) := [(0, 39), (39, 52), (52, 66), (66, 85), (85, 109), (109, 123), (123, 137), (137, 148), (148, 165), (165, 177), (177, 195), (195, 216), (216, 225)]
noncomputable def e1_F4X_0_0 : List Term := [⟨4, false, law 4 4, DA_X4W4_0_0⟩, ⟨4, true, law 0 4, DA_X4W4_0_4⟩, ⟨96, false, shiftX 4 (law 1 4), law 1 4⟩, ⟨48, true, shiftX 4 (law 0 4), law 3 4⟩]
theorem e1_F4X_0_0_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 39)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R1 : (evalO2 (nfTree5.mapRows (rowsIn 39 52)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R2 : (evalO2 (nfTree5.mapRows (rowsIn 52 66)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R3 : (evalO2 (nfTree5.mapRows (rowsIn 66 85)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R4 : (evalO2 (nfTree5.mapRows (rowsIn 85 109)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R5 : (evalO2 (nfTree5.mapRows (rowsIn 109 123)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R6 : (evalO2 (nfTree5.mapRows (rowsIn 123 137)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R7 : (evalO2 (nfTree5.mapRows (rowsIn 137 148)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R8 : (evalO2 (nfTree5.mapRows (rowsIn 148 165)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R9 : (evalO2 (nfTree5.mapRows (rowsIn 165 177)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R10 : (evalO2 (nfTree5.mapRows (rowsIn 177 195)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R11 : (evalO2 (nfTree5.mapRows (rowsIn 195 216)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_R12 : (evalO2 (nfTree5.mapRows (rowsIn 216 225)) nfTree4b e1_F4X_0_0).allZero = true := by decide +kernel
theorem e1_F4X_0_0_B : wsum e1_F4X_0_0 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_0_0_T : e1_F4X_0_0.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_0_1 : List (Nat × Nat) := [(0, 31), (31, 47), (47, 61), (61, 74), (74, 86), (86, 100), (100, 120), (120, 130), (130, 140), (140, 151), (151, 166), (166, 176), (176, 195), (195, 215), (215, 225)]
noncomputable def e1_F4X_0_1 : List Term := [⟨4, false, law 4 4, DA_X4W4_0_1⟩, ⟨4, true, law 1 4, DA_X4W4_0_4⟩, ⟨24, false, shiftX 4 (law 1 4), law 3 4⟩, ⟨8, false, shiftX 4 (law 4 4), law 4 4⟩, ⟨24, true, shiftX 4 (law 0 4), law 8 4⟩]
theorem e1_F4X_0_1_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 31)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R1 : (evalO2 (nfTree5.mapRows (rowsIn 31 47)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R2 : (evalO2 (nfTree5.mapRows (rowsIn 47 61)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R3 : (evalO2 (nfTree5.mapRows (rowsIn 61 74)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R4 : (evalO2 (nfTree5.mapRows (rowsIn 74 86)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R5 : (evalO2 (nfTree5.mapRows (rowsIn 86 100)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R6 : (evalO2 (nfTree5.mapRows (rowsIn 100 120)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R7 : (evalO2 (nfTree5.mapRows (rowsIn 120 130)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R8 : (evalO2 (nfTree5.mapRows (rowsIn 130 140)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R9 : (evalO2 (nfTree5.mapRows (rowsIn 140 151)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R10 : (evalO2 (nfTree5.mapRows (rowsIn 151 166)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R11 : (evalO2 (nfTree5.mapRows (rowsIn 166 176)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R12 : (evalO2 (nfTree5.mapRows (rowsIn 176 195)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R13 : (evalO2 (nfTree5.mapRows (rowsIn 195 215)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_R14 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_F4X_0_1).allZero = true := by decide +kernel
theorem e1_F4X_0_1_B : wsum e1_F4X_0_1 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_0_1_T : e1_F4X_0_1.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_0_2 : List (Nat × Nat) := [(0, 28), (28, 44), (44, 57), (57, 71), (71, 83), (83, 100), (100, 120), (120, 128), (128, 139), (139, 150), (150, 165), (165, 176), (176, 194), (194, 214), (214, 225)]
noncomputable def e1_F4X_0_2 : List Term := [⟨4, false, law 4 4, DA_X4W4_0_2⟩, ⟨4, true, law 2 4, DA_X4W4_0_4⟩, ⟨48, false, shiftX 4 (law 0 4), law 1 4⟩, ⟨24, true, shiftX 4 (law 2 4), law 3 4⟩, ⟨8, false, shiftX 4 (law 4 4), law 5 4⟩]
theorem e1_F4X_0_2_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 28)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R1 : (evalO2 (nfTree5.mapRows (rowsIn 28 44)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R2 : (evalO2 (nfTree5.mapRows (rowsIn 44 57)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R3 : (evalO2 (nfTree5.mapRows (rowsIn 57 71)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R4 : (evalO2 (nfTree5.mapRows (rowsIn 71 83)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R5 : (evalO2 (nfTree5.mapRows (rowsIn 83 100)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R6 : (evalO2 (nfTree5.mapRows (rowsIn 100 120)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R7 : (evalO2 (nfTree5.mapRows (rowsIn 120 128)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R8 : (evalO2 (nfTree5.mapRows (rowsIn 128 139)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R9 : (evalO2 (nfTree5.mapRows (rowsIn 139 150)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R10 : (evalO2 (nfTree5.mapRows (rowsIn 150 165)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R11 : (evalO2 (nfTree5.mapRows (rowsIn 165 176)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R12 : (evalO2 (nfTree5.mapRows (rowsIn 176 194)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R13 : (evalO2 (nfTree5.mapRows (rowsIn 194 214)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_R14 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_F4X_0_2).allZero = true := by decide +kernel
theorem e1_F4X_0_2_B : wsum e1_F4X_0_2 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_0_2_T : e1_F4X_0_2.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_0_3 : List (Nat × Nat) := [(0, 28), (28, 43), (43, 57), (57, 71), (71, 83), (83, 99), (99, 119), (119, 126), (126, 137), (137, 147), (147, 162), (162, 175), (175, 186), (186, 199), (199, 215), (215, 225)]
noncomputable def e1_F4X_0_3 : List Term := [⟨4, false, law 4 4, DA_X4W4_0_3⟩, ⟨4, true, law 3 4, DA_X4W4_0_4⟩, ⟨24, false, shiftX 4 (law 0 4), law 2 4⟩, ⟨8, false, shiftX 4 (law 4 4), law 6 4⟩, ⟨48, true, shiftX 4 (law 1 4), law 8 4⟩]
theorem e1_F4X_0_3_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 28)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R1 : (evalO2 (nfTree5.mapRows (rowsIn 28 43)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R2 : (evalO2 (nfTree5.mapRows (rowsIn 43 57)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R3 : (evalO2 (nfTree5.mapRows (rowsIn 57 71)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R4 : (evalO2 (nfTree5.mapRows (rowsIn 71 83)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R5 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R6 : (evalO2 (nfTree5.mapRows (rowsIn 99 119)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R7 : (evalO2 (nfTree5.mapRows (rowsIn 119 126)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R8 : (evalO2 (nfTree5.mapRows (rowsIn 126 137)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R9 : (evalO2 (nfTree5.mapRows (rowsIn 137 147)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R10 : (evalO2 (nfTree5.mapRows (rowsIn 147 162)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R11 : (evalO2 (nfTree5.mapRows (rowsIn 162 175)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R12 : (evalO2 (nfTree5.mapRows (rowsIn 175 186)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R13 : (evalO2 (nfTree5.mapRows (rowsIn 186 199)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R14 : (evalO2 (nfTree5.mapRows (rowsIn 199 215)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_R15 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_F4X_0_3).allZero = true := by decide +kernel
theorem e1_F4X_0_3_B : wsum e1_F4X_0_3 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_0_3_T : e1_F4X_0_3.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_0_5 : List (Nat × Nat) := [(0, 25), (25, 39), (39, 47), (47, 57), (57, 71), (71, 83), (83, 99), (99, 119), (119, 126), (126, 137), (137, 147), (147, 161), (161, 175), (175, 186), (186, 199), (199, 215), (215, 225)]
noncomputable def e1_F4X_0_5 : List Term := [⟨4, false, law 4 4, DA_X4W4_0_5⟩, ⟨4, true, law 5 4, DA_X4W4_0_4⟩, ⟨8, true, shiftX 4 (law 0 4), law 4 4⟩, ⟨24, true, shiftX 4 (law 2 4), law 6 4⟩, ⟨24, false, shiftX 4 (law 1 4), law 7 4⟩]
theorem e1_F4X_0_5_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 25)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R1 : (evalO2 (nfTree5.mapRows (rowsIn 25 39)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R2 : (evalO2 (nfTree5.mapRows (rowsIn 39 47)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R3 : (evalO2 (nfTree5.mapRows (rowsIn 47 57)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 71)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R5 : (evalO2 (nfTree5.mapRows (rowsIn 71 83)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R6 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R7 : (evalO2 (nfTree5.mapRows (rowsIn 99 119)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R8 : (evalO2 (nfTree5.mapRows (rowsIn 119 126)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R9 : (evalO2 (nfTree5.mapRows (rowsIn 126 137)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R10 : (evalO2 (nfTree5.mapRows (rowsIn 137 147)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R11 : (evalO2 (nfTree5.mapRows (rowsIn 147 161)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R12 : (evalO2 (nfTree5.mapRows (rowsIn 161 175)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R13 : (evalO2 (nfTree5.mapRows (rowsIn 175 186)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R14 : (evalO2 (nfTree5.mapRows (rowsIn 186 199)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R15 : (evalO2 (nfTree5.mapRows (rowsIn 199 215)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_R16 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_F4X_0_5).allZero = true := by decide +kernel
theorem e1_F4X_0_5_B : wsum e1_F4X_0_5 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_0_5_T : e1_F4X_0_5.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_0_6 : List (Nat × Nat) := [(0, 25), (25, 39), (39, 47), (47, 57), (57, 71), (71, 83), (83, 99), (99, 119), (119, 126), (126, 137), (137, 147), (147, 161), (161, 175), (175, 186), (186, 199), (199, 215), (215, 225)]
noncomputable def e1_F4X_0_6 : List Term := [⟨4, false, law 4 4, DA_X4W4_0_6⟩, ⟨4, true, law 6 4, DA_X4W4_0_4⟩, ⟨48, false, shiftX 4 (law 0 4), law 5 4⟩, ⟨24, true, shiftX 4 (law 2 4), law 7 4⟩, ⟨16, true, shiftX 4 (law 4 4), law 8 4⟩]
theorem e1_F4X_0_6_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 25)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R1 : (evalO2 (nfTree5.mapRows (rowsIn 25 39)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R2 : (evalO2 (nfTree5.mapRows (rowsIn 39 47)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R3 : (evalO2 (nfTree5.mapRows (rowsIn 47 57)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 71)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R5 : (evalO2 (nfTree5.mapRows (rowsIn 71 83)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R6 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R7 : (evalO2 (nfTree5.mapRows (rowsIn 99 119)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R8 : (evalO2 (nfTree5.mapRows (rowsIn 119 126)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R9 : (evalO2 (nfTree5.mapRows (rowsIn 126 137)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R10 : (evalO2 (nfTree5.mapRows (rowsIn 137 147)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R11 : (evalO2 (nfTree5.mapRows (rowsIn 147 161)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R12 : (evalO2 (nfTree5.mapRows (rowsIn 161 175)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R13 : (evalO2 (nfTree5.mapRows (rowsIn 175 186)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R14 : (evalO2 (nfTree5.mapRows (rowsIn 186 199)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R15 : (evalO2 (nfTree5.mapRows (rowsIn 199 215)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_R16 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_F4X_0_6).allZero = true := by decide +kernel
theorem e1_F4X_0_6_B : wsum e1_F4X_0_6 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_0_6_T : e1_F4X_0_6.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_0_7 : List (Nat × Nat) := [(0, 25), (25, 39), (39, 47), (47, 57), (57, 70), (70, 83), (83, 99), (99, 117), (117, 123), (123, 133), (133, 140), (140, 151), (151, 164), (164, 176), (176, 187), (187, 199), (199, 214), (214, 225)]
noncomputable def e1_F4X_0_7 : List Term := [⟨4, false, law 4 4, DA_X4W4_0_7⟩, ⟨4, true, law 7 4, DA_X4W4_0_4⟩, ⟨64, true, shiftX 4 (law 1 4), law 4 4⟩, ⟨24, false, shiftX 4 (law 3 4), law 7 4⟩, ⟨48, true, shiftX 4 (law 5 4), law 8 4⟩]
theorem e1_F4X_0_7_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 25)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R1 : (evalO2 (nfTree5.mapRows (rowsIn 25 39)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R2 : (evalO2 (nfTree5.mapRows (rowsIn 39 47)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R3 : (evalO2 (nfTree5.mapRows (rowsIn 47 57)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 70)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R5 : (evalO2 (nfTree5.mapRows (rowsIn 70 83)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R6 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R7 : (evalO2 (nfTree5.mapRows (rowsIn 99 117)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R8 : (evalO2 (nfTree5.mapRows (rowsIn 117 123)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R9 : (evalO2 (nfTree5.mapRows (rowsIn 123 133)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R10 : (evalO2 (nfTree5.mapRows (rowsIn 133 140)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R11 : (evalO2 (nfTree5.mapRows (rowsIn 140 151)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R12 : (evalO2 (nfTree5.mapRows (rowsIn 151 164)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R13 : (evalO2 (nfTree5.mapRows (rowsIn 164 176)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R14 : (evalO2 (nfTree5.mapRows (rowsIn 176 187)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R15 : (evalO2 (nfTree5.mapRows (rowsIn 187 199)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R16 : (evalO2 (nfTree5.mapRows (rowsIn 199 214)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_R17 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_F4X_0_7).allZero = true := by decide +kernel
theorem e1_F4X_0_7_B : wsum e1_F4X_0_7 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_0_7_T : e1_F4X_0_7.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_0_8 : List (Nat × Nat) := [(0, 26), (26, 40), (40, 47), (47, 57), (57, 69), (69, 83), (83, 99), (99, 116), (116, 123), (123, 132), (132, 140), (140, 150), (150, 164), (164, 175), (175, 185), (185, 196), (196, 214), (214, 225)]
noncomputable def e1_F4X_0_8 : List Term := [⟨4, false, law 4 4, DA_X4W4_0_8⟩, ⟨4, true, law 8 4, DA_X4W4_0_4⟩, ⟨96, false, shiftX 4 (law 1 4), law 2 4⟩, ⟨12, true, shiftX 4 (law 5 4), law 7 4⟩, ⟨24, false, shiftX 4 (law 3 4), law 8 4⟩]
theorem e1_F4X_0_8_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 26)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R1 : (evalO2 (nfTree5.mapRows (rowsIn 26 40)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R2 : (evalO2 (nfTree5.mapRows (rowsIn 40 47)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R3 : (evalO2 (nfTree5.mapRows (rowsIn 47 57)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 69)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R5 : (evalO2 (nfTree5.mapRows (rowsIn 69 83)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R6 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R7 : (evalO2 (nfTree5.mapRows (rowsIn 99 116)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R8 : (evalO2 (nfTree5.mapRows (rowsIn 116 123)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R9 : (evalO2 (nfTree5.mapRows (rowsIn 123 132)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R10 : (evalO2 (nfTree5.mapRows (rowsIn 132 140)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R11 : (evalO2 (nfTree5.mapRows (rowsIn 140 150)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R12 : (evalO2 (nfTree5.mapRows (rowsIn 150 164)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R13 : (evalO2 (nfTree5.mapRows (rowsIn 164 175)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R14 : (evalO2 (nfTree5.mapRows (rowsIn 175 185)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R15 : (evalO2 (nfTree5.mapRows (rowsIn 185 196)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R16 : (evalO2 (nfTree5.mapRows (rowsIn 196 214)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_R17 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_F4X_0_8).allZero = true := by decide +kernel
theorem e1_F4X_0_8_B : wsum e1_F4X_0_8 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_0_8_T : e1_F4X_0_8.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
