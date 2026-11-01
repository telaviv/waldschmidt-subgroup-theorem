import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table5
import LSG.Jac.Data.E1
import LSG.Jac.CheckerRange

/-! GENERATED — equivariance identities `F4X` (law 4, `X`-flow, output chart 4), j = 1, split by
`X`-slot ranges `rs_e1_F4X_1_<l>` (adaptive, `scripts/jac/e1_cost.py`, budget 50000). -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

def rs_e1_F4X_1_0 : List (Nat × Nat) := [(0, 34), (34, 48), (48, 63), (63, 80), (80, 96), (96, 120), (120, 131), (131, 141), (141, 160), (160, 176), (176, 195), (195, 215), (215, 225)]
noncomputable def e1_F4X_1_0 : List Term := [⟨4, false, law 4 4, DA_X4W4_1_0⟩, ⟨4, true, law 0 4, DA_X4W4_1_4⟩, ⟨16, true, shiftX 4 (law 0 4), law 0 4⟩, ⟨96, false, shiftX 4 (law 1 4), law 2 4⟩]
theorem e1_F4X_1_0_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 34)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R1 : (evalO2 (nfTree5.mapRows (rowsIn 34 48)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R2 : (evalO2 (nfTree5.mapRows (rowsIn 48 63)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R3 : (evalO2 (nfTree5.mapRows (rowsIn 63 80)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R4 : (evalO2 (nfTree5.mapRows (rowsIn 80 96)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R5 : (evalO2 (nfTree5.mapRows (rowsIn 96 120)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R6 : (evalO2 (nfTree5.mapRows (rowsIn 120 131)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R7 : (evalO2 (nfTree5.mapRows (rowsIn 131 141)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R8 : (evalO2 (nfTree5.mapRows (rowsIn 141 160)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R9 : (evalO2 (nfTree5.mapRows (rowsIn 160 176)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R10 : (evalO2 (nfTree5.mapRows (rowsIn 176 195)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R11 : (evalO2 (nfTree5.mapRows (rowsIn 195 215)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_R12 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_F4X_1_0).allZero = true := by decide +kernel
theorem e1_F4X_1_0_B : wsum e1_F4X_1_0 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_1_0_T : e1_F4X_1_0.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_1_1 : List (Nat × Nat) := [(0, 26), (26, 40), (40, 48), (48, 57), (57, 71), (71, 83), (83, 99), (99, 118), (118, 124), (124, 135), (135, 142), (142, 152), (152, 164), (164, 176), (176, 188), (188, 199), (199, 214), (214, 225)]
noncomputable def e1_F4X_1_1 : List Term := [⟨4, false, law 4 4, DA_X4W4_1_1⟩, ⟨4, true, law 1 4, DA_X4W4_1_4⟩, ⟨32, false, shiftX 4 (law 0 4), law 1 4⟩, ⟨24, false, shiftX 4 (law 2 4), law 3 4⟩, ⟨8, false, shiftX 4 (law 4 4), law 5 4⟩]
theorem e1_F4X_1_1_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 26)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R1 : (evalO2 (nfTree5.mapRows (rowsIn 26 40)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R2 : (evalO2 (nfTree5.mapRows (rowsIn 40 48)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R3 : (evalO2 (nfTree5.mapRows (rowsIn 48 57)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 71)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R5 : (evalO2 (nfTree5.mapRows (rowsIn 71 83)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R6 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R7 : (evalO2 (nfTree5.mapRows (rowsIn 99 118)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R8 : (evalO2 (nfTree5.mapRows (rowsIn 118 124)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R9 : (evalO2 (nfTree5.mapRows (rowsIn 124 135)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R10 : (evalO2 (nfTree5.mapRows (rowsIn 135 142)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R11 : (evalO2 (nfTree5.mapRows (rowsIn 142 152)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R12 : (evalO2 (nfTree5.mapRows (rowsIn 152 164)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R13 : (evalO2 (nfTree5.mapRows (rowsIn 164 176)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R14 : (evalO2 (nfTree5.mapRows (rowsIn 176 188)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R15 : (evalO2 (nfTree5.mapRows (rowsIn 188 199)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R16 : (evalO2 (nfTree5.mapRows (rowsIn 199 214)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_R17 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_F4X_1_1).allZero = true := by decide +kernel
theorem e1_F4X_1_1_B : wsum e1_F4X_1_1 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_1_1_T : e1_F4X_1_1.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_1_2 : List (Nat × Nat) := [(0, 24), (24, 34), (34, 44), (44, 56), (56, 66), (66, 76), (76, 86), (86, 97), (97, 112), (112, 122), (122, 131), (131, 139), (139, 148), (148, 161), (161, 174), (174, 183), (183, 196), (196, 211), (211, 220), (220, 225)]
noncomputable def e1_F4X_1_2 : List Term := [⟨4, false, law 4 4, DA_X4W4_1_2⟩, ⟨4, true, law 2 4, DA_X4W4_1_4⟩, ⟨8, false, shiftX 4 (law 0 4), law 2 4⟩, ⟨48, false, shiftX 4 (law 3 4), law 3 4⟩, ⟨8, false, shiftX 4 (law 4 4), law 6 4⟩, ⟨48, false, shiftX 4 (law 1 4), law 8 4⟩]
theorem e1_F4X_1_2_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 34)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R2 : (evalO2 (nfTree5.mapRows (rowsIn 34 44)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R3 : (evalO2 (nfTree5.mapRows (rowsIn 44 56)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R4 : (evalO2 (nfTree5.mapRows (rowsIn 56 66)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R5 : (evalO2 (nfTree5.mapRows (rowsIn 66 76)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R6 : (evalO2 (nfTree5.mapRows (rowsIn 76 86)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R7 : (evalO2 (nfTree5.mapRows (rowsIn 86 97)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R8 : (evalO2 (nfTree5.mapRows (rowsIn 97 112)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R9 : (evalO2 (nfTree5.mapRows (rowsIn 112 122)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R10 : (evalO2 (nfTree5.mapRows (rowsIn 122 131)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R11 : (evalO2 (nfTree5.mapRows (rowsIn 131 139)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R12 : (evalO2 (nfTree5.mapRows (rowsIn 139 148)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R13 : (evalO2 (nfTree5.mapRows (rowsIn 148 161)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R14 : (evalO2 (nfTree5.mapRows (rowsIn 161 174)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R15 : (evalO2 (nfTree5.mapRows (rowsIn 174 183)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R16 : (evalO2 (nfTree5.mapRows (rowsIn 183 196)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R17 : (evalO2 (nfTree5.mapRows (rowsIn 196 211)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R18 : (evalO2 (nfTree5.mapRows (rowsIn 211 220)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_R19 : (evalO2 (nfTree5.mapRows (rowsIn 220 225)) nfTree4b e1_F4X_1_2).allZero = true := by decide +kernel
theorem e1_F4X_1_2_B : wsum e1_F4X_1_2 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_1_2_T : e1_F4X_1_2.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_1_3 : List (Nat × Nat) := [(0, 24), (24, 34), (34, 44), (44, 56), (56, 66), (66, 76), (76, 86), (86, 96), (96, 112), (112, 122), (122, 131), (131, 139), (139, 148), (148, 160), (160, 172), (172, 182), (182, 195), (195, 208), (208, 215), (215, 225)]
noncomputable def e1_F4X_1_3 : List Term := [⟨4, false, law 4 4, DA_X4W4_1_3⟩, ⟨4, true, law 3 4, DA_X4W4_1_4⟩, ⟨96, false, shiftX 4 (law 1 4), law 1 4⟩, ⟨16, true, shiftX 4 (law 0 4), law 3 4⟩, ⟨8, false, shiftX 4 (law 4 4), law 7 4⟩, ⟨48, false, shiftX 4 (law 2 4), law 8 4⟩]
theorem e1_F4X_1_3_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 34)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R2 : (evalO2 (nfTree5.mapRows (rowsIn 34 44)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R3 : (evalO2 (nfTree5.mapRows (rowsIn 44 56)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R4 : (evalO2 (nfTree5.mapRows (rowsIn 56 66)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R5 : (evalO2 (nfTree5.mapRows (rowsIn 66 76)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R6 : (evalO2 (nfTree5.mapRows (rowsIn 76 86)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R7 : (evalO2 (nfTree5.mapRows (rowsIn 86 96)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R8 : (evalO2 (nfTree5.mapRows (rowsIn 96 112)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R9 : (evalO2 (nfTree5.mapRows (rowsIn 112 122)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R10 : (evalO2 (nfTree5.mapRows (rowsIn 122 131)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R11 : (evalO2 (nfTree5.mapRows (rowsIn 131 139)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R12 : (evalO2 (nfTree5.mapRows (rowsIn 139 148)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R13 : (evalO2 (nfTree5.mapRows (rowsIn 148 160)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R14 : (evalO2 (nfTree5.mapRows (rowsIn 160 172)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R15 : (evalO2 (nfTree5.mapRows (rowsIn 172 182)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R16 : (evalO2 (nfTree5.mapRows (rowsIn 182 195)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R17 : (evalO2 (nfTree5.mapRows (rowsIn 195 208)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R18 : (evalO2 (nfTree5.mapRows (rowsIn 208 215)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_R19 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_F4X_1_3).allZero = true := by decide +kernel
theorem e1_F4X_1_3_B : wsum e1_F4X_1_3 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_1_3_T : e1_F4X_1_3.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_1_5 : List (Nat × Nat) := [(0, 24), (24, 34), (34, 45), (45, 57), (57, 67), (67, 77), (77, 91), (91, 101), (101, 120), (120, 127), (127, 137), (137, 147), (147, 161), (161, 174), (174, 183), (183, 196), (196, 214), (214, 225)]
noncomputable def e1_F4X_1_5 : List Term := [⟨4, false, law 4 4, DA_X4W4_1_5⟩, ⟨4, true, law 5 4, DA_X4W4_1_4⟩, ⟨16, true, shiftX 4 (law 0 4), law 5 4⟩, ⟨48, false, shiftX 4 (law 2 4), law 7 4⟩, ⟨32, false, shiftX 4 (law 4 4), law 8 4⟩]
theorem e1_F4X_1_5_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 34)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R2 : (evalO2 (nfTree5.mapRows (rowsIn 34 45)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R3 : (evalO2 (nfTree5.mapRows (rowsIn 45 57)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 67)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R5 : (evalO2 (nfTree5.mapRows (rowsIn 67 77)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R6 : (evalO2 (nfTree5.mapRows (rowsIn 77 91)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R7 : (evalO2 (nfTree5.mapRows (rowsIn 91 101)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R8 : (evalO2 (nfTree5.mapRows (rowsIn 101 120)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R9 : (evalO2 (nfTree5.mapRows (rowsIn 120 127)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R10 : (evalO2 (nfTree5.mapRows (rowsIn 127 137)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R11 : (evalO2 (nfTree5.mapRows (rowsIn 137 147)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R12 : (evalO2 (nfTree5.mapRows (rowsIn 147 161)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R13 : (evalO2 (nfTree5.mapRows (rowsIn 161 174)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R14 : (evalO2 (nfTree5.mapRows (rowsIn 174 183)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R15 : (evalO2 (nfTree5.mapRows (rowsIn 183 196)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R16 : (evalO2 (nfTree5.mapRows (rowsIn 196 214)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_R17 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_F4X_1_5).allZero = true := by decide +kernel
theorem e1_F4X_1_5_B : wsum e1_F4X_1_5 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_1_5_T : e1_F4X_1_5.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_1_6 : List (Nat × Nat) := [(0, 23), (23, 33), (33, 43), (43, 55), (55, 65), (65, 76), (76, 86), (86, 96), (96, 112), (112, 122), (122, 131), (131, 139), (139, 148), (148, 160), (160, 172), (172, 182), (182, 195), (195, 208), (208, 215), (215, 225)]
noncomputable def e1_F4X_1_6 : List Term := [⟨4, false, law 4 4, DA_X4W4_1_6⟩, ⟨4, true, law 6 4, DA_X4W4_1_4⟩, ⟨32, false, shiftX 4 (law 1 4), law 4 4⟩, ⟨16, true, shiftX 4 (law 0 4), law 6 4⟩, ⟨24, false, shiftX 4 (law 3 4), law 7 4⟩, ⟨48, false, shiftX 4 (law 5 4), law 8 4⟩]
theorem e1_F4X_1_6_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 33)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R2 : (evalO2 (nfTree5.mapRows (rowsIn 33 43)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R3 : (evalO2 (nfTree5.mapRows (rowsIn 43 55)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R4 : (evalO2 (nfTree5.mapRows (rowsIn 55 65)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R5 : (evalO2 (nfTree5.mapRows (rowsIn 65 76)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R6 : (evalO2 (nfTree5.mapRows (rowsIn 76 86)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R7 : (evalO2 (nfTree5.mapRows (rowsIn 86 96)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R8 : (evalO2 (nfTree5.mapRows (rowsIn 96 112)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R9 : (evalO2 (nfTree5.mapRows (rowsIn 112 122)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R10 : (evalO2 (nfTree5.mapRows (rowsIn 122 131)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R11 : (evalO2 (nfTree5.mapRows (rowsIn 131 139)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R12 : (evalO2 (nfTree5.mapRows (rowsIn 139 148)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R13 : (evalO2 (nfTree5.mapRows (rowsIn 148 160)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R14 : (evalO2 (nfTree5.mapRows (rowsIn 160 172)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R15 : (evalO2 (nfTree5.mapRows (rowsIn 172 182)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R16 : (evalO2 (nfTree5.mapRows (rowsIn 182 195)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R17 : (evalO2 (nfTree5.mapRows (rowsIn 195 208)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R18 : (evalO2 (nfTree5.mapRows (rowsIn 208 215)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_R19 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_F4X_1_6).allZero = true := by decide +kernel
theorem e1_F4X_1_6_B : wsum e1_F4X_1_6 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_1_6_T : e1_F4X_1_6.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_1_7 : List (Nat × Nat) := [(0, 24), (24, 34), (34, 44), (44, 56), (56, 67), (67, 77), (77, 87), (87, 99), (99, 115), (115, 123), (123, 132), (132, 140), (140, 150), (150, 164), (164, 175), (175, 185), (185, 196), (196, 213), (213, 225)]
noncomputable def e1_F4X_1_7 : List Term := [⟨4, false, law 4 4, DA_X4W4_1_7⟩, ⟨4, true, law 7 4, DA_X4W4_1_4⟩, ⟨128, false, shiftX 4 (law 1 4), law 5 4⟩, ⟨8, true, shiftX 4 (law 0 4), law 7 4⟩, ⟨48, false, shiftX 4 (law 6 4), law 8 4⟩]
theorem e1_F4X_1_7_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 34)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R2 : (evalO2 (nfTree5.mapRows (rowsIn 34 44)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R3 : (evalO2 (nfTree5.mapRows (rowsIn 44 56)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R4 : (evalO2 (nfTree5.mapRows (rowsIn 56 67)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R5 : (evalO2 (nfTree5.mapRows (rowsIn 67 77)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R6 : (evalO2 (nfTree5.mapRows (rowsIn 77 87)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R7 : (evalO2 (nfTree5.mapRows (rowsIn 87 99)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R8 : (evalO2 (nfTree5.mapRows (rowsIn 99 115)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R9 : (evalO2 (nfTree5.mapRows (rowsIn 115 123)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R10 : (evalO2 (nfTree5.mapRows (rowsIn 123 132)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R11 : (evalO2 (nfTree5.mapRows (rowsIn 132 140)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R12 : (evalO2 (nfTree5.mapRows (rowsIn 140 150)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R13 : (evalO2 (nfTree5.mapRows (rowsIn 150 164)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R14 : (evalO2 (nfTree5.mapRows (rowsIn 164 175)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R15 : (evalO2 (nfTree5.mapRows (rowsIn 175 185)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R16 : (evalO2 (nfTree5.mapRows (rowsIn 185 196)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R17 : (evalO2 (nfTree5.mapRows (rowsIn 196 213)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_R18 : (evalO2 (nfTree5.mapRows (rowsIn 213 225)) nfTree4b e1_F4X_1_7).allZero = true := by decide +kernel
theorem e1_F4X_1_7_B : wsum e1_F4X_1_7 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_1_7_T : e1_F4X_1_7.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_F4X_1_8 : List (Nat × Nat) := [(0, 24), (24, 36), (36, 45), (45, 56), (56, 66), (66, 76), (76, 86), (86, 98), (98, 112), (112, 122), (122, 131), (131, 139), (139, 148), (148, 160), (160, 174), (174, 183), (183, 196), (196, 211), (211, 220), (220, 225)]
noncomputable def e1_F4X_1_8 : List Term := [⟨4, false, law 4 4, DA_X4W4_1_8⟩, ⟨4, true, law 8 4, DA_X4W4_1_4⟩, ⟨48, true, shiftX 4 (law 1 4), law 3 4⟩, ⟨16, true, shiftX 4 (law 4 4), law 4 4⟩, ⟨12, false, shiftX 4 (law 6 4), law 7 4⟩, ⟨8, false, shiftX 4 (law 0 4), law 8 4⟩]
theorem e1_F4X_1_8_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 36)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R2 : (evalO2 (nfTree5.mapRows (rowsIn 36 45)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R3 : (evalO2 (nfTree5.mapRows (rowsIn 45 56)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R4 : (evalO2 (nfTree5.mapRows (rowsIn 56 66)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R5 : (evalO2 (nfTree5.mapRows (rowsIn 66 76)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R6 : (evalO2 (nfTree5.mapRows (rowsIn 76 86)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R7 : (evalO2 (nfTree5.mapRows (rowsIn 86 98)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R8 : (evalO2 (nfTree5.mapRows (rowsIn 98 112)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R9 : (evalO2 (nfTree5.mapRows (rowsIn 112 122)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R10 : (evalO2 (nfTree5.mapRows (rowsIn 122 131)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R11 : (evalO2 (nfTree5.mapRows (rowsIn 131 139)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R12 : (evalO2 (nfTree5.mapRows (rowsIn 139 148)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R13 : (evalO2 (nfTree5.mapRows (rowsIn 148 160)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R14 : (evalO2 (nfTree5.mapRows (rowsIn 160 174)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R15 : (evalO2 (nfTree5.mapRows (rowsIn 174 183)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R16 : (evalO2 (nfTree5.mapRows (rowsIn 183 196)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R17 : (evalO2 (nfTree5.mapRows (rowsIn 196 211)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R18 : (evalO2 (nfTree5.mapRows (rowsIn 211 220)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_R19 : (evalO2 (nfTree5.mapRows (rowsIn 220 225)) nfTree4b e1_F4X_1_8).allZero = true := by decide +kernel
theorem e1_F4X_1_8_B : wsum e1_F4X_1_8 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_F4X_1_8_T : e1_F4X_1_8.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
