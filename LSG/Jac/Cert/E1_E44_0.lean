import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table5
import LSG.Jac.Data.E1
import LSG.Jac.CheckerRange

/-! GENERATED — equivariance identities `E44` (law 0, `X`-flow, output chart 4), j = 0, split by
`X`-slot ranges `rs_e1_E44_0_<l>` (adaptive, `scripts/jac/e1_cost.py`, budget 50000). -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

def rs_e1_E44_0_0 : List (Nat × Nat) := [(0, 42), (42, 63), (63, 87), (87, 112), (112, 133), (133, 150), (150, 175), (175, 196), (196, 220), (220, 225)]
noncomputable def e1_E44_0_0 : List Term := [⟨4, false, law 4 0, DA_X0W4_0_0⟩, ⟨4, true, law 0 0, DA_X0W4_0_4⟩, ⟨96, false, shiftX 4 (law 1 0), law 1 0⟩, ⟨48, true, shiftX 4 (law 0 0), law 3 0⟩]
theorem e1_E44_0_0_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 42)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_R1 : (evalO2 (nfTree5.mapRows (rowsIn 42 63)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_R2 : (evalO2 (nfTree5.mapRows (rowsIn 63 87)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_R3 : (evalO2 (nfTree5.mapRows (rowsIn 87 112)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_R4 : (evalO2 (nfTree5.mapRows (rowsIn 112 133)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_R5 : (evalO2 (nfTree5.mapRows (rowsIn 133 150)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_R6 : (evalO2 (nfTree5.mapRows (rowsIn 150 175)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_R7 : (evalO2 (nfTree5.mapRows (rowsIn 175 196)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_R8 : (evalO2 (nfTree5.mapRows (rowsIn 196 220)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_R9 : (evalO2 (nfTree5.mapRows (rowsIn 220 225)) nfTree4b e1_E44_0_0).allZero = true := by decide +kernel
theorem e1_E44_0_0_B : wsum e1_E44_0_0 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E44_0_0_T : e1_E44_0_0.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E44_0_1 : List (Nat × Nat) := [(0, 24), (24, 34), (34, 45), (45, 57), (57, 67), (67, 77), (77, 87), (87, 99), (99, 114), (114, 123), (123, 132), (132, 139), (139, 148), (148, 161), (161, 174), (174, 183), (183, 196), (196, 211), (211, 221), (221, 225)]
noncomputable def e1_E44_0_1 : List Term := [⟨4, false, law 4 0, DA_X0W4_0_1⟩, ⟨4, true, law 1 0, DA_X0W4_0_4⟩, ⟨24, false, shiftX 4 (law 1 0), law 3 0⟩, ⟨8, false, shiftX 4 (law 4 0), law 4 0⟩, ⟨24, true, shiftX 4 (law 0 0), law 8 0⟩]
theorem e1_E44_0_1_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 34)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R2 : (evalO2 (nfTree5.mapRows (rowsIn 34 45)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R3 : (evalO2 (nfTree5.mapRows (rowsIn 45 57)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 67)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R5 : (evalO2 (nfTree5.mapRows (rowsIn 67 77)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R6 : (evalO2 (nfTree5.mapRows (rowsIn 77 87)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R7 : (evalO2 (nfTree5.mapRows (rowsIn 87 99)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R8 : (evalO2 (nfTree5.mapRows (rowsIn 99 114)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R9 : (evalO2 (nfTree5.mapRows (rowsIn 114 123)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R10 : (evalO2 (nfTree5.mapRows (rowsIn 123 132)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R11 : (evalO2 (nfTree5.mapRows (rowsIn 132 139)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R12 : (evalO2 (nfTree5.mapRows (rowsIn 139 148)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R13 : (evalO2 (nfTree5.mapRows (rowsIn 148 161)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R14 : (evalO2 (nfTree5.mapRows (rowsIn 161 174)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R15 : (evalO2 (nfTree5.mapRows (rowsIn 174 183)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R16 : (evalO2 (nfTree5.mapRows (rowsIn 183 196)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R17 : (evalO2 (nfTree5.mapRows (rowsIn 196 211)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R18 : (evalO2 (nfTree5.mapRows (rowsIn 211 221)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_R19 : (evalO2 (nfTree5.mapRows (rowsIn 221 225)) nfTree4b e1_E44_0_1).allZero = true := by decide +kernel
theorem e1_E44_0_1_B : wsum e1_E44_0_1 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E44_0_1_T : e1_E44_0_1.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E44_0_2 : List (Nat × Nat) := [(0, 24), (24, 34), (34, 45), (45, 56), (56, 67), (67, 77), (77, 87), (87, 99), (99, 113), (113, 123), (123, 132), (132, 139), (139, 148), (148, 161), (161, 174), (174, 183), (183, 196), (196, 210), (210, 220), (220, 225)]
noncomputable def e1_E44_0_2 : List Term := [⟨4, false, law 4 0, DA_X0W4_0_2⟩, ⟨4, true, law 2 0, DA_X0W4_0_4⟩, ⟨48, false, shiftX 4 (law 0 0), law 1 0⟩, ⟨24, true, shiftX 4 (law 2 0), law 3 0⟩, ⟨8, false, shiftX 4 (law 4 0), law 5 0⟩]
theorem e1_E44_0_2_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 34)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R2 : (evalO2 (nfTree5.mapRows (rowsIn 34 45)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R3 : (evalO2 (nfTree5.mapRows (rowsIn 45 56)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R4 : (evalO2 (nfTree5.mapRows (rowsIn 56 67)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R5 : (evalO2 (nfTree5.mapRows (rowsIn 67 77)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R6 : (evalO2 (nfTree5.mapRows (rowsIn 77 87)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R7 : (evalO2 (nfTree5.mapRows (rowsIn 87 99)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R8 : (evalO2 (nfTree5.mapRows (rowsIn 99 113)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R9 : (evalO2 (nfTree5.mapRows (rowsIn 113 123)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R10 : (evalO2 (nfTree5.mapRows (rowsIn 123 132)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R11 : (evalO2 (nfTree5.mapRows (rowsIn 132 139)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R12 : (evalO2 (nfTree5.mapRows (rowsIn 139 148)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R13 : (evalO2 (nfTree5.mapRows (rowsIn 148 161)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R14 : (evalO2 (nfTree5.mapRows (rowsIn 161 174)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R15 : (evalO2 (nfTree5.mapRows (rowsIn 174 183)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R16 : (evalO2 (nfTree5.mapRows (rowsIn 183 196)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R17 : (evalO2 (nfTree5.mapRows (rowsIn 196 210)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R18 : (evalO2 (nfTree5.mapRows (rowsIn 210 220)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_R19 : (evalO2 (nfTree5.mapRows (rowsIn 220 225)) nfTree4b e1_E44_0_2).allZero = true := by decide +kernel
theorem e1_E44_0_2_B : wsum e1_E44_0_2 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E44_0_2_T : e1_E44_0_2.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E44_0_3 : List (Nat × Nat) := [(0, 23), (23, 33), (33, 43), (43, 55), (55, 64), (64, 75), (75, 85), (85, 96), (96, 111), (111, 121), (121, 127), (127, 136), (136, 142), (142, 150), (150, 161), (161, 171), (171, 177), (177, 186), (186, 196), (196, 207), (207, 215), (215, 225)]
noncomputable def e1_E44_0_3 : List Term := [⟨4, false, law 4 0, DA_X0W4_0_3⟩, ⟨4, true, law 3 0, DA_X0W4_0_4⟩, ⟨24, false, shiftX 4 (law 0 0), law 2 0⟩, ⟨8, false, shiftX 4 (law 4 0), law 6 0⟩, ⟨48, true, shiftX 4 (law 1 0), law 8 0⟩]
theorem e1_E44_0_3_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 33)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R2 : (evalO2 (nfTree5.mapRows (rowsIn 33 43)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R3 : (evalO2 (nfTree5.mapRows (rowsIn 43 55)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R4 : (evalO2 (nfTree5.mapRows (rowsIn 55 64)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R5 : (evalO2 (nfTree5.mapRows (rowsIn 64 75)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R6 : (evalO2 (nfTree5.mapRows (rowsIn 75 85)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R7 : (evalO2 (nfTree5.mapRows (rowsIn 85 96)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R8 : (evalO2 (nfTree5.mapRows (rowsIn 96 111)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R9 : (evalO2 (nfTree5.mapRows (rowsIn 111 121)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R10 : (evalO2 (nfTree5.mapRows (rowsIn 121 127)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R11 : (evalO2 (nfTree5.mapRows (rowsIn 127 136)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R12 : (evalO2 (nfTree5.mapRows (rowsIn 136 142)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R13 : (evalO2 (nfTree5.mapRows (rowsIn 142 150)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R14 : (evalO2 (nfTree5.mapRows (rowsIn 150 161)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R15 : (evalO2 (nfTree5.mapRows (rowsIn 161 171)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R16 : (evalO2 (nfTree5.mapRows (rowsIn 171 177)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R17 : (evalO2 (nfTree5.mapRows (rowsIn 177 186)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R18 : (evalO2 (nfTree5.mapRows (rowsIn 186 196)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R19 : (evalO2 (nfTree5.mapRows (rowsIn 196 207)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R20 : (evalO2 (nfTree5.mapRows (rowsIn 207 215)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_R21 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_E44_0_3).allZero = true := by decide +kernel
theorem e1_E44_0_3_B : wsum e1_E44_0_3 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E44_0_3_T : e1_E44_0_3.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E44_0_5 : List (Nat × Nat) := [(0, 23), (23, 33), (33, 43), (43, 55), (55, 64), (64, 75), (75, 85), (85, 96), (96, 111), (111, 121), (121, 127), (127, 136), (136, 142), (142, 150), (150, 161), (161, 171), (171, 177), (177, 186), (186, 196), (196, 206), (206, 214), (214, 225)]
noncomputable def e1_E44_0_5 : List Term := [⟨4, false, law 4 0, DA_X0W4_0_5⟩, ⟨4, true, law 5 0, DA_X0W4_0_4⟩, ⟨8, true, shiftX 4 (law 0 0), law 4 0⟩, ⟨24, true, shiftX 4 (law 2 0), law 6 0⟩, ⟨24, false, shiftX 4 (law 1 0), law 7 0⟩]
theorem e1_E44_0_5_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 33)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R2 : (evalO2 (nfTree5.mapRows (rowsIn 33 43)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R3 : (evalO2 (nfTree5.mapRows (rowsIn 43 55)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R4 : (evalO2 (nfTree5.mapRows (rowsIn 55 64)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R5 : (evalO2 (nfTree5.mapRows (rowsIn 64 75)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R6 : (evalO2 (nfTree5.mapRows (rowsIn 75 85)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R7 : (evalO2 (nfTree5.mapRows (rowsIn 85 96)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R8 : (evalO2 (nfTree5.mapRows (rowsIn 96 111)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R9 : (evalO2 (nfTree5.mapRows (rowsIn 111 121)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R10 : (evalO2 (nfTree5.mapRows (rowsIn 121 127)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R11 : (evalO2 (nfTree5.mapRows (rowsIn 127 136)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R12 : (evalO2 (nfTree5.mapRows (rowsIn 136 142)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R13 : (evalO2 (nfTree5.mapRows (rowsIn 142 150)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R14 : (evalO2 (nfTree5.mapRows (rowsIn 150 161)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R15 : (evalO2 (nfTree5.mapRows (rowsIn 161 171)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R16 : (evalO2 (nfTree5.mapRows (rowsIn 171 177)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R17 : (evalO2 (nfTree5.mapRows (rowsIn 177 186)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R18 : (evalO2 (nfTree5.mapRows (rowsIn 186 196)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R19 : (evalO2 (nfTree5.mapRows (rowsIn 196 206)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R20 : (evalO2 (nfTree5.mapRows (rowsIn 206 214)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_R21 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_E44_0_5).allZero = true := by decide +kernel
theorem e1_E44_0_5_B : wsum e1_E44_0_5 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E44_0_5_T : e1_E44_0_5.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E44_0_6 : List (Nat × Nat) := [(0, 23), (23, 32), (32, 42), (42, 48), (48, 56), (56, 66), (66, 75), (75, 84), (84, 96), (96, 111), (111, 120), (120, 126), (126, 135), (135, 141), (141, 150), (150, 161), (161, 169), (169, 175), (175, 183), (183, 195), (195, 205), (205, 211), (211, 219), (219, 225)]
noncomputable def e1_E44_0_6 : List Term := [⟨4, false, law 4 0, DA_X0W4_0_6⟩, ⟨4, true, law 6 0, DA_X0W4_0_4⟩, ⟨48, false, shiftX 4 (law 0 0), law 5 0⟩, ⟨24, true, shiftX 4 (law 2 0), law 7 0⟩, ⟨16, true, shiftX 4 (law 4 0), law 8 0⟩]
theorem e1_E44_0_6_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 32)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R2 : (evalO2 (nfTree5.mapRows (rowsIn 32 42)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R3 : (evalO2 (nfTree5.mapRows (rowsIn 42 48)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R4 : (evalO2 (nfTree5.mapRows (rowsIn 48 56)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R5 : (evalO2 (nfTree5.mapRows (rowsIn 56 66)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R6 : (evalO2 (nfTree5.mapRows (rowsIn 66 75)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R7 : (evalO2 (nfTree5.mapRows (rowsIn 75 84)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R8 : (evalO2 (nfTree5.mapRows (rowsIn 84 96)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R9 : (evalO2 (nfTree5.mapRows (rowsIn 96 111)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R10 : (evalO2 (nfTree5.mapRows (rowsIn 111 120)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R11 : (evalO2 (nfTree5.mapRows (rowsIn 120 126)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R12 : (evalO2 (nfTree5.mapRows (rowsIn 126 135)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R13 : (evalO2 (nfTree5.mapRows (rowsIn 135 141)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R14 : (evalO2 (nfTree5.mapRows (rowsIn 141 150)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R15 : (evalO2 (nfTree5.mapRows (rowsIn 150 161)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R16 : (evalO2 (nfTree5.mapRows (rowsIn 161 169)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R17 : (evalO2 (nfTree5.mapRows (rowsIn 169 175)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R18 : (evalO2 (nfTree5.mapRows (rowsIn 175 183)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R19 : (evalO2 (nfTree5.mapRows (rowsIn 183 195)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R20 : (evalO2 (nfTree5.mapRows (rowsIn 195 205)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R21 : (evalO2 (nfTree5.mapRows (rowsIn 205 211)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R22 : (evalO2 (nfTree5.mapRows (rowsIn 211 219)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_R23 : (evalO2 (nfTree5.mapRows (rowsIn 219 225)) nfTree4b e1_E44_0_6).allZero = true := by decide +kernel
theorem e1_E44_0_6_B : wsum e1_E44_0_6 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E44_0_6_T : e1_E44_0_6.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E44_0_7 : List (Nat × Nat) := [(0, 23), (23, 32), (32, 42), (42, 48), (48, 55), (55, 64), (64, 74), (74, 83), (83, 95), (95, 110), (110, 120), (120, 126), (126, 135), (135, 140), (140, 148), (148, 160), (160, 169), (169, 175), (175, 183), (183, 195), (195, 205), (205, 211), (211, 219), (219, 225)]
noncomputable def e1_E44_0_7 : List Term := [⟨4, false, law 4 0, DA_X0W4_0_7⟩, ⟨4, true, law 7 0, DA_X0W4_0_4⟩, ⟨64, true, shiftX 4 (law 1 0), law 4 0⟩, ⟨24, false, shiftX 4 (law 3 0), law 7 0⟩, ⟨48, true, shiftX 4 (law 5 0), law 8 0⟩]
theorem e1_E44_0_7_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 32)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R2 : (evalO2 (nfTree5.mapRows (rowsIn 32 42)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R3 : (evalO2 (nfTree5.mapRows (rowsIn 42 48)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R4 : (evalO2 (nfTree5.mapRows (rowsIn 48 55)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R5 : (evalO2 (nfTree5.mapRows (rowsIn 55 64)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R6 : (evalO2 (nfTree5.mapRows (rowsIn 64 74)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R7 : (evalO2 (nfTree5.mapRows (rowsIn 74 83)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R8 : (evalO2 (nfTree5.mapRows (rowsIn 83 95)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R9 : (evalO2 (nfTree5.mapRows (rowsIn 95 110)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R10 : (evalO2 (nfTree5.mapRows (rowsIn 110 120)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R11 : (evalO2 (nfTree5.mapRows (rowsIn 120 126)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R12 : (evalO2 (nfTree5.mapRows (rowsIn 126 135)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R13 : (evalO2 (nfTree5.mapRows (rowsIn 135 140)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R14 : (evalO2 (nfTree5.mapRows (rowsIn 140 148)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R15 : (evalO2 (nfTree5.mapRows (rowsIn 148 160)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R16 : (evalO2 (nfTree5.mapRows (rowsIn 160 169)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R17 : (evalO2 (nfTree5.mapRows (rowsIn 169 175)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R18 : (evalO2 (nfTree5.mapRows (rowsIn 175 183)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R19 : (evalO2 (nfTree5.mapRows (rowsIn 183 195)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R20 : (evalO2 (nfTree5.mapRows (rowsIn 195 205)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R21 : (evalO2 (nfTree5.mapRows (rowsIn 205 211)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R22 : (evalO2 (nfTree5.mapRows (rowsIn 211 219)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_R23 : (evalO2 (nfTree5.mapRows (rowsIn 219 225)) nfTree4b e1_E44_0_7).allZero = true := by decide +kernel
theorem e1_E44_0_7_B : wsum e1_E44_0_7 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E44_0_7_T : e1_E44_0_7.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E44_0_8 : List (Nat × Nat) := [(0, 23), (23, 33), (33, 43), (43, 55), (55, 65), (65, 76), (76, 86), (86, 96), (96, 112), (112, 122), (122, 131), (131, 139), (139, 148), (148, 160), (160, 170), (170, 176), (176, 185), (185, 196), (196, 207), (207, 215), (215, 225)]
noncomputable def e1_E44_0_8 : List Term := [⟨4, false, law 4 0, DA_X0W4_0_8⟩, ⟨4, true, law 8 0, DA_X0W4_0_4⟩, ⟨96, false, shiftX 4 (law 1 0), law 2 0⟩, ⟨12, true, shiftX 4 (law 5 0), law 7 0⟩, ⟨24, false, shiftX 4 (law 3 0), law 8 0⟩]
theorem e1_E44_0_8_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 33)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R2 : (evalO2 (nfTree5.mapRows (rowsIn 33 43)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R3 : (evalO2 (nfTree5.mapRows (rowsIn 43 55)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R4 : (evalO2 (nfTree5.mapRows (rowsIn 55 65)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R5 : (evalO2 (nfTree5.mapRows (rowsIn 65 76)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R6 : (evalO2 (nfTree5.mapRows (rowsIn 76 86)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R7 : (evalO2 (nfTree5.mapRows (rowsIn 86 96)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R8 : (evalO2 (nfTree5.mapRows (rowsIn 96 112)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R9 : (evalO2 (nfTree5.mapRows (rowsIn 112 122)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R10 : (evalO2 (nfTree5.mapRows (rowsIn 122 131)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R11 : (evalO2 (nfTree5.mapRows (rowsIn 131 139)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R12 : (evalO2 (nfTree5.mapRows (rowsIn 139 148)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R13 : (evalO2 (nfTree5.mapRows (rowsIn 148 160)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R14 : (evalO2 (nfTree5.mapRows (rowsIn 160 170)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R15 : (evalO2 (nfTree5.mapRows (rowsIn 170 176)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R16 : (evalO2 (nfTree5.mapRows (rowsIn 176 185)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R17 : (evalO2 (nfTree5.mapRows (rowsIn 185 196)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R18 : (evalO2 (nfTree5.mapRows (rowsIn 196 207)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R19 : (evalO2 (nfTree5.mapRows (rowsIn 207 215)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_R20 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_E44_0_8).allZero = true := by decide +kernel
theorem e1_E44_0_8_B : wsum e1_E44_0_8 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E44_0_8_T : e1_E44_0_8.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
