import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table5
import LSG.Jac.Data.E1
import LSG.Jac.CheckerRange

/-! GENERATED — equivariance identities `E04` (law 0, `X`-flow, output chart 4), j = 1, split by
`X`-slot ranges `rs_e1_E04_1_<l>` (adaptive, `scripts/jac/e1_cost.py`, budget 50000). -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

def rs_e1_E04_1_0 : List (Nat × Nat) := [(0, 62), (62, 124), (124, 171), (171, 217), (217, 225)]
noncomputable def e1_E04_1_0 : List Term := [⟨4, false, law 4 0, DA_X0W_1_0⟩, ⟨4, true, law 0 0, DA_X0W_1_4⟩, ⟨8, true, shiftX 0 (law 0 0), law 0 0⟩, ⟨48, false, shiftX 0 (law 1 0), law 2 0⟩]
theorem e1_E04_1_0_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 62)) nfTree4b e1_E04_1_0).allZero = true := by decide +kernel
theorem e1_E04_1_0_R1 : (evalO2 (nfTree5.mapRows (rowsIn 62 124)) nfTree4b e1_E04_1_0).allZero = true := by decide +kernel
theorem e1_E04_1_0_R2 : (evalO2 (nfTree5.mapRows (rowsIn 124 171)) nfTree4b e1_E04_1_0).allZero = true := by decide +kernel
theorem e1_E04_1_0_R3 : (evalO2 (nfTree5.mapRows (rowsIn 171 217)) nfTree4b e1_E04_1_0).allZero = true := by decide +kernel
theorem e1_E04_1_0_R4 : (evalO2 (nfTree5.mapRows (rowsIn 217 225)) nfTree4b e1_E04_1_0).allZero = true := by decide +kernel
theorem e1_E04_1_0_B : wsum e1_E04_1_0 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_1_0_T : e1_E04_1_0.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_1_1 : List (Nat × Nat) := [(0, 24), (24, 34), (34, 47), (47, 58), (58, 72), (72, 85), (85, 100), (100, 121), (121, 132), (132, 141), (141, 157), (157, 174), (174, 185), (185, 199), (199, 215), (215, 225)]
noncomputable def e1_E04_1_1 : List Term := [⟨4, false, law 4 0, DA_X0W_1_1⟩, ⟨4, true, law 1 0, DA_X0W_1_4⟩, ⟨16, false, shiftX 0 (law 0 0), law 1 0⟩, ⟨12, false, shiftX 0 (law 2 0), law 3 0⟩, ⟨4, false, shiftX 0 (law 4 0), law 5 0⟩]
theorem e1_E04_1_1_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 34)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R2 : (evalO2 (nfTree5.mapRows (rowsIn 34 47)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R3 : (evalO2 (nfTree5.mapRows (rowsIn 47 58)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R4 : (evalO2 (nfTree5.mapRows (rowsIn 58 72)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R5 : (evalO2 (nfTree5.mapRows (rowsIn 72 85)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R6 : (evalO2 (nfTree5.mapRows (rowsIn 85 100)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R7 : (evalO2 (nfTree5.mapRows (rowsIn 100 121)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R8 : (evalO2 (nfTree5.mapRows (rowsIn 121 132)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R9 : (evalO2 (nfTree5.mapRows (rowsIn 132 141)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R10 : (evalO2 (nfTree5.mapRows (rowsIn 141 157)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R11 : (evalO2 (nfTree5.mapRows (rowsIn 157 174)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R12 : (evalO2 (nfTree5.mapRows (rowsIn 174 185)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R13 : (evalO2 (nfTree5.mapRows (rowsIn 185 199)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R14 : (evalO2 (nfTree5.mapRows (rowsIn 199 215)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_R15 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_E04_1_1).allZero = true := by decide +kernel
theorem e1_E04_1_1_B : wsum e1_E04_1_1 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_1_1_T : e1_E04_1_1.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_1_2 : List (Nat × Nat) := [(0, 22), (22, 31), (31, 41), (41, 48), (48, 57), (57, 67), (67, 77), (77, 88), (88, 99), (99, 117), (117, 123), (123, 133), (133, 140), (140, 150), (150, 164), (164, 175), (175, 185), (185, 196), (196, 212), (212, 225)]
noncomputable def e1_E04_1_2 : List Term := [⟨4, false, law 4 0, DA_X0W_1_2⟩, ⟨4, true, law 2 0, DA_X0W_1_4⟩, ⟨4, false, shiftX 0 (law 0 0), law 2 0⟩, ⟨24, false, shiftX 0 (law 3 0), law 3 0⟩, ⟨4, false, shiftX 0 (law 4 0), law 6 0⟩, ⟨24, false, shiftX 0 (law 1 0), law 8 0⟩]
theorem e1_E04_1_2_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 22)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R1 : (evalO2 (nfTree5.mapRows (rowsIn 22 31)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R2 : (evalO2 (nfTree5.mapRows (rowsIn 31 41)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R3 : (evalO2 (nfTree5.mapRows (rowsIn 41 48)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R4 : (evalO2 (nfTree5.mapRows (rowsIn 48 57)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R5 : (evalO2 (nfTree5.mapRows (rowsIn 57 67)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R6 : (evalO2 (nfTree5.mapRows (rowsIn 67 77)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R7 : (evalO2 (nfTree5.mapRows (rowsIn 77 88)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R8 : (evalO2 (nfTree5.mapRows (rowsIn 88 99)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R9 : (evalO2 (nfTree5.mapRows (rowsIn 99 117)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R10 : (evalO2 (nfTree5.mapRows (rowsIn 117 123)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R11 : (evalO2 (nfTree5.mapRows (rowsIn 123 133)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R12 : (evalO2 (nfTree5.mapRows (rowsIn 133 140)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R13 : (evalO2 (nfTree5.mapRows (rowsIn 140 150)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R14 : (evalO2 (nfTree5.mapRows (rowsIn 150 164)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R15 : (evalO2 (nfTree5.mapRows (rowsIn 164 175)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R16 : (evalO2 (nfTree5.mapRows (rowsIn 175 185)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R17 : (evalO2 (nfTree5.mapRows (rowsIn 185 196)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R18 : (evalO2 (nfTree5.mapRows (rowsIn 196 212)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_R19 : (evalO2 (nfTree5.mapRows (rowsIn 212 225)) nfTree4b e1_E04_1_2).allZero = true := by decide +kernel
theorem e1_E04_1_2_B : wsum e1_E04_1_2 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_1_2_T : e1_E04_1_2.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_1_3 : List (Nat × Nat) := [(0, 22), (22, 31), (31, 41), (41, 48), (48, 57), (57, 67), (67, 77), (77, 88), (88, 99), (99, 117), (117, 123), (123, 133), (133, 140), (140, 150), (150, 164), (164, 175), (175, 185), (185, 196), (196, 212), (212, 225)]
noncomputable def e1_E04_1_3 : List Term := [⟨4, false, law 4 0, DA_X0W_1_3⟩, ⟨4, true, law 3 0, DA_X0W_1_4⟩, ⟨48, false, shiftX 0 (law 1 0), law 1 0⟩, ⟨8, true, shiftX 0 (law 0 0), law 3 0⟩, ⟨4, false, shiftX 0 (law 4 0), law 7 0⟩, ⟨24, false, shiftX 0 (law 2 0), law 8 0⟩]
theorem e1_E04_1_3_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 22)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R1 : (evalO2 (nfTree5.mapRows (rowsIn 22 31)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R2 : (evalO2 (nfTree5.mapRows (rowsIn 31 41)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R3 : (evalO2 (nfTree5.mapRows (rowsIn 41 48)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R4 : (evalO2 (nfTree5.mapRows (rowsIn 48 57)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R5 : (evalO2 (nfTree5.mapRows (rowsIn 57 67)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R6 : (evalO2 (nfTree5.mapRows (rowsIn 67 77)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R7 : (evalO2 (nfTree5.mapRows (rowsIn 77 88)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R8 : (evalO2 (nfTree5.mapRows (rowsIn 88 99)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R9 : (evalO2 (nfTree5.mapRows (rowsIn 99 117)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R10 : (evalO2 (nfTree5.mapRows (rowsIn 117 123)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R11 : (evalO2 (nfTree5.mapRows (rowsIn 123 133)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R12 : (evalO2 (nfTree5.mapRows (rowsIn 133 140)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R13 : (evalO2 (nfTree5.mapRows (rowsIn 140 150)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R14 : (evalO2 (nfTree5.mapRows (rowsIn 150 164)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R15 : (evalO2 (nfTree5.mapRows (rowsIn 164 175)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R16 : (evalO2 (nfTree5.mapRows (rowsIn 175 185)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R17 : (evalO2 (nfTree5.mapRows (rowsIn 185 196)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R18 : (evalO2 (nfTree5.mapRows (rowsIn 196 212)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_R19 : (evalO2 (nfTree5.mapRows (rowsIn 212 225)) nfTree4b e1_E04_1_3).allZero = true := by decide +kernel
theorem e1_E04_1_3_B : wsum e1_E04_1_3 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_1_3_T : e1_E04_1_3.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_1_5 : List (Nat × Nat) := [(0, 23), (23, 33), (33, 44), (44, 57), (57, 70), (70, 83), (83, 99), (99, 120), (120, 127), (127, 139), (139, 150), (150, 164), (164, 176), (176, 187), (187, 199), (199, 214), (214, 225)]
noncomputable def e1_E04_1_5 : List Term := [⟨4, false, law 4 0, DA_X0W_1_5⟩, ⟨4, true, law 5 0, DA_X0W_1_4⟩, ⟨8, true, shiftX 0 (law 0 0), law 5 0⟩, ⟨24, false, shiftX 0 (law 2 0), law 7 0⟩, ⟨16, false, shiftX 0 (law 4 0), law 8 0⟩]
theorem e1_E04_1_5_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 33)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R2 : (evalO2 (nfTree5.mapRows (rowsIn 33 44)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R3 : (evalO2 (nfTree5.mapRows (rowsIn 44 57)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 70)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R5 : (evalO2 (nfTree5.mapRows (rowsIn 70 83)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R6 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R7 : (evalO2 (nfTree5.mapRows (rowsIn 99 120)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R8 : (evalO2 (nfTree5.mapRows (rowsIn 120 127)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R9 : (evalO2 (nfTree5.mapRows (rowsIn 127 139)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R10 : (evalO2 (nfTree5.mapRows (rowsIn 139 150)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R11 : (evalO2 (nfTree5.mapRows (rowsIn 150 164)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R12 : (evalO2 (nfTree5.mapRows (rowsIn 164 176)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R13 : (evalO2 (nfTree5.mapRows (rowsIn 176 187)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R14 : (evalO2 (nfTree5.mapRows (rowsIn 187 199)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R15 : (evalO2 (nfTree5.mapRows (rowsIn 199 214)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_R16 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_E04_1_5).allZero = true := by decide +kernel
theorem e1_E04_1_5_B : wsum e1_E04_1_5 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_1_5_T : e1_E04_1_5.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_1_6 : List (Nat × Nat) := [(0, 21), (21, 28), (28, 39), (39, 45), (45, 55), (55, 65), (65, 75), (75, 85), (85, 96), (96, 111), (111, 121), (121, 127), (127, 137), (137, 142), (142, 150), (150, 161), (161, 172), (172, 182), (182, 195), (195, 206), (206, 215), (215, 225)]
noncomputable def e1_E04_1_6 : List Term := [⟨4, false, law 4 0, DA_X0W_1_6⟩, ⟨4, true, law 6 0, DA_X0W_1_4⟩, ⟨16, false, shiftX 0 (law 1 0), law 4 0⟩, ⟨8, true, shiftX 0 (law 0 0), law 6 0⟩, ⟨12, false, shiftX 0 (law 3 0), law 7 0⟩, ⟨24, false, shiftX 0 (law 5 0), law 8 0⟩]
theorem e1_E04_1_6_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 21)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R1 : (evalO2 (nfTree5.mapRows (rowsIn 21 28)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R2 : (evalO2 (nfTree5.mapRows (rowsIn 28 39)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R3 : (evalO2 (nfTree5.mapRows (rowsIn 39 45)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R4 : (evalO2 (nfTree5.mapRows (rowsIn 45 55)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R5 : (evalO2 (nfTree5.mapRows (rowsIn 55 65)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R6 : (evalO2 (nfTree5.mapRows (rowsIn 65 75)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R7 : (evalO2 (nfTree5.mapRows (rowsIn 75 85)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R8 : (evalO2 (nfTree5.mapRows (rowsIn 85 96)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R9 : (evalO2 (nfTree5.mapRows (rowsIn 96 111)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R10 : (evalO2 (nfTree5.mapRows (rowsIn 111 121)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R11 : (evalO2 (nfTree5.mapRows (rowsIn 121 127)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R12 : (evalO2 (nfTree5.mapRows (rowsIn 127 137)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R13 : (evalO2 (nfTree5.mapRows (rowsIn 137 142)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R14 : (evalO2 (nfTree5.mapRows (rowsIn 142 150)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R15 : (evalO2 (nfTree5.mapRows (rowsIn 150 161)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R16 : (evalO2 (nfTree5.mapRows (rowsIn 161 172)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R17 : (evalO2 (nfTree5.mapRows (rowsIn 172 182)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R18 : (evalO2 (nfTree5.mapRows (rowsIn 182 195)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R19 : (evalO2 (nfTree5.mapRows (rowsIn 195 206)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R20 : (evalO2 (nfTree5.mapRows (rowsIn 206 215)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_R21 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_E04_1_6).allZero = true := by decide +kernel
theorem e1_E04_1_6_B : wsum e1_E04_1_6 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_1_6_T : e1_E04_1_6.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_1_7 : List (Nat × Nat) := [(0, 23), (23, 33), (33, 43), (43, 56), (56, 67), (67, 77), (77, 91), (91, 100), (100, 120), (120, 127), (127, 137), (137, 147), (147, 161), (161, 174), (174, 183), (183, 196), (196, 214), (214, 225)]
noncomputable def e1_E04_1_7 : List Term := [⟨4, false, law 4 0, DA_X0W_1_7⟩, ⟨4, true, law 7 0, DA_X0W_1_4⟩, ⟨64, false, shiftX 0 (law 1 0), law 5 0⟩, ⟨4, true, shiftX 0 (law 0 0), law 7 0⟩, ⟨24, false, shiftX 0 (law 6 0), law 8 0⟩]
theorem e1_E04_1_7_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 33)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R2 : (evalO2 (nfTree5.mapRows (rowsIn 33 43)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R3 : (evalO2 (nfTree5.mapRows (rowsIn 43 56)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R4 : (evalO2 (nfTree5.mapRows (rowsIn 56 67)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R5 : (evalO2 (nfTree5.mapRows (rowsIn 67 77)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R6 : (evalO2 (nfTree5.mapRows (rowsIn 77 91)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R7 : (evalO2 (nfTree5.mapRows (rowsIn 91 100)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R8 : (evalO2 (nfTree5.mapRows (rowsIn 100 120)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R9 : (evalO2 (nfTree5.mapRows (rowsIn 120 127)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R10 : (evalO2 (nfTree5.mapRows (rowsIn 127 137)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R11 : (evalO2 (nfTree5.mapRows (rowsIn 137 147)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R12 : (evalO2 (nfTree5.mapRows (rowsIn 147 161)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R13 : (evalO2 (nfTree5.mapRows (rowsIn 161 174)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R14 : (evalO2 (nfTree5.mapRows (rowsIn 174 183)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R15 : (evalO2 (nfTree5.mapRows (rowsIn 183 196)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R16 : (evalO2 (nfTree5.mapRows (rowsIn 196 214)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_R17 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_E04_1_7).allZero = true := by decide +kernel
theorem e1_E04_1_7_B : wsum e1_E04_1_7 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_1_7_T : e1_E04_1_7.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_1_8 : List (Nat × Nat) := [(0, 22), (22, 31), (31, 41), (41, 48), (48, 57), (57, 67), (67, 77), (77, 87), (87, 97), (97, 112), (112, 122), (122, 131), (131, 139), (139, 148), (148, 161), (161, 174), (174, 183), (183, 196), (196, 210), (210, 220), (220, 225)]
noncomputable def e1_E04_1_8 : List Term := [⟨4, false, law 4 0, DA_X0W_1_8⟩, ⟨4, true, law 8 0, DA_X0W_1_4⟩, ⟨24, true, shiftX 0 (law 1 0), law 3 0⟩, ⟨8, true, shiftX 0 (law 4 0), law 4 0⟩, ⟨6, false, shiftX 0 (law 6 0), law 7 0⟩, ⟨4, false, shiftX 0 (law 0 0), law 8 0⟩]
theorem e1_E04_1_8_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 22)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R1 : (evalO2 (nfTree5.mapRows (rowsIn 22 31)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R2 : (evalO2 (nfTree5.mapRows (rowsIn 31 41)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R3 : (evalO2 (nfTree5.mapRows (rowsIn 41 48)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R4 : (evalO2 (nfTree5.mapRows (rowsIn 48 57)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R5 : (evalO2 (nfTree5.mapRows (rowsIn 57 67)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R6 : (evalO2 (nfTree5.mapRows (rowsIn 67 77)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R7 : (evalO2 (nfTree5.mapRows (rowsIn 77 87)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R8 : (evalO2 (nfTree5.mapRows (rowsIn 87 97)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R9 : (evalO2 (nfTree5.mapRows (rowsIn 97 112)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R10 : (evalO2 (nfTree5.mapRows (rowsIn 112 122)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R11 : (evalO2 (nfTree5.mapRows (rowsIn 122 131)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R12 : (evalO2 (nfTree5.mapRows (rowsIn 131 139)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R13 : (evalO2 (nfTree5.mapRows (rowsIn 139 148)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R14 : (evalO2 (nfTree5.mapRows (rowsIn 148 161)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R15 : (evalO2 (nfTree5.mapRows (rowsIn 161 174)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R16 : (evalO2 (nfTree5.mapRows (rowsIn 174 183)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R17 : (evalO2 (nfTree5.mapRows (rowsIn 183 196)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R18 : (evalO2 (nfTree5.mapRows (rowsIn 196 210)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R19 : (evalO2 (nfTree5.mapRows (rowsIn 210 220)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_R20 : (evalO2 (nfTree5.mapRows (rowsIn 220 225)) nfTree4b e1_E04_1_8).allZero = true := by decide +kernel
theorem e1_E04_1_8_B : wsum e1_E04_1_8 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_1_8_T : e1_E04_1_8.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
