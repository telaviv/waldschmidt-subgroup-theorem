import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table5
import LSG.Jac.Data.E1
import LSG.Jac.CheckerRange

/-! GENERATED — equivariance identities `E40` (law 0, `X`-flow, output chart 0), j = 1, split by
`X`-slot ranges `rs_e1_E40_1_<l>` (adaptive, `scripts/jac/e1_cost.py`, budget 50000). -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

def rs_e1_E40_1_1 : List (Nat × Nat) := [(0, 46), (46, 83), (83, 122), (122, 151), (151, 178), (178, 202), (202, 225)]
noncomputable def e1_E40_1_1 : List Term := [⟨2, false, law 0 0, DA_X0W4_1_1⟩, ⟨2, true, law 1 0, DA_X0W4_1_0⟩, ⟨8, true, shiftX 4 (law 0 0), law 5 0⟩]
theorem e1_E40_1_1_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 46)) nfTree4b e1_E40_1_1).allZero = true := by decide +kernel
theorem e1_E40_1_1_R1 : (evalO2 (nfTree5.mapRows (rowsIn 46 83)) nfTree4b e1_E40_1_1).allZero = true := by decide +kernel
theorem e1_E40_1_1_R2 : (evalO2 (nfTree5.mapRows (rowsIn 83 122)) nfTree4b e1_E40_1_1).allZero = true := by decide +kernel
theorem e1_E40_1_1_R3 : (evalO2 (nfTree5.mapRows (rowsIn 122 151)) nfTree4b e1_E40_1_1).allZero = true := by decide +kernel
theorem e1_E40_1_1_R4 : (evalO2 (nfTree5.mapRows (rowsIn 151 178)) nfTree4b e1_E40_1_1).allZero = true := by decide +kernel
theorem e1_E40_1_1_R5 : (evalO2 (nfTree5.mapRows (rowsIn 178 202)) nfTree4b e1_E40_1_1).allZero = true := by decide +kernel
theorem e1_E40_1_1_R6 : (evalO2 (nfTree5.mapRows (rowsIn 202 225)) nfTree4b e1_E40_1_1).allZero = true := by decide +kernel
theorem e1_E40_1_1_B : wsum e1_E40_1_1 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_1_1_T : e1_E40_1_1.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_1_2 : List (Nat × Nat) := [(0, 45), (45, 77), (77, 111), (111, 142), (142, 167), (167, 190), (190, 216), (216, 225)]
noncomputable def e1_E40_1_2 : List Term := [⟨2, false, law 0 0, DA_X0W4_1_2⟩, ⟨2, true, law 2 0, DA_X0W4_1_0⟩, ⟨8, true, shiftX 4 (law 0 0), law 6 0⟩]
theorem e1_E40_1_2_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 45)) nfTree4b e1_E40_1_2).allZero = true := by decide +kernel
theorem e1_E40_1_2_R1 : (evalO2 (nfTree5.mapRows (rowsIn 45 77)) nfTree4b e1_E40_1_2).allZero = true := by decide +kernel
theorem e1_E40_1_2_R2 : (evalO2 (nfTree5.mapRows (rowsIn 77 111)) nfTree4b e1_E40_1_2).allZero = true := by decide +kernel
theorem e1_E40_1_2_R3 : (evalO2 (nfTree5.mapRows (rowsIn 111 142)) nfTree4b e1_E40_1_2).allZero = true := by decide +kernel
theorem e1_E40_1_2_R4 : (evalO2 (nfTree5.mapRows (rowsIn 142 167)) nfTree4b e1_E40_1_2).allZero = true := by decide +kernel
theorem e1_E40_1_2_R5 : (evalO2 (nfTree5.mapRows (rowsIn 167 190)) nfTree4b e1_E40_1_2).allZero = true := by decide +kernel
theorem e1_E40_1_2_R6 : (evalO2 (nfTree5.mapRows (rowsIn 190 216)) nfTree4b e1_E40_1_2).allZero = true := by decide +kernel
theorem e1_E40_1_2_R7 : (evalO2 (nfTree5.mapRows (rowsIn 216 225)) nfTree4b e1_E40_1_2).allZero = true := by decide +kernel
theorem e1_E40_1_2_B : wsum e1_E40_1_2 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_1_2_T : e1_E40_1_2.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_1_3 : List (Nat × Nat) := [(0, 42), (42, 66), (66, 97), (97, 126), (126, 151), (151, 177), (177, 200), (200, 225)]
noncomputable def e1_E40_1_3 : List Term := [⟨2, false, law 0 0, DA_X0W4_1_3⟩, ⟨2, true, law 3 0, DA_X0W4_1_0⟩, ⟨8, true, shiftX 4 (law 0 0), law 7 0⟩]
theorem e1_E40_1_3_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 42)) nfTree4b e1_E40_1_3).allZero = true := by decide +kernel
theorem e1_E40_1_3_R1 : (evalO2 (nfTree5.mapRows (rowsIn 42 66)) nfTree4b e1_E40_1_3).allZero = true := by decide +kernel
theorem e1_E40_1_3_R2 : (evalO2 (nfTree5.mapRows (rowsIn 66 97)) nfTree4b e1_E40_1_3).allZero = true := by decide +kernel
theorem e1_E40_1_3_R3 : (evalO2 (nfTree5.mapRows (rowsIn 97 126)) nfTree4b e1_E40_1_3).allZero = true := by decide +kernel
theorem e1_E40_1_3_R4 : (evalO2 (nfTree5.mapRows (rowsIn 126 151)) nfTree4b e1_E40_1_3).allZero = true := by decide +kernel
theorem e1_E40_1_3_R5 : (evalO2 (nfTree5.mapRows (rowsIn 151 177)) nfTree4b e1_E40_1_3).allZero = true := by decide +kernel
theorem e1_E40_1_3_R6 : (evalO2 (nfTree5.mapRows (rowsIn 177 200)) nfTree4b e1_E40_1_3).allZero = true := by decide +kernel
theorem e1_E40_1_3_R7 : (evalO2 (nfTree5.mapRows (rowsIn 200 225)) nfTree4b e1_E40_1_3).allZero = true := by decide +kernel
theorem e1_E40_1_3_B : wsum e1_E40_1_3 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_1_3_T : e1_E40_1_3.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_1_4 : List (Nat × Nat) := [(0, 42), (42, 63), (63, 86), (86, 112), (112, 131), (131, 146), (146, 167), (167, 184), (184, 211), (211, 225)]
noncomputable def e1_E40_1_4 : List Term := [⟨2, false, law 0 0, DA_X0W4_1_4⟩, ⟨2, true, law 4 0, DA_X0W4_1_0⟩, ⟨8, false, shiftX 4 (law 0 0), law 0 0⟩, ⟨48, true, shiftX 4 (law 1 0), law 2 0⟩]
theorem e1_E40_1_4_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 42)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_R1 : (evalO2 (nfTree5.mapRows (rowsIn 42 63)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_R2 : (evalO2 (nfTree5.mapRows (rowsIn 63 86)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_R3 : (evalO2 (nfTree5.mapRows (rowsIn 86 112)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_R4 : (evalO2 (nfTree5.mapRows (rowsIn 112 131)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_R5 : (evalO2 (nfTree5.mapRows (rowsIn 131 146)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_R6 : (evalO2 (nfTree5.mapRows (rowsIn 146 167)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_R7 : (evalO2 (nfTree5.mapRows (rowsIn 167 184)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_R8 : (evalO2 (nfTree5.mapRows (rowsIn 184 211)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_R9 : (evalO2 (nfTree5.mapRows (rowsIn 211 225)) nfTree4b e1_E40_1_4).allZero = true := by decide +kernel
theorem e1_E40_1_4_B : wsum e1_E40_1_4 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_1_4_T : e1_E40_1_4.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_1_5 : List (Nat × Nat) := [(0, 39), (39, 57), (57, 82), (82, 111), (111, 126), (126, 141), (141, 161), (161, 177), (177, 196), (196, 219), (219, 225)]
noncomputable def e1_E40_1_5 : List Term := [⟨2, false, law 0 0, DA_X0W4_1_5⟩, ⟨2, true, law 5 0, DA_X0W4_1_0⟩, ⟨48, true, shiftX 4 (law 1 0), law 3 0⟩, ⟨32, true, shiftX 4 (law 0 0), law 8 0⟩]
theorem e1_E40_1_5_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 39)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R1 : (evalO2 (nfTree5.mapRows (rowsIn 39 57)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R2 : (evalO2 (nfTree5.mapRows (rowsIn 57 82)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R3 : (evalO2 (nfTree5.mapRows (rowsIn 82 111)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R4 : (evalO2 (nfTree5.mapRows (rowsIn 111 126)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R5 : (evalO2 (nfTree5.mapRows (rowsIn 126 141)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R6 : (evalO2 (nfTree5.mapRows (rowsIn 141 161)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R7 : (evalO2 (nfTree5.mapRows (rowsIn 161 177)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R8 : (evalO2 (nfTree5.mapRows (rowsIn 177 196)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R9 : (evalO2 (nfTree5.mapRows (rowsIn 196 219)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_R10 : (evalO2 (nfTree5.mapRows (rowsIn 219 225)) nfTree4b e1_E40_1_5).allZero = true := by decide +kernel
theorem e1_E40_1_5_B : wsum e1_E40_1_5 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_1_5_T : e1_E40_1_5.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_1_6 : List (Nat × Nat) := [(0, 34), (34, 51), (51, 66), (66, 85), (85, 110), (110, 125), (125, 137), (137, 149), (149, 169), (169, 183), (183, 200), (200, 219), (219, 225)]
noncomputable def e1_E40_1_6 : List Term := [⟨2, false, law 0 0, DA_X0W4_1_6⟩, ⟨2, true, law 6 0, DA_X0W4_1_0⟩, ⟨16, false, shiftX 4 (law 0 0), law 1 0⟩, ⟨48, true, shiftX 4 (law 2 0), law 3 0⟩]
theorem e1_E40_1_6_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 34)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R1 : (evalO2 (nfTree5.mapRows (rowsIn 34 51)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R2 : (evalO2 (nfTree5.mapRows (rowsIn 51 66)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R3 : (evalO2 (nfTree5.mapRows (rowsIn 66 85)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R4 : (evalO2 (nfTree5.mapRows (rowsIn 85 110)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R5 : (evalO2 (nfTree5.mapRows (rowsIn 110 125)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R6 : (evalO2 (nfTree5.mapRows (rowsIn 125 137)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R7 : (evalO2 (nfTree5.mapRows (rowsIn 137 149)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R8 : (evalO2 (nfTree5.mapRows (rowsIn 149 169)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R9 : (evalO2 (nfTree5.mapRows (rowsIn 169 183)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R10 : (evalO2 (nfTree5.mapRows (rowsIn 183 200)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R11 : (evalO2 (nfTree5.mapRows (rowsIn 200 219)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_R12 : (evalO2 (nfTree5.mapRows (rowsIn 219 225)) nfTree4b e1_E40_1_6).allZero = true := by decide +kernel
theorem e1_E40_1_6_B : wsum e1_E40_1_6 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_1_6_T : e1_E40_1_6.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_1_7 : List (Nat × Nat) := [(0, 36), (36, 54), (54, 71), (71, 86), (86, 110), (110, 126), (126, 139), (139, 151), (151, 172), (172, 186), (186, 200), (200, 219), (219, 225)]
noncomputable def e1_E40_1_7 : List Term := [⟨2, false, law 0 0, DA_X0W4_1_7⟩, ⟨2, true, law 7 0, DA_X0W4_1_0⟩, ⟨32, true, shiftX 4 (law 0 0), law 2 0⟩, ⟨48, true, shiftX 4 (law 3 0), law 3 0⟩]
theorem e1_E40_1_7_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 36)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R1 : (evalO2 (nfTree5.mapRows (rowsIn 36 54)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R2 : (evalO2 (nfTree5.mapRows (rowsIn 54 71)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R3 : (evalO2 (nfTree5.mapRows (rowsIn 71 86)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R4 : (evalO2 (nfTree5.mapRows (rowsIn 86 110)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R5 : (evalO2 (nfTree5.mapRows (rowsIn 110 126)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R6 : (evalO2 (nfTree5.mapRows (rowsIn 126 139)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R7 : (evalO2 (nfTree5.mapRows (rowsIn 139 151)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R8 : (evalO2 (nfTree5.mapRows (rowsIn 151 172)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R9 : (evalO2 (nfTree5.mapRows (rowsIn 172 186)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R10 : (evalO2 (nfTree5.mapRows (rowsIn 186 200)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R11 : (evalO2 (nfTree5.mapRows (rowsIn 200 219)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_R12 : (evalO2 (nfTree5.mapRows (rowsIn 219 225)) nfTree4b e1_E40_1_7).allZero = true := by decide +kernel
theorem e1_E40_1_7_B : wsum e1_E40_1_7 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_1_7_T : e1_E40_1_7.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_1_8 : List (Nat × Nat) := [(0, 30), (30, 47), (47, 63), (63, 80), (80, 96), (96, 120), (120, 131), (131, 141), (141, 160), (160, 176), (176, 195), (195, 215), (215, 225)]
noncomputable def e1_E40_1_8 : List Term := [⟨2, false, law 0 0, DA_X0W4_1_8⟩, ⟨2, true, law 8 0, DA_X0W4_1_0⟩, ⟨4, false, shiftX 4 (law 0 0), law 4 0⟩, ⟨12, true, shiftX 4 (law 2 0), law 6 0⟩, ⟨12, false, shiftX 4 (law 1 0), law 7 0⟩]
theorem e1_E40_1_8_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 30)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R1 : (evalO2 (nfTree5.mapRows (rowsIn 30 47)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R2 : (evalO2 (nfTree5.mapRows (rowsIn 47 63)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R3 : (evalO2 (nfTree5.mapRows (rowsIn 63 80)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R4 : (evalO2 (nfTree5.mapRows (rowsIn 80 96)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R5 : (evalO2 (nfTree5.mapRows (rowsIn 96 120)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R6 : (evalO2 (nfTree5.mapRows (rowsIn 120 131)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R7 : (evalO2 (nfTree5.mapRows (rowsIn 131 141)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R8 : (evalO2 (nfTree5.mapRows (rowsIn 141 160)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R9 : (evalO2 (nfTree5.mapRows (rowsIn 160 176)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R10 : (evalO2 (nfTree5.mapRows (rowsIn 176 195)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R11 : (evalO2 (nfTree5.mapRows (rowsIn 195 215)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_R12 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_E40_1_8).allZero = true := by decide +kernel
theorem e1_E40_1_8_B : wsum e1_E40_1_8 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_1_8_T : e1_E40_1_8.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
