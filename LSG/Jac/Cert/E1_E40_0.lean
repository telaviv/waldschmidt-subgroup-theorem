import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table5
import LSG.Jac.Data.E1
import LSG.Jac.CheckerRange

/-! GENERATED — equivariance identities `E40` (law 0, `X`-flow, output chart 0), j = 0, split by
`X`-slot ranges `rs_e1_E40_0_<l>` (adaptive, `scripts/jac/e1_cost.py`, budget 50000). -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

def rs_e1_E40_0_1 : List (Nat × Nat) := [(0, 57), (57, 110), (110, 149), (149, 188), (188, 225)]
noncomputable def e1_E40_0_1 : List Term := [⟨2, false, law 0 0, DA_X0W4_0_1⟩, ⟨2, true, law 1 0, DA_X0W4_0_0⟩, ⟨8, true, shiftX 4 (law 0 0), law 4 0⟩]
theorem e1_E40_0_1_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 57)) nfTree4b e1_E40_0_1).allZero = true := by decide +kernel
theorem e1_E40_0_1_R1 : (evalO2 (nfTree5.mapRows (rowsIn 57 110)) nfTree4b e1_E40_0_1).allZero = true := by decide +kernel
theorem e1_E40_0_1_R2 : (evalO2 (nfTree5.mapRows (rowsIn 110 149)) nfTree4b e1_E40_0_1).allZero = true := by decide +kernel
theorem e1_E40_0_1_R3 : (evalO2 (nfTree5.mapRows (rowsIn 149 188)) nfTree4b e1_E40_0_1).allZero = true := by decide +kernel
theorem e1_E40_0_1_R4 : (evalO2 (nfTree5.mapRows (rowsIn 188 225)) nfTree4b e1_E40_0_1).allZero = true := by decide +kernel
theorem e1_E40_0_1_B : wsum e1_E40_0_1 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_0_1_T : e1_E40_0_1.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_0_2 : List (Nat × Nat) := [(0, 56), (56, 102), (102, 143), (143, 181), (181, 216), (216, 225)]
noncomputable def e1_E40_0_2 : List Term := [⟨2, false, law 0 0, DA_X0W4_0_2⟩, ⟨2, true, law 2 0, DA_X0W4_0_0⟩, ⟨8, true, shiftX 4 (law 0 0), law 5 0⟩]
theorem e1_E40_0_2_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 56)) nfTree4b e1_E40_0_2).allZero = true := by decide +kernel
theorem e1_E40_0_2_R1 : (evalO2 (nfTree5.mapRows (rowsIn 56 102)) nfTree4b e1_E40_0_2).allZero = true := by decide +kernel
theorem e1_E40_0_2_R2 : (evalO2 (nfTree5.mapRows (rowsIn 102 143)) nfTree4b e1_E40_0_2).allZero = true := by decide +kernel
theorem e1_E40_0_2_R3 : (evalO2 (nfTree5.mapRows (rowsIn 143 181)) nfTree4b e1_E40_0_2).allZero = true := by decide +kernel
theorem e1_E40_0_2_R4 : (evalO2 (nfTree5.mapRows (rowsIn 181 216)) nfTree4b e1_E40_0_2).allZero = true := by decide +kernel
theorem e1_E40_0_2_R5 : (evalO2 (nfTree5.mapRows (rowsIn 216 225)) nfTree4b e1_E40_0_2).allZero = true := by decide +kernel
theorem e1_E40_0_2_B : wsum e1_E40_0_2 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_0_2_T : e1_E40_0_2.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_0_3 : List (Nat × Nat) := [(0, 47), (47, 83), (83, 121), (121, 151), (151, 177), (177, 200), (200, 225)]
noncomputable def e1_E40_0_3 : List Term := [⟨2, false, law 0 0, DA_X0W4_0_3⟩, ⟨2, true, law 3 0, DA_X0W4_0_0⟩, ⟨8, true, shiftX 4 (law 0 0), law 6 0⟩]
theorem e1_E40_0_3_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 47)) nfTree4b e1_E40_0_3).allZero = true := by decide +kernel
theorem e1_E40_0_3_R1 : (evalO2 (nfTree5.mapRows (rowsIn 47 83)) nfTree4b e1_E40_0_3).allZero = true := by decide +kernel
theorem e1_E40_0_3_R2 : (evalO2 (nfTree5.mapRows (rowsIn 83 121)) nfTree4b e1_E40_0_3).allZero = true := by decide +kernel
theorem e1_E40_0_3_R3 : (evalO2 (nfTree5.mapRows (rowsIn 121 151)) nfTree4b e1_E40_0_3).allZero = true := by decide +kernel
theorem e1_E40_0_3_R4 : (evalO2 (nfTree5.mapRows (rowsIn 151 177)) nfTree4b e1_E40_0_3).allZero = true := by decide +kernel
theorem e1_E40_0_3_R5 : (evalO2 (nfTree5.mapRows (rowsIn 177 200)) nfTree4b e1_E40_0_3).allZero = true := by decide +kernel
theorem e1_E40_0_3_R6 : (evalO2 (nfTree5.mapRows (rowsIn 200 225)) nfTree4b e1_E40_0_3).allZero = true := by decide +kernel
theorem e1_E40_0_3_B : wsum e1_E40_0_3 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_0_3_T : e1_E40_0_3.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_0_4 : List (Nat × Nat) := [(0, 42), (42, 63), (63, 87), (87, 112), (112, 133), (133, 150), (150, 175), (175, 196), (196, 220), (220, 225)]
noncomputable def e1_E40_0_4 : List Term := [⟨2, false, law 0 0, DA_X0W4_0_4⟩, ⟨2, true, law 4 0, DA_X0W4_0_0⟩, ⟨48, true, shiftX 4 (law 1 0), law 1 0⟩, ⟨24, false, shiftX 4 (law 0 0), law 3 0⟩]
theorem e1_E40_0_4_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 42)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_R1 : (evalO2 (nfTree5.mapRows (rowsIn 42 63)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_R2 : (evalO2 (nfTree5.mapRows (rowsIn 63 87)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_R3 : (evalO2 (nfTree5.mapRows (rowsIn 87 112)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_R4 : (evalO2 (nfTree5.mapRows (rowsIn 112 133)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_R5 : (evalO2 (nfTree5.mapRows (rowsIn 133 150)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_R6 : (evalO2 (nfTree5.mapRows (rowsIn 150 175)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_R7 : (evalO2 (nfTree5.mapRows (rowsIn 175 196)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_R8 : (evalO2 (nfTree5.mapRows (rowsIn 196 220)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_R9 : (evalO2 (nfTree5.mapRows (rowsIn 220 225)) nfTree4b e1_E40_0_4).allZero = true := by decide +kernel
theorem e1_E40_0_4_B : wsum e1_E40_0_4 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_0_4_T : e1_E40_0_4.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_0_5 : List (Nat × Nat) := [(0, 43), (43, 66), (66, 91), (91, 120), (120, 138), (138, 158), (158, 177), (177, 199), (199, 225)]
noncomputable def e1_E40_0_5 : List Term := [⟨2, false, law 0 0, DA_X0W4_0_5⟩, ⟨2, true, law 5 0, DA_X0W4_0_0⟩, ⟨8, false, shiftX 4 (law 0 0), law 0 0⟩, ⟨48, true, shiftX 4 (law 1 0), law 2 0⟩]
theorem e1_E40_0_5_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 43)) nfTree4b e1_E40_0_5).allZero = true := by decide +kernel
theorem e1_E40_0_5_R1 : (evalO2 (nfTree5.mapRows (rowsIn 43 66)) nfTree4b e1_E40_0_5).allZero = true := by decide +kernel
theorem e1_E40_0_5_R2 : (evalO2 (nfTree5.mapRows (rowsIn 66 91)) nfTree4b e1_E40_0_5).allZero = true := by decide +kernel
theorem e1_E40_0_5_R3 : (evalO2 (nfTree5.mapRows (rowsIn 91 120)) nfTree4b e1_E40_0_5).allZero = true := by decide +kernel
theorem e1_E40_0_5_R4 : (evalO2 (nfTree5.mapRows (rowsIn 120 138)) nfTree4b e1_E40_0_5).allZero = true := by decide +kernel
theorem e1_E40_0_5_R5 : (evalO2 (nfTree5.mapRows (rowsIn 138 158)) nfTree4b e1_E40_0_5).allZero = true := by decide +kernel
theorem e1_E40_0_5_R6 : (evalO2 (nfTree5.mapRows (rowsIn 158 177)) nfTree4b e1_E40_0_5).allZero = true := by decide +kernel
theorem e1_E40_0_5_R7 : (evalO2 (nfTree5.mapRows (rowsIn 177 199)) nfTree4b e1_E40_0_5).allZero = true := by decide +kernel
theorem e1_E40_0_5_R8 : (evalO2 (nfTree5.mapRows (rowsIn 199 225)) nfTree4b e1_E40_0_5).allZero = true := by decide +kernel
theorem e1_E40_0_5_B : wsum e1_E40_0_5 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_0_5_T : e1_E40_0_5.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_0_6 : List (Nat × Nat) := [(0, 39), (39, 57), (57, 83), (83, 111), (111, 126), (126, 141), (141, 161), (161, 177), (177, 196), (196, 219), (219, 225)]
noncomputable def e1_E40_0_6 : List Term := [⟨2, false, law 0 0, DA_X0W4_0_6⟩, ⟨2, true, law 6 0, DA_X0W4_0_0⟩, ⟨48, true, shiftX 4 (law 1 0), law 3 0⟩, ⟨32, true, shiftX 4 (law 0 0), law 8 0⟩]
theorem e1_E40_0_6_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 39)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R1 : (evalO2 (nfTree5.mapRows (rowsIn 39 57)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R2 : (evalO2 (nfTree5.mapRows (rowsIn 57 83)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R3 : (evalO2 (nfTree5.mapRows (rowsIn 83 111)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R4 : (evalO2 (nfTree5.mapRows (rowsIn 111 126)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R5 : (evalO2 (nfTree5.mapRows (rowsIn 126 141)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R6 : (evalO2 (nfTree5.mapRows (rowsIn 141 161)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R7 : (evalO2 (nfTree5.mapRows (rowsIn 161 177)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R8 : (evalO2 (nfTree5.mapRows (rowsIn 177 196)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R9 : (evalO2 (nfTree5.mapRows (rowsIn 196 219)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_R10 : (evalO2 (nfTree5.mapRows (rowsIn 219 225)) nfTree4b e1_E40_0_6).allZero = true := by decide +kernel
theorem e1_E40_0_6_B : wsum e1_E40_0_6 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_0_6_T : e1_E40_0_6.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_0_7 : List (Nat × Nat) := [(0, 40), (40, 62), (62, 86), (86, 112), (112, 131), (131, 142), (142, 162), (162, 177), (177, 197), (197, 219), (219, 225)]
noncomputable def e1_E40_0_7 : List Term := [⟨2, false, law 0 0, DA_X0W4_0_7⟩, ⟨2, true, law 7 0, DA_X0W4_0_0⟩, ⟨16, false, shiftX 4 (law 0 0), law 1 0⟩, ⟨48, true, shiftX 4 (law 2 0), law 3 0⟩]
theorem e1_E40_0_7_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 40)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R1 : (evalO2 (nfTree5.mapRows (rowsIn 40 62)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R2 : (evalO2 (nfTree5.mapRows (rowsIn 62 86)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R3 : (evalO2 (nfTree5.mapRows (rowsIn 86 112)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R4 : (evalO2 (nfTree5.mapRows (rowsIn 112 131)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R5 : (evalO2 (nfTree5.mapRows (rowsIn 131 142)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R6 : (evalO2 (nfTree5.mapRows (rowsIn 142 162)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R7 : (evalO2 (nfTree5.mapRows (rowsIn 162 177)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R8 : (evalO2 (nfTree5.mapRows (rowsIn 177 197)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R9 : (evalO2 (nfTree5.mapRows (rowsIn 197 219)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_R10 : (evalO2 (nfTree5.mapRows (rowsIn 219 225)) nfTree4b e1_E40_0_7).allZero = true := by decide +kernel
theorem e1_E40_0_7_B : wsum e1_E40_0_7 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_0_7_T : e1_E40_0_7.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E40_0_8 : List (Nat × Nat) := [(0, 40), (40, 62), (62, 86), (86, 112), (112, 131), (131, 142), (142, 161), (161, 177), (177, 196), (196, 219), (219, 225)]
noncomputable def e1_E40_0_8 : List Term := [⟨2, false, law 0 0, DA_X0W4_0_8⟩, ⟨2, true, law 8 0, DA_X0W4_0_0⟩, ⟨24, true, shiftX 4 (law 2 0), law 5 0⟩, ⟨24, false, shiftX 4 (law 1 0), law 6 0⟩]
theorem e1_E40_0_8_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 40)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R1 : (evalO2 (nfTree5.mapRows (rowsIn 40 62)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R2 : (evalO2 (nfTree5.mapRows (rowsIn 62 86)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R3 : (evalO2 (nfTree5.mapRows (rowsIn 86 112)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R4 : (evalO2 (nfTree5.mapRows (rowsIn 112 131)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R5 : (evalO2 (nfTree5.mapRows (rowsIn 131 142)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R6 : (evalO2 (nfTree5.mapRows (rowsIn 142 161)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R7 : (evalO2 (nfTree5.mapRows (rowsIn 161 177)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R8 : (evalO2 (nfTree5.mapRows (rowsIn 177 196)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R9 : (evalO2 (nfTree5.mapRows (rowsIn 196 219)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_R10 : (evalO2 (nfTree5.mapRows (rowsIn 219 225)) nfTree4b e1_E40_0_8).allZero = true := by decide +kernel
theorem e1_E40_0_8_B : wsum e1_E40_0_8 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E40_0_8_T : e1_E40_0_8.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
