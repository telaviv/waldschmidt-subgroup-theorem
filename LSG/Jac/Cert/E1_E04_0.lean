import LSG.Jac.Data.Laws
import LSG.Jac.Data.Table
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table5
import LSG.Jac.Data.E1
import LSG.Jac.CheckerRange

/-! GENERATED — equivariance identities `E04` (law 0, `X`-flow, output chart 4), j = 0, split by
`X`-slot ranges `rs_e1_E04_0_<l>` (adaptive, `scripts/jac/e1_cost.py`, budget 50000). -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

def rs_e1_E04_0_0 : List (Nat × Nat) := [(0, 57), (57, 109), (109, 149), (149, 190), (190, 225)]
noncomputable def e1_E04_0_0 : List Term := [⟨4, false, law 4 0, DA_X0W_0_0⟩, ⟨4, true, law 0 0, DA_X0W_0_4⟩, ⟨48, false, shiftX 0 (law 1 0), law 1 0⟩, ⟨24, true, shiftX 0 (law 0 0), law 3 0⟩]
theorem e1_E04_0_0_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 57)) nfTree4b e1_E04_0_0).allZero = true := by decide +kernel
theorem e1_E04_0_0_R1 : (evalO2 (nfTree5.mapRows (rowsIn 57 109)) nfTree4b e1_E04_0_0).allZero = true := by decide +kernel
theorem e1_E04_0_0_R2 : (evalO2 (nfTree5.mapRows (rowsIn 109 149)) nfTree4b e1_E04_0_0).allZero = true := by decide +kernel
theorem e1_E04_0_0_R3 : (evalO2 (nfTree5.mapRows (rowsIn 149 190)) nfTree4b e1_E04_0_0).allZero = true := by decide +kernel
theorem e1_E04_0_0_R4 : (evalO2 (nfTree5.mapRows (rowsIn 190 225)) nfTree4b e1_E04_0_0).allZero = true := by decide +kernel
theorem e1_E04_0_0_B : wsum e1_E04_0_0 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_0_0_T : e1_E04_0_0.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_0_1 : List (Nat × Nat) := [(0, 24), (24, 37), (37, 47), (47, 60), (60, 72), (72, 85), (85, 100), (100, 121), (121, 132), (132, 141), (141, 159), (159, 175), (175, 186), (186, 199), (199, 215), (215, 225)]
noncomputable def e1_E04_0_1 : List Term := [⟨4, false, law 4 0, DA_X0W_0_1⟩, ⟨4, true, law 1 0, DA_X0W_0_4⟩, ⟨12, false, shiftX 0 (law 1 0), law 3 0⟩, ⟨4, false, shiftX 0 (law 4 0), law 4 0⟩, ⟨12, true, shiftX 0 (law 0 0), law 8 0⟩]
theorem e1_E04_0_1_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 37)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R2 : (evalO2 (nfTree5.mapRows (rowsIn 37 47)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R3 : (evalO2 (nfTree5.mapRows (rowsIn 47 60)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R4 : (evalO2 (nfTree5.mapRows (rowsIn 60 72)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R5 : (evalO2 (nfTree5.mapRows (rowsIn 72 85)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R6 : (evalO2 (nfTree5.mapRows (rowsIn 85 100)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R7 : (evalO2 (nfTree5.mapRows (rowsIn 100 121)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R8 : (evalO2 (nfTree5.mapRows (rowsIn 121 132)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R9 : (evalO2 (nfTree5.mapRows (rowsIn 132 141)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R10 : (evalO2 (nfTree5.mapRows (rowsIn 141 159)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R11 : (evalO2 (nfTree5.mapRows (rowsIn 159 175)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R12 : (evalO2 (nfTree5.mapRows (rowsIn 175 186)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R13 : (evalO2 (nfTree5.mapRows (rowsIn 186 199)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R14 : (evalO2 (nfTree5.mapRows (rowsIn 199 215)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_R15 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_E04_0_1).allZero = true := by decide +kernel
theorem e1_E04_0_1_B : wsum e1_E04_0_1 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_0_1_T : e1_E04_0_1.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_0_2 : List (Nat × Nat) := [(0, 24), (24, 36), (36, 47), (47, 58), (58, 72), (72, 85), (85, 100), (100, 121), (121, 132), (132, 141), (141, 159), (159, 175), (175, 186), (186, 199), (199, 215), (215, 225)]
noncomputable def e1_E04_0_2 : List Term := [⟨4, false, law 4 0, DA_X0W_0_2⟩, ⟨4, true, law 2 0, DA_X0W_0_4⟩, ⟨24, false, shiftX 0 (law 0 0), law 1 0⟩, ⟨12, true, shiftX 0 (law 2 0), law 3 0⟩, ⟨4, false, shiftX 0 (law 4 0), law 5 0⟩]
theorem e1_E04_0_2_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 36)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R2 : (evalO2 (nfTree5.mapRows (rowsIn 36 47)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R3 : (evalO2 (nfTree5.mapRows (rowsIn 47 58)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R4 : (evalO2 (nfTree5.mapRows (rowsIn 58 72)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R5 : (evalO2 (nfTree5.mapRows (rowsIn 72 85)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R6 : (evalO2 (nfTree5.mapRows (rowsIn 85 100)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R7 : (evalO2 (nfTree5.mapRows (rowsIn 100 121)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R8 : (evalO2 (nfTree5.mapRows (rowsIn 121 132)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R9 : (evalO2 (nfTree5.mapRows (rowsIn 132 141)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R10 : (evalO2 (nfTree5.mapRows (rowsIn 141 159)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R11 : (evalO2 (nfTree5.mapRows (rowsIn 159 175)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R12 : (evalO2 (nfTree5.mapRows (rowsIn 175 186)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R13 : (evalO2 (nfTree5.mapRows (rowsIn 186 199)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R14 : (evalO2 (nfTree5.mapRows (rowsIn 199 215)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_R15 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_E04_0_2).allZero = true := by decide +kernel
theorem e1_E04_0_2_B : wsum e1_E04_0_2 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_0_2_T : e1_E04_0_2.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_0_3 : List (Nat × Nat) := [(0, 24), (24, 34), (34, 47), (47, 57), (57, 71), (71, 83), (83, 99), (99, 120), (120, 131), (131, 140), (140, 151), (151, 165), (165, 176), (176, 191), (191, 200), (200, 215), (215, 225)]
noncomputable def e1_E04_0_3 : List Term := [⟨4, false, law 4 0, DA_X0W_0_3⟩, ⟨4, true, law 3 0, DA_X0W_0_4⟩, ⟨12, false, shiftX 0 (law 0 0), law 2 0⟩, ⟨4, false, shiftX 0 (law 4 0), law 6 0⟩, ⟨24, true, shiftX 0 (law 1 0), law 8 0⟩]
theorem e1_E04_0_3_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 24)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R1 : (evalO2 (nfTree5.mapRows (rowsIn 24 34)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R2 : (evalO2 (nfTree5.mapRows (rowsIn 34 47)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R3 : (evalO2 (nfTree5.mapRows (rowsIn 47 57)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 71)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R5 : (evalO2 (nfTree5.mapRows (rowsIn 71 83)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R6 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R7 : (evalO2 (nfTree5.mapRows (rowsIn 99 120)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R8 : (evalO2 (nfTree5.mapRows (rowsIn 120 131)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R9 : (evalO2 (nfTree5.mapRows (rowsIn 131 140)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R10 : (evalO2 (nfTree5.mapRows (rowsIn 140 151)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R11 : (evalO2 (nfTree5.mapRows (rowsIn 151 165)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R12 : (evalO2 (nfTree5.mapRows (rowsIn 165 176)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R13 : (evalO2 (nfTree5.mapRows (rowsIn 176 191)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R14 : (evalO2 (nfTree5.mapRows (rowsIn 191 200)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R15 : (evalO2 (nfTree5.mapRows (rowsIn 200 215)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_R16 : (evalO2 (nfTree5.mapRows (rowsIn 215 225)) nfTree4b e1_E04_0_3).allZero = true := by decide +kernel
theorem e1_E04_0_3_B : wsum e1_E04_0_3 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_0_3_T : e1_E04_0_3.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_0_5 : List (Nat × Nat) := [(0, 23), (23, 33), (33, 45), (45, 57), (57, 71), (71, 83), (83, 99), (99, 120), (120, 128), (128, 139), (139, 150), (150, 164), (164, 176), (176, 188), (188, 199), (199, 214), (214, 225)]
noncomputable def e1_E04_0_5 : List Term := [⟨4, false, law 4 0, DA_X0W_0_5⟩, ⟨4, true, law 5 0, DA_X0W_0_4⟩, ⟨4, true, shiftX 0 (law 0 0), law 4 0⟩, ⟨12, true, shiftX 0 (law 2 0), law 6 0⟩, ⟨12, false, shiftX 0 (law 1 0), law 7 0⟩]
theorem e1_E04_0_5_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 33)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R2 : (evalO2 (nfTree5.mapRows (rowsIn 33 45)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R3 : (evalO2 (nfTree5.mapRows (rowsIn 45 57)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 71)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R5 : (evalO2 (nfTree5.mapRows (rowsIn 71 83)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R6 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R7 : (evalO2 (nfTree5.mapRows (rowsIn 99 120)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R8 : (evalO2 (nfTree5.mapRows (rowsIn 120 128)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R9 : (evalO2 (nfTree5.mapRows (rowsIn 128 139)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R10 : (evalO2 (nfTree5.mapRows (rowsIn 139 150)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R11 : (evalO2 (nfTree5.mapRows (rowsIn 150 164)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R12 : (evalO2 (nfTree5.mapRows (rowsIn 164 176)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R13 : (evalO2 (nfTree5.mapRows (rowsIn 176 188)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R14 : (evalO2 (nfTree5.mapRows (rowsIn 188 199)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R15 : (evalO2 (nfTree5.mapRows (rowsIn 199 214)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_R16 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_E04_0_5).allZero = true := by decide +kernel
theorem e1_E04_0_5_B : wsum e1_E04_0_5 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_0_5_T : e1_E04_0_5.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_0_6 : List (Nat × Nat) := [(0, 23), (23, 33), (33, 43), (43, 57), (57, 69), (69, 82), (82, 97), (97, 112), (112, 123), (123, 135), (135, 142), (142, 151), (151, 164), (164, 176), (176, 186), (186, 198), (198, 214), (214, 225)]
noncomputable def e1_E04_0_6 : List Term := [⟨4, false, law 4 0, DA_X0W_0_6⟩, ⟨4, true, law 6 0, DA_X0W_0_4⟩, ⟨24, false, shiftX 0 (law 0 0), law 5 0⟩, ⟨12, true, shiftX 0 (law 2 0), law 7 0⟩, ⟨8, true, shiftX 0 (law 4 0), law 8 0⟩]
theorem e1_E04_0_6_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 33)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R2 : (evalO2 (nfTree5.mapRows (rowsIn 33 43)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R3 : (evalO2 (nfTree5.mapRows (rowsIn 43 57)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 69)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R5 : (evalO2 (nfTree5.mapRows (rowsIn 69 82)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R6 : (evalO2 (nfTree5.mapRows (rowsIn 82 97)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R7 : (evalO2 (nfTree5.mapRows (rowsIn 97 112)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R8 : (evalO2 (nfTree5.mapRows (rowsIn 112 123)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R9 : (evalO2 (nfTree5.mapRows (rowsIn 123 135)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R10 : (evalO2 (nfTree5.mapRows (rowsIn 135 142)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R11 : (evalO2 (nfTree5.mapRows (rowsIn 142 151)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R12 : (evalO2 (nfTree5.mapRows (rowsIn 151 164)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R13 : (evalO2 (nfTree5.mapRows (rowsIn 164 176)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R14 : (evalO2 (nfTree5.mapRows (rowsIn 176 186)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R15 : (evalO2 (nfTree5.mapRows (rowsIn 186 198)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R16 : (evalO2 (nfTree5.mapRows (rowsIn 198 214)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_R17 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_E04_0_6).allZero = true := by decide +kernel
theorem e1_E04_0_6_B : wsum e1_E04_0_6 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_0_6_T : e1_E04_0_6.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_0_7 : List (Nat × Nat) := [(0, 22), (22, 31), (31, 41), (41, 49), (49, 57), (57, 67), (67, 77), (77, 90), (90, 99), (99, 116), (116, 123), (123, 132), (132, 140), (140, 150), (150, 164), (164, 175), (175, 185), (185, 196), (196, 212), (212, 225)]
noncomputable def e1_E04_0_7 : List Term := [⟨4, false, law 4 0, DA_X0W_0_7⟩, ⟨4, true, law 7 0, DA_X0W_0_4⟩, ⟨32, true, shiftX 0 (law 1 0), law 4 0⟩, ⟨12, false, shiftX 0 (law 3 0), law 7 0⟩, ⟨24, true, shiftX 0 (law 5 0), law 8 0⟩]
theorem e1_E04_0_7_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 22)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R1 : (evalO2 (nfTree5.mapRows (rowsIn 22 31)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R2 : (evalO2 (nfTree5.mapRows (rowsIn 31 41)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R3 : (evalO2 (nfTree5.mapRows (rowsIn 41 49)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R4 : (evalO2 (nfTree5.mapRows (rowsIn 49 57)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R5 : (evalO2 (nfTree5.mapRows (rowsIn 57 67)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R6 : (evalO2 (nfTree5.mapRows (rowsIn 67 77)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R7 : (evalO2 (nfTree5.mapRows (rowsIn 77 90)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R8 : (evalO2 (nfTree5.mapRows (rowsIn 90 99)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R9 : (evalO2 (nfTree5.mapRows (rowsIn 99 116)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R10 : (evalO2 (nfTree5.mapRows (rowsIn 116 123)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R11 : (evalO2 (nfTree5.mapRows (rowsIn 123 132)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R12 : (evalO2 (nfTree5.mapRows (rowsIn 132 140)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R13 : (evalO2 (nfTree5.mapRows (rowsIn 140 150)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R14 : (evalO2 (nfTree5.mapRows (rowsIn 150 164)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R15 : (evalO2 (nfTree5.mapRows (rowsIn 164 175)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R16 : (evalO2 (nfTree5.mapRows (rowsIn 175 185)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R17 : (evalO2 (nfTree5.mapRows (rowsIn 185 196)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R18 : (evalO2 (nfTree5.mapRows (rowsIn 196 212)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_R19 : (evalO2 (nfTree5.mapRows (rowsIn 212 225)) nfTree4b e1_E04_0_7).allZero = true := by decide +kernel
theorem e1_E04_0_7_B : wsum e1_E04_0_7 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_0_7_T : e1_E04_0_7.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

def rs_e1_E04_0_8 : List (Nat × Nat) := [(0, 23), (23, 33), (33, 45), (45, 57), (57, 70), (70, 83), (83, 99), (99, 120), (120, 127), (127, 139), (139, 150), (150, 164), (164, 176), (176, 188), (188, 199), (199, 214), (214, 225)]
noncomputable def e1_E04_0_8 : List Term := [⟨4, false, law 4 0, DA_X0W_0_8⟩, ⟨4, true, law 8 0, DA_X0W_0_4⟩, ⟨48, false, shiftX 0 (law 1 0), law 2 0⟩, ⟨6, true, shiftX 0 (law 5 0), law 7 0⟩, ⟨12, false, shiftX 0 (law 3 0), law 8 0⟩]
theorem e1_E04_0_8_R0 : (evalO2 (nfTree5.mapRows (rowsIn 0 23)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R1 : (evalO2 (nfTree5.mapRows (rowsIn 23 33)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R2 : (evalO2 (nfTree5.mapRows (rowsIn 33 45)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R3 : (evalO2 (nfTree5.mapRows (rowsIn 45 57)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R4 : (evalO2 (nfTree5.mapRows (rowsIn 57 70)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R5 : (evalO2 (nfTree5.mapRows (rowsIn 70 83)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R6 : (evalO2 (nfTree5.mapRows (rowsIn 83 99)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R7 : (evalO2 (nfTree5.mapRows (rowsIn 99 120)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R8 : (evalO2 (nfTree5.mapRows (rowsIn 120 127)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R9 : (evalO2 (nfTree5.mapRows (rowsIn 127 139)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R10 : (evalO2 (nfTree5.mapRows (rowsIn 139 150)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R11 : (evalO2 (nfTree5.mapRows (rowsIn 150 164)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R12 : (evalO2 (nfTree5.mapRows (rowsIn 164 176)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R13 : (evalO2 (nfTree5.mapRows (rowsIn 176 188)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R14 : (evalO2 (nfTree5.mapRows (rowsIn 188 199)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R15 : (evalO2 (nfTree5.mapRows (rowsIn 199 214)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_R16 : (evalO2 (nfTree5.mapRows (rowsIn 214 225)) nfTree4b e1_E04_0_8).allZero = true := by decide +kernel
theorem e1_E04_0_8_B : wsum e1_E04_0_8 * (rowM5 * rowM) < 2 ^ kb4b := by decide +kernel
theorem e1_E04_0_8_T : e1_E04_0_8.all (fun q => termOK2 nfTree5 nfTree4b q && q.a.wf && q.b.wf) = true := by decide +kernel

end LSG.Jac.Cert
