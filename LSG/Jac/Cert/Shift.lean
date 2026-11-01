import LSG.Jac.Data.Laws
import LSG.Jac.CheckerRange

/-! No-carry checks for the shifted factors `X_f · A`, `Y_f · A` of the E1 identities. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

theorem shX_0_0_0 : shiftXOK 0 (law 0 0) = true := by decide +kernel
theorem shX_0_1_0 : shiftXOK 0 (law 1 0) = true := by decide +kernel
theorem shX_0_2_0 : shiftXOK 0 (law 2 0) = true := by decide +kernel
theorem shX_0_3_0 : shiftXOK 0 (law 3 0) = true := by decide +kernel
theorem shX_0_4_0 : shiftXOK 0 (law 4 0) = true := by decide +kernel
theorem shX_0_5_0 : shiftXOK 0 (law 5 0) = true := by decide +kernel
theorem shX_0_6_0 : shiftXOK 0 (law 6 0) = true := by decide +kernel
theorem shX_0_7_0 : shiftXOK 0 (law 7 0) = true := by decide +kernel
theorem shX_0_8_0 : shiftXOK 0 (law 8 0) = true := by decide +kernel
theorem shX_0_0_4 : shiftXOK 0 (law 0 4) = true := by decide +kernel
theorem shX_0_1_4 : shiftXOK 0 (law 1 4) = true := by decide +kernel
theorem shX_0_2_4 : shiftXOK 0 (law 2 4) = true := by decide +kernel
theorem shX_0_3_4 : shiftXOK 0 (law 3 4) = true := by decide +kernel
theorem shX_0_4_4 : shiftXOK 0 (law 4 4) = true := by decide +kernel
theorem shX_0_5_4 : shiftXOK 0 (law 5 4) = true := by decide +kernel
theorem shX_0_6_4 : shiftXOK 0 (law 6 4) = true := by decide +kernel
theorem shX_0_7_4 : shiftXOK 0 (law 7 4) = true := by decide +kernel
theorem shX_0_8_4 : shiftXOK 0 (law 8 4) = true := by decide +kernel
theorem shX_4_0_0 : shiftXOK 4 (law 0 0) = true := by decide +kernel
theorem shX_4_1_0 : shiftXOK 4 (law 1 0) = true := by decide +kernel
theorem shX_4_2_0 : shiftXOK 4 (law 2 0) = true := by decide +kernel
theorem shX_4_3_0 : shiftXOK 4 (law 3 0) = true := by decide +kernel
theorem shX_4_4_0 : shiftXOK 4 (law 4 0) = true := by decide +kernel
theorem shX_4_5_0 : shiftXOK 4 (law 5 0) = true := by decide +kernel
theorem shX_4_6_0 : shiftXOK 4 (law 6 0) = true := by decide +kernel
theorem shX_4_7_0 : shiftXOK 4 (law 7 0) = true := by decide +kernel
theorem shX_4_8_0 : shiftXOK 4 (law 8 0) = true := by decide +kernel
theorem shX_4_0_4 : shiftXOK 4 (law 0 4) = true := by decide +kernel
theorem shX_4_1_4 : shiftXOK 4 (law 1 4) = true := by decide +kernel
theorem shX_4_2_4 : shiftXOK 4 (law 2 4) = true := by decide +kernel
theorem shX_4_3_4 : shiftXOK 4 (law 3 4) = true := by decide +kernel
theorem shX_4_4_4 : shiftXOK 4 (law 4 4) = true := by decide +kernel
theorem shX_4_5_4 : shiftXOK 4 (law 5 4) = true := by decide +kernel
theorem shX_4_6_4 : shiftXOK 4 (law 6 4) = true := by decide +kernel
theorem shX_4_7_4 : shiftXOK 4 (law 7 4) = true := by decide +kernel
theorem shX_4_8_4 : shiftXOK 4 (law 8 4) = true := by decide +kernel
theorem shY_4_0_4 : shiftYOK 4 (law 0 4) = true := by decide +kernel
theorem shY_4_1_4 : shiftYOK 4 (law 1 4) = true := by decide +kernel
theorem shY_4_2_4 : shiftYOK 4 (law 2 4) = true := by decide +kernel
theorem shY_4_3_4 : shiftYOK 4 (law 3 4) = true := by decide +kernel
theorem shY_4_4_4 : shiftYOK 4 (law 4 4) = true := by decide +kernel
theorem shY_4_5_4 : shiftYOK 4 (law 5 4) = true := by decide +kernel
theorem shY_4_6_4 : shiftYOK 4 (law 6 4) = true := by decide +kernel
theorem shY_4_7_4 : shiftYOK 4 (law 7 4) = true := by decide +kernel
theorem shY_4_8_4 : shiftYOK 4 (law 8 4) = true := by decide +kernel

end LSG.Jac.Cert
