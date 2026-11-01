import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table4b
import LSG.Jac.Data.Table
import LSG.Jac.Data.IdTab
import LSG.Jac.CheckerNF2
import LSG.Jac.CheckerRange

/-! GENERATED — structural checks of the E1 tables. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem leaves_ok5 : nfTree5.leaves.all (leafOK 225 kb5 rowM5) = true := by decide +kernel
theorem keys_ok5 : keysOK nfTree5 keys5 = true := by decide +kernel
theorem leaves_len5 : nfTree5.leaves.length = 1287 := by decide +kernel
theorem leaves_ok4b : nfTree4b.leaves.all (leafOK 144 kb4b rowM) = true := by decide +kernel
theorem same4b : sameRows nfTree nfTree4b = true := by decide +kernel
theorem id2_ok : idOK idTree2 stdcId2 = true := by decide +kernel
theorem id3_ok : idOK idTree3 stdcId3 = true := by decide +kernel
theorem id2_leaves : idTree2.leaves.all (leafOK 45 kbId 1) = true := by decide +kernel
theorem id3_leaves : idTree3.leaves.all (leafOK 165 kbId 1) = true := by decide +kernel

end LSG.Jac.Cert
