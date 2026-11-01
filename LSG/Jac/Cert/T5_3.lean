import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_3
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 93 … 126. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_3 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 93 nfc5_3 = true := by decide +kernel

theorem nfc5_len_3 : nfc5_3.length = 34 := rfl

end LSG.Jac.Cert
