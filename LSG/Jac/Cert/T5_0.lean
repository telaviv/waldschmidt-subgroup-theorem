import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_0
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 0 … 29. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_0 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 0 nfc5_0 = true := by decide +kernel

theorem nfc5_len_0 : nfc5_0.length = 30 := rfl

end LSG.Jac.Cert
