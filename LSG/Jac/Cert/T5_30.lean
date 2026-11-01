import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_30
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 1074 … 1127. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_30 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 1074 nfc5_30 = true := by decide +kernel

theorem nfc5_len_30 : nfc5_30.length = 54 := rfl

end LSG.Jac.Cert
