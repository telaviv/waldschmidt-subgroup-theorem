import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_15
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 501 … 534. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_15 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 501 nfc5_15 = true := by decide +kernel

theorem nfc5_len_15 : nfc5_15.length = 34 := rfl

end LSG.Jac.Cert
