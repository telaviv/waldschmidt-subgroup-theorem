import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_12
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 391 … 423. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_12 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 391 nfc5_12 = true := by decide +kernel

theorem nfc5_len_12 : nfc5_12.length = 33 := rfl

end LSG.Jac.Cert
