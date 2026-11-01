import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_17
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 566 … 601. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_17 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 566 nfc5_17 = true := by decide +kernel

theorem nfc5_len_17 : nfc5_17.length = 36 := rfl

end LSG.Jac.Cert
