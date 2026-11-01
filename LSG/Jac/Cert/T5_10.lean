import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_10
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 320 … 351. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_10 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 320 nfc5_10 = true := by decide +kernel

theorem nfc5_len_10 : nfc5_10.length = 32 := rfl

end LSG.Jac.Cert
