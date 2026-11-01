import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_8
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 259 … 288. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_8 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 259 nfc5_8 = true := by decide +kernel

theorem nfc5_len_8 : nfc5_8.length = 30 := rfl

end LSG.Jac.Cert
