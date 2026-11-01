import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_7
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 221 … 258. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_7 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 221 nfc5_7 = true := by decide +kernel

theorem nfc5_len_7 : nfc5_7.length = 38 := rfl

end LSG.Jac.Cert
