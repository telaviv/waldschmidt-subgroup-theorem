import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_14
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 471 … 500. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_14 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 471 nfc5_14 = true := by decide +kernel

theorem nfc5_len_14 : nfc5_14.length = 30 := rfl

end LSG.Jac.Cert
