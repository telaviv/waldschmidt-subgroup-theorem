import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_11
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 352 … 390. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_11 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 352 nfc5_11 = true := by decide +kernel

theorem nfc5_len_11 : nfc5_11.length = 39 := rfl

end LSG.Jac.Cert
