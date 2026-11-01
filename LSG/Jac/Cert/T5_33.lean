import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_33
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 1211 … 1258. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_33 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 1211 nfc5_33 = true := by decide +kernel

theorem nfc5_len_33 : nfc5_33.length = 48 := rfl

end LSG.Jac.Cert
