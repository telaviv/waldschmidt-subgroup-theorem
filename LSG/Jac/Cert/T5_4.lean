import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_4
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 127 … 155. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_4 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 127 nfc5_4 = true := by decide +kernel

theorem nfc5_len_4 : nfc5_4.length = 29 := rfl

end LSG.Jac.Cert
