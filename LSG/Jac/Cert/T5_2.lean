import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_2
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 62 … 92. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_2 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 62 nfc5_2 = true := by decide +kernel

theorem nfc5_len_2 : nfc5_2.length = 31 := rfl

end LSG.Jac.Cert
