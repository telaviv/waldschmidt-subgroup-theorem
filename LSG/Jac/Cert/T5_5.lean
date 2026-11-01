import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_5
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 156 … 187. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_5 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 156 nfc5_5 = true := by decide +kernel

theorem nfc5_len_5 : nfc5_5.length = 32 := rfl

end LSG.Jac.Cert
