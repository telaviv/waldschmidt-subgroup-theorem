import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_1
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 30 … 61. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_1 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 30 nfc5_1 = true := by decide +kernel

theorem nfc5_len_1 : nfc5_1.length = 32 := rfl

end LSG.Jac.Cert
