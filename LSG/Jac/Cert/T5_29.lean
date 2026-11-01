import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_29
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 1030 … 1073. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_29 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 1030 nfc5_29 = true := by decide +kernel

theorem nfc5_len_29 : nfc5_29.length = 44 := rfl

end LSG.Jac.Cert
