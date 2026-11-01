import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_18
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 602 … 636. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_18 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 602 nfc5_18 = true := by decide +kernel

theorem nfc5_len_18 : nfc5_18.length = 35 := rfl

end LSG.Jac.Cert
