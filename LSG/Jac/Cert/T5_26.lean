import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_26
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 909 … 944. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_26 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 909 nfc5_26 = true := by decide +kernel

theorem nfc5_len_26 : nfc5_26.length = 36 := rfl

end LSG.Jac.Cert
