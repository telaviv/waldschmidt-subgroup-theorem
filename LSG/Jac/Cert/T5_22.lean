import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_22
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 758 … 802. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_22 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 758 nfc5_22 = true := by decide +kernel

theorem nfc5_len_22 : nfc5_22.length = 45 := rfl

end LSG.Jac.Cert
