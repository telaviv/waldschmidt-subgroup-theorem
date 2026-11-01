import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_21
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 713 … 757. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_21 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 713 nfc5_21 = true := by decide +kernel

theorem nfc5_len_21 : nfc5_21.length = 45 := rfl

end LSG.Jac.Cert
