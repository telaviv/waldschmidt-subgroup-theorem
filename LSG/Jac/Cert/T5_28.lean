import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_28
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 989 … 1029. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_28 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 989 nfc5_28 = true := by decide +kernel

theorem nfc5_len_28 : nfc5_28.length = 41 := rfl

end LSG.Jac.Cert
