import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_31
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 1128 … 1163. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_31 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 1128 nfc5_31 = true := by decide +kernel

theorem nfc5_len_31 : nfc5_31.length = 36 := rfl

end LSG.Jac.Cert
