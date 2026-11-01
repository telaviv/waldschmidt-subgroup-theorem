import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_25
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 872 … 908. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_25 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 872 nfc5_25 = true := by decide +kernel

theorem nfc5_len_25 : nfc5_25.length = 37 := rfl

end LSG.Jac.Cert
