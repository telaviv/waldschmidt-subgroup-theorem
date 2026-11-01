import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_9
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 289 … 319. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_9 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 289 nfc5_9 = true := by decide +kernel

theorem nfc5_len_9 : nfc5_9.length = 31 := rfl

end LSG.Jac.Cert
