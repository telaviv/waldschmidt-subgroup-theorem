import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_16
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 535 … 565. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_16 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 535 nfc5_16 = true := by decide +kernel

theorem nfc5_len_16 : nfc5_16.length = 31 := rfl

end LSG.Jac.Cert
