import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_13
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 424 … 470. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_13 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 424 nfc5_13 = true := by decide +kernel

theorem nfc5_len_13 : nfc5_13.length = 47 := rfl

end LSG.Jac.Cert
