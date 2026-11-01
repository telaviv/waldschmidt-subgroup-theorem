import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_19
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 637 … 679. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_19 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 637 nfc5_19 = true := by decide +kernel

theorem nfc5_len_19 : nfc5_19.length = 43 := rfl

end LSG.Jac.Cert
