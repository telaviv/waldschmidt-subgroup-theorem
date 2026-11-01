import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_24
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 837 … 871. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_24 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 837 nfc5_24 = true := by decide +kernel

theorem nfc5_len_24 : nfc5_24.length = 35 := rfl

end LSG.Jac.Cert
