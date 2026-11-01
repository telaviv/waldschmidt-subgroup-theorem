import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_34
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 1259 … 1286. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_34 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 1259 nfc5_34 = true := by decide +kernel

theorem nfc5_len_34 : nfc5_34.length = 28 := rfl

end LSG.Jac.Cert
