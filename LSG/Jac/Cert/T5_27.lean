import LSG.Jac.Data.Table5
import LSG.Jac.Data.Table
import LSG.Jac.Data.NFCert5_27
import LSG.Jac.CheckerNF2

/-! GENERATED — degree-5 table check, leaves 945 … 988. -/

namespace LSG.Jac.Cert

open LSG.Jac LSG.Jac.Data

set_option maxRecDepth 100000

theorem nf5_ok_27 : nfRangeOK nfTree5 39 1287 nfDelta5 stdc5 Qd 945 nfc5_27 = true := by decide +kernel

theorem nfc5_len_27 : nfc5_27.length = 44 := rfl

end LSG.Jac.Cert
