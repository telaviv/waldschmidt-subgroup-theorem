set_option maxRecDepth 1000000
def big : Nat := (1 <<< 7000) + 12345
def l : List Nat := List.range 20000
-- Nat: sum of k * big
def sN : Nat := l.foldl (fun a k => a + k * big) 0
theorem microN : sN = 199990000 * big := by decide +kernel
-- Int: same with alternating signs
def bigI : Int := Int.ofNat big
def sI : Int := l.foldl (fun a k => a + (if k % 2 = 0 then (k : Int) else -(k : Int)) * bigI) 0
theorem microI : sI = -10000 * bigI := by decide +kernel
