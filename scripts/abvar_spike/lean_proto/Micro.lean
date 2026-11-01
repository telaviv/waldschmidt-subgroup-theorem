set_option maxRecDepth 1000000
def l : List Nat := List.range 20000
theorem micro1 : l.foldl (· + ·) 0 = 199990000 := by decide +kernel
def li : List Int := (List.range 20000).map (fun n => (n : Int) - 7)
theorem micro2 : li.foldl (fun a x => a + x * 3) 0 = 599550000 - 420000 := by decide +kernel
def cmp (c : Nat) : Nat := if c < 5000 then (if c < 2500 then 1 else 2) else (if c < 7500 then 3 else 4)
theorem micro3 : (l.map cmp).foldl (· + ·) 0 = 2*2500+3*2500+4*12500 + 2500 := by decide +kernel
